#!/usr/bin/env python3
"""Build commit-level accounting and missing-data artifacts for the paper.

This script intentionally keeps three concepts separate:

1. exact commit-attributed measurements from the LLM ledger;
2. measured but commit-unattributed ``pending@...`` transcript segments; and
3. genuinely unmeasured work, for which extrapolation is exploratory.

The generated CSVs are designed to be auditable inputs to the manuscript rather
than opaque summary numbers.
"""

from __future__ import annotations

import csv
import json
import math
import pathlib
import random
import statistics
from collections import Counter, defaultdict

from accounting_lib import (
    RidgeLogModel,
    component_flags,
    feature_vector,
    format_int,
    instrumentation_commit,
    latex_escape,
    load_commits,
    load_ledger,
    load_overrides,
    matching_pending_windows,
    model_feature_names,
    parse_dt,
    pending_windows,
    quantile,
    repo_root,
    rolling_origin_splits,
    run_git,
    subject_flags,
    write_csv,
)

HERE = pathlib.Path(__file__).resolve().parent.parent
GENERATED = HERE / "generated"
DATA = HERE / "data"
CONFIG = json.loads((HERE / "analysis_config.json").read_text())
ROOT = repo_root(HERE)
CUTOFF = CONFIG["history_cutoff_commit"]


def infer_assistance(commit, override: dict | None) -> tuple[str, str, str]:
    """Return assistance_class, channel, evidence.

    Overrides are the only way to assert chat-interface work. Automatic labels
    are deliberately conservative and are evidence labels, not ground truth.
    """
    if override:
        cls = override.get("assistance_class") or "unknown"
        channel = override.get("channel") or "unknown"
        return cls, channel, "manual_override"

    names = commit.llm_coauthors
    author_agent = commit.author_name.strip().lower() in {"agent", "claude", "codex"}
    if names:
        return "llm", "unknown", "llm_coauthor_trailer"
    if author_agent:
        return "llm", "agent_harness", "agent_author"
    return "unknown", "unknown", "none"


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    commits = load_commits(ROOT, CUTOFF)
    commit_by_sha = {c.commit: c for c in commits}
    exact, pending, token_rows = load_ledger(ROOT)
    inst_sha, inst_dt = instrumentation_commit(ROOT, CUTOFF)
    windows = pending_windows(pending, float(CONFIG.get("pending_window_minutes", 0)))
    overrides = load_overrides(DATA / "accounting_overrides.csv")
    patterns = CONFIG["component_patterns"]
    component_names = list(patterns)

    rows: list[dict] = []
    for idx, commit in enumerate(commits, 1):
        measure = exact.get(commit.commit)
        pending_matches = matching_pending_windows(commit.timestamp_dt, windows)
        flags = component_flags(commit.files, patterns)
        sflags = subject_flags(commit.subject)
        override = overrides.get(commit.commit)
        assistance_class, channel, evidence = infer_assistance(commit, override)
        llm_names = commit.llm_coauthors
        llm_text = " | ".join(llm_names)
        claude = int(any("claude" in x.lower() or "opus" in x.lower() or "fable" in x.lower() for x in llm_names))
        openai = int(any("gpt" in x.lower() or "openai" in x.lower() or "codex" in x.lower() for x in llm_names))
        agent_author = int(commit.author_name.strip().lower() in {"agent", "claude", "codex"})

        # Commit-level accounting is exact only when the ledger names this SHA.
        # Pending transcript ranges are reported separately as allocation
        # candidates; a broad session range must never make a commit look
        # accounted when its usage cannot actually be assigned to that commit.
        if measure:
            state = "exact_measured"
        elif commit.commit == inst_sha:
            state = "instrumentation_commit_unmeasured"
        elif commit.timestamp_dt < inst_dt:
            state = "unmeasured_pre_instrumentation"
        else:
            state = "unmeasured_post_instrumentation"

        lean_files = sum(path.endswith(".lean") for path in commit.files)
        row = {
            "history_index": idx,
            "commit": commit.commit,
            "date": commit.timestamp_dt.date().isoformat(),
            "timestamp": commit.timestamp,
            "author_name": commit.author_name,
            "author_email": commit.author_email,
            "subject": commit.subject,
            "files_changed": len(commit.files),
            "lean_files_changed": lean_files,
            "additions": commit.additions,
            "deletions": commit.deletions,
            "lean_additions": commit.lean_additions,
            "lean_deletions": commit.lean_deletions,
            "binary_files": commit.binary_files,
            "llm_trailer": int(bool(llm_names)),
            "claude_trailer": claude,
            "openai_trailer": openai,
            "agent_author": agent_author,
            "llm_coauthors": llm_text,
            "assistance_class": assistance_class,
            "channel": channel,
            "assistance_evidence": evidence,
            "accounting_state": state,
            "pending_segment_count": len(pending_matches),
            "pending_segment_ids": " | ".join(w["segment_id"] for w in pending_matches),
            "ledger_rows": int(measure["ledger_rows"]) if measure else 0,
            "turns": int(measure["turns"]) if measure else 0,
            "input_tokens": int(measure["input_tokens"]) if measure else 0,
            "cache_write_tokens": int(measure["cache_write_tokens"]) if measure else 0,
            "cache_read_tokens": int(measure["cache_read_tokens"]) if measure else 0,
            "output_tokens": int(measure["output_tokens"]) if measure else 0,
            "billable_input_tokens": (
                int(measure["input_tokens"] + measure["cache_write_tokens"] + measure["cache_read_tokens"])
                if measure
                else 0
            ),
            "measured_agents": " | ".join(sorted(measure["agents"])) if measure else "",
            "measured_models": " | ".join(sorted(measure["models"])) if measure else "",
            **sflags,
            **{f"component_{name}": value for name, value in flags.items()},
        }
        # Extrapolation is only counted when we have positive evidence of LLM
        # assistance and no measured pending window that could already contain
        # the work. Users can assert chat-interface provenance in overrides.csv.
        row["extrapolation_eligible"] = int(
            not measure and not pending_matches and assistance_class == "llm"
        )
        rows.append(row)

    manifest_fields = list(rows[0].keys())
    write_csv(GENERATED / "commit_accounting_manifest.csv", rows, manifest_fields)

    # Pending transcript segments: measured usage whose precise commit allocation
    # is unknown. Candidate commits are reported, never silently assigned.
    pending_rows = []
    for w in windows:
        r = w["row"]
        candidates = [c for c in commits if w["match_start"] <= c.timestamp_dt <= w["match_end"]]
        tokens = list(r.get("t") or [0, 0, 0, 0])
        pending_rows.append(
            {
                "segment_id": w["segment_id"],
                "ledger_row": r.get("ledger_row", ""),
                "ledger_commit_label": r.get("c", ""),
                "session_id": r.get("sid", ""),
                "agent": r.get("a", ""),
                "activity": r.get("act", ""),
                "models": " | ".join(r.get("m") or []),
                "start_utc": w["start"].isoformat(),
                "end_utc": w["end"].isoformat(),
                "turns": int(r.get("n") or 0),
                "input_tokens": int(tokens[0]),
                "cache_write_tokens": int(tokens[1]),
                "cache_read_tokens": int(tokens[2]),
                "output_tokens": int(tokens[3]),
                "billable_input_tokens": int(tokens[0] + tokens[1] + tokens[2]),
                "candidate_commit_count": len(candidates),
                "candidate_commits": " | ".join(c.commit for c in candidates),
            }
        )
    pending_fields = list(pending_rows[0].keys()) if pending_rows else ["segment_id"]
    write_csv(GENERATED / "pending_segments.csv", pending_rows, pending_fields)

    # Ledger rows that reference commit hashes absent from the pinned HEAD history.
    off_history = []
    for sha, m in exact.items():
        if sha in commit_by_sha:
            continue
        off_history.append(
            {
                "commit": sha,
                "ledger_rows": m["ledger_rows"],
                "turns": m["turns"],
                "input_tokens": m["input_tokens"],
                "cache_write_tokens": m["cache_write_tokens"],
                "cache_read_tokens": m["cache_read_tokens"],
                "output_tokens": m["output_tokens"],
                "billable_input_tokens": m["input_tokens"] + m["cache_write_tokens"] + m["cache_read_tokens"],
            }
        )
    write_csv(
        GENERATED / "off_history_ledger_commits.csv",
        off_history,
        [
            "commit",
            "ledger_rows",
            "turns",
            "input_tokens",
            "cache_write_tokens",
            "cache_read_tokens",
            "output_tokens",
            "billable_input_tokens",
        ],
    )

    # Coverage summaries by state and by mathematical component.
    state_counts = Counter(r["accounting_state"] for r in rows)
    evidence_counts = Counter(r["assistance_evidence"] for r in rows)
    state_rows = [
        {"accounting_state": state, "commits": n, "share": n / len(rows)}
        for state, n in sorted(state_counts.items())
    ]
    write_csv(GENERATED / "accounting_state_summary.csv", state_rows, ["accounting_state", "commits", "share"])

    component_rows = []
    for name in component_names:
        subset = [r for r in rows if r[f"component_{name}"]]
        if not subset:
            continue
        component_rows.append(
            {
                "component": name,
                "commits": len(subset),
                "exact_measured": sum(r["accounting_state"] == "exact_measured" for r in subset),
                "pending_window_overlap": sum(int(r["pending_segment_count"]) > 0 for r in subset),
                "unmeasured_pre_instrumentation": sum(r["accounting_state"] == "unmeasured_pre_instrumentation" for r in subset),
                "unmeasured_post_instrumentation": sum(r["accounting_state"] == "unmeasured_post_instrumentation" for r in subset),
                "llm_evidence_unmeasured": sum(
                    r["accounting_state"] != "exact_measured" and r["assistance_class"] == "llm" for r in subset
                ),
                "exact_output_tokens": sum(r["output_tokens"] for r in subset),
                "exact_billable_input_tokens": sum(r["billable_input_tokens"] for r in subset),
            }
        )
    write_csv(
        GENERATED / "component_accounting_summary.csv",
        component_rows,
        list(component_rows[0].keys()) if component_rows else ["component"],
    )

    # Weekly coverage is useful for visualizing the transition from unobserved
    # history into increasingly instrumented development.
    weekly = defaultdict(lambda: Counter())
    for r in rows:
        dt = parse_dt(r["timestamp"])
        assert dt is not None
        year, week, _ = dt.isocalendar()
        key = f"{year}-W{week:02d}"
        weekly[key]["commits"] += 1
        weekly[key][r["accounting_state"]] += 1
        weekly[key]["llm_evidence"] += int(r["assistance_class"] == "llm")
    weekly_rows = []
    all_states = sorted(state_counts)
    for week in sorted(weekly):
        c = weekly[week]
        row = {"iso_week": week, "commits": c["commits"], "llm_evidence": c["llm_evidence"]}
        for state in all_states:
            row[state] = c[state]
        weekly_rows.append(row)
    write_csv(
        GENERATED / "accounting_coverage_by_week.csv",
        weekly_rows,
        ["iso_week", "commits", "llm_evidence", *all_states],
    )

    # Exploratory missing-cost model. It is trained only on exact measured
    # commits and validated with rolling-origin splits. Predictions are emitted
    # for all unmeasured commits, but only positive LLM-evidence commits outside
    # pending measured windows are counted toward the extrapolated total.
    feature_names = model_feature_names(component_names)
    exact_rows = [r for r in rows if r["accounting_state"] == "exact_measured"]
    exact_rows.sort(key=lambda r: r["timestamp"])
    targets = ["turns", "output_tokens", "billable_input_tokens"]
    alpha = float(CONFIG.get("ridge_alpha", 5.0))
    folds = int(CONFIG.get("rolling_validation_folds", 5))
    validation = []
    residuals = {target: [] for target in targets}
    splits = rolling_origin_splits(len(exact_rows), folds)
    xs_all = [feature_vector(r, component_names) for r in exact_rows]
    for fold_index, (train_idx, test_idx) in enumerate(splits, 1):
        train = list(train_idx)
        test = list(test_idx)
        for target in targets:
            model = RidgeLogModel(alpha=alpha).fit(
                [xs_all[i] for i in train], [float(exact_rows[i][target]) for i in train]
            )
            actuals = []
            preds = []
            fold_resid = []
            for i in test:
                actual = float(exact_rows[i][target])
                pred = model.predict_one(xs_all[i])
                actuals.append(actual)
                preds.append(pred)
                resid = math.log1p(actual) - math.log1p(pred)
                fold_resid.append(resid)
                residuals[target].append(resid)
            ratios = [(p + 1.0) / (a + 1.0) for p, a in zip(preds, actuals)]
            validation.append(
                {
                    "fold": fold_index,
                    "target": target,
                    "train_n": len(train),
                    "test_n": len(test),
                    "test_start": exact_rows[test[0]]["date"],
                    "test_end": exact_rows[test[-1]]["date"],
                    "median_abs_log_error": statistics.median(abs(x) for x in fold_resid),
                    "median_prediction_ratio": statistics.median(ratios),
                    "p10_prediction_ratio": quantile(ratios, 0.10),
                    "p90_prediction_ratio": quantile(ratios, 0.90),
                }
            )
    write_csv(
        GENERATED / "imputation_validation.csv",
        validation,
        list(validation[0].keys()) if validation else ["fold", "target"],
    )

    final_models = {}
    for target in targets:
        final_models[target] = RidgeLogModel(alpha=alpha).fit(
            xs_all, [float(r[target]) for r in exact_rows]
        )

    prediction_rows = []
    eligible_rows = []
    for r in rows:
        if r["accounting_state"] == "exact_measured":
            continue
        x = feature_vector(r, component_names)
        out = {
            "commit": r["commit"],
            "date": r["date"],
            "subject": r["subject"],
            "accounting_state": r["accounting_state"],
            "assistance_class": r["assistance_class"],
            "assistance_evidence": r["assistance_evidence"],
            "pending_segment_count": r["pending_segment_count"],
            "extrapolation_eligible": r["extrapolation_eligible"],
        }
        for target in targets:
            out[f"predicted_{target}"] = round(final_models[target].predict_one(x), 3)
        prediction_rows.append(out)
        if r["extrapolation_eligible"]:
            eligible_rows.append(out)
    write_csv(
        GENERATED / "imputation_predictions.csv",
        prediction_rows,
        list(prediction_rows[0].keys()) if prediction_rows else ["commit"],
    )

    # Empirical residual bootstrap gives a transparent sensitivity interval for
    # the aggregate extrapolated total. It is not a claim of statistical
    # identifiability; the manuscript labels it as exploratory.
    rng = random.Random(int(CONFIG.get("bootstrap_seed", 20260814)))
    draws = int(CONFIG.get("bootstrap_draws", 1000))
    boot = {target: [] for target in targets}
    centered_residuals = {}
    for target in targets:
        pool = residuals[target] or [0.0]
        center = statistics.median(pool)
        centered_residuals[target] = [r - center for r in pool]

    for _ in range(draws):
        for target in targets:
            pool = centered_residuals[target]
            total = 0.0
            for row in eligible_rows:
                pred = float(row[f"predicted_{target}"])
                resid = rng.choice(pool)
                total += max(0.0, math.expm1(math.log1p(pred) + resid))
            boot[target].append(total)

    measured_all = {
        "turns": sum(int(r.get("n") or 0) for r in token_rows),
        "input_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[0]) for r in token_rows),
        "cache_write_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[1]) for r in token_rows),
        "cache_read_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[2]) for r in token_rows),
        "output_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[3]) for r in token_rows),
    }
    measured_all["billable_input_tokens"] = (
        measured_all["input_tokens"] + measured_all["cache_write_tokens"] + measured_all["cache_read_tokens"]
    )
    lifetime_path = ROOT / ".llm_resource_tally/lifetime-totals.json"
    lifetime_snapshot = json.loads(lifetime_path.read_text()) if lifetime_path.exists() else {}
    lifetime_tokens = lifetime_snapshot.get("tokens") or {}
    lifetime_reconciliation = {
        "ledger_rows_current": len((ROOT / ".llm_resource_tally/ledger/ledger.jsonl").read_text().splitlines()),
        "lifetime_ledger_rows": int(lifetime_snapshot.get("ledger_rows") or 0),
        "ledger_turns_current": measured_all["turns"],
        "lifetime_turns": int(lifetime_snapshot.get("turns") or 0),
        "ledger_output_tokens_current": measured_all["output_tokens"],
        "lifetime_output_tokens": int(lifetime_tokens.get("output") or 0),
        "ledger_billable_input_current": measured_all["billable_input_tokens"],
        "lifetime_billable_input": int(lifetime_tokens.get("billable_input") or 0),
    }
    lifetime_reconciliation["snapshot_is_stale"] = any(
        [
            lifetime_reconciliation["ledger_rows_current"] != lifetime_reconciliation["lifetime_ledger_rows"],
            lifetime_reconciliation["ledger_turns_current"] != lifetime_reconciliation["lifetime_turns"],
            lifetime_reconciliation["ledger_output_tokens_current"] != lifetime_reconciliation["lifetime_output_tokens"],
        ]
    )
    exact_on_history = {
        "turns": sum(r["turns"] for r in rows),
        "input_tokens": sum(r["input_tokens"] for r in rows),
        "cache_write_tokens": sum(r["cache_write_tokens"] for r in rows),
        "cache_read_tokens": sum(r["cache_read_tokens"] for r in rows),
        "output_tokens": sum(r["output_tokens"] for r in rows),
        "billable_input_tokens": sum(r["billable_input_tokens"] for r in rows),
    }
    pending_totals = {
        "turns": sum(r["turns"] for r in pending_rows),
        "input_tokens": sum(r["input_tokens"] for r in pending_rows),
        "cache_write_tokens": sum(r["cache_write_tokens"] for r in pending_rows),
        "cache_read_tokens": sum(r["cache_read_tokens"] for r in pending_rows),
        "output_tokens": sum(r["output_tokens"] for r in pending_rows),
        "billable_input_tokens": sum(r["billable_input_tokens"] for r in pending_rows),
    }

    exact_all = {
        "turns": sum(int(m["turns"]) for m in exact.values()),
        "input_tokens": sum(int(m["input_tokens"]) for m in exact.values()),
        "cache_write_tokens": sum(int(m["cache_write_tokens"]) for m in exact.values()),
        "cache_read_tokens": sum(int(m["cache_read_tokens"]) for m in exact.values()),
        "output_tokens": sum(int(m["output_tokens"]) for m in exact.values()),
    }
    exact_all["billable_input_tokens"] = (
        exact_all["input_tokens"] + exact_all["cache_write_tokens"] + exact_all["cache_read_tokens"]
    )
    token_breakdown_rows = []
    for key, label in [
        ("input_tokens", "ordinary input"),
        ("cache_write_tokens", "cache write"),
        ("cache_read_tokens", "cache read"),
        ("output_tokens", "output"),
        ("billable_input_tokens", "billable-input measure"),
    ]:
        token_breakdown_rows.append({
            "token_kind": key,
            "label": label,
            "ledger_total": measured_all[key],
            "exact_commit_attributed_all": exact_all[key],
            "pending_session_level": pending_totals[key],
            "exact_on_pinned_history": exact_on_history[key],
        })
    write_csv(
        GENERATED / "measured_token_breakdown.csv",
        token_breakdown_rows,
        list(token_breakdown_rows[0].keys()),
    )

    extrapolated = {}
    for target in targets:
        point = sum(float(r[f"predicted_{target}"]) for r in eligible_rows)
        # Normalize the residual bootstrap to the model point estimate. The
        # residual distribution is intentionally used only as a sensitivity
        # shape; without this normalization Jensen's inequality shifts the
        # aggregate bootstrap upward even after centering log residuals.
        raw_boot = boot[target]
        boot_median = quantile(raw_boot, 0.50) if raw_boot else point
        scale = point / boot_median if boot_median > 0 else 1.0
        adjusted_boot = [x * scale for x in raw_boot]
        extrapolated[target] = {
            "point": point,
            "p05": quantile(adjusted_boot, 0.05),
            "p95": quantile(adjusted_boot, 0.95),
        }

    summary = {
        "schema": "formalization-draft2/accounting-summary/v1",
        "history_cutoff_commit": CUTOFF,
        "history_commit_count": len(rows),
        "instrumentation_commit": inst_sha,
        "instrumentation_time_utc": inst_dt.isoformat(),
        "ledger_exact_commit_ids": len(exact),
        "ledger_exact_commits_on_history": sum(sha in commit_by_sha for sha in exact),
        "ledger_exact_commits_off_history": sum(sha not in commit_by_sha for sha in exact),
        "commits_before_instrumentation": sum(c.timestamp_dt < inst_dt for c in commits),
        "commits_without_exact_accounting": sum(r["accounting_state"] != "exact_measured" for r in rows),
        "commits_overlapping_pending_windows": sum(int(r["pending_segment_count"]) > 0 for r in rows),
        "pending_segments": len(pending_rows),
        "pending_segments_turns": pending_totals["turns"],
        "pending_segments_output_tokens": pending_totals["output_tokens"],
        "pending_segments_billable_input_tokens": pending_totals["billable_input_tokens"],
        "measured_lower_bound": measured_all,
        "lifetime_snapshot_reconciliation": lifetime_reconciliation,
        "exact_on_history": exact_on_history,
        "accounting_states": dict(state_counts),
        "assistance_evidence": dict(evidence_counts),
        "llm_evidence_commits": sum(r["assistance_class"] == "llm" for r in rows),
        "llm_evidence_unmeasured_commits": sum(
            r["assistance_class"] == "llm" and r["accounting_state"] != "exact_measured" for r in rows
        ),
        "extrapolation_eligible_commits": len(eligible_rows),
        "exploratory_extrapolation": extrapolated,
        "model": {
            "features": feature_names,
            "ridge_alpha": alpha,
            "rolling_validation_folds": len(splits),
            "bootstrap_draws": draws,
            "warning": "Exploratory missing-cost model; missingness is not random, pending session windows are only allocation candidates, and chat-interface provenance requires manual overrides.",
        },
    }
    (GENERATED / "accounting_summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    # Human-readable text report for auditing before any number is quoted.
    report = []
    report.append("# Accounting coverage report")
    report.append("")
    report.append(f"Pinned history cutoff: `{CUTOFF}` ({len(rows):,} commits).")
    report.append(f"Instrumentation enters history at `{inst_sha}` ({inst_dt.isoformat()}).")
    report.append("")
    report.append("## Measured lower bound")
    report.append("")
    report.append(f"- ledger model turns: **{measured_all['turns']:,}**")
    report.append(f"- output tokens: **{measured_all['output_tokens']:,}**")
    report.append(f"- billable-input accounting measure: **{measured_all['billable_input_tokens']:,}**")
    report.append(f"- exact ledger commit IDs: **{len(exact):,}**; on pinned history: **{summary['ledger_exact_commits_on_history']:,}**")
    report.append(f"- pinned-history commits without exact commit-level accounting: **{summary['commits_without_exact_accounting']:,}**")
    report.append(f"- commits preceding the instrumentation commit: **{summary['commits_before_instrumentation']:,}**")
    report.append(f"- measured but commit-unattributed pending segments: **{len(pending_rows):,}** containing **{pending_totals['turns']:,}** turns")
    if lifetime_reconciliation["snapshot_is_stale"]:
        report.append(
            f"- note: `lifetime-totals.json` is behind the current ledger "
            f"({lifetime_reconciliation['lifetime_ledger_rows']:,} vs. {lifetime_reconciliation['ledger_rows_current']:,} ledger rows); "
            "the paper pipeline recomputes measured totals from the ledger itself"
        )
    report.append("")
    report.append("## Commit accounting states")
    report.append("")
    for state, n in sorted(state_counts.items()):
        report.append(f"- `{state}`: **{n:,}**")
    report.append("")
    report.append("## Provenance warning")
    report.append("")
    report.append(
        "Automatic LLM provenance is conservative: it recognizes explicit LLM co-author trailers and a small set of agent authors. "
        "Chat-interface work must be entered in `data/accounting_overrides.csv`; absent such an override, it remains `unknown`."
    )
    report.append("")
    report.append("## Exploratory extrapolation")
    report.append("")
    report.append(
        f"The current model has {len(eligible_rows):,} extrapolation-eligible commits. "
        "These are positive-evidence LLM-assisted commits with neither exact accounting nor overlap with a measured pending segment."
    )
    for target in targets:
        x = extrapolated[target]
        report.append(
            f"- {target}: point **{format_int(x['point'])}**, residual-bootstrap 5--95% sensitivity interval "
            f"**{format_int(x['p05'])}--{format_int(x['p95'])}**"
        )
    report.append("")
    report.append(
        "These model-based values are not part of the measured lower bound and should not be quoted without first auditing the override file, the validation table, and the missingness assumptions."
    )
    (GENERATED / "ACCOUNTING_REPORT.md").write_text("\n".join(report) + "\n")

    # LaTeX macros and two small tables used directly by paper.tex.
    def state_n(name: str) -> int:
        return state_counts.get(name, 0)

    macros = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        f"\\newcommand{{\\AccountingCutoffCommit}}{{\\texttt{{{CUTOFF[:12]}}}}}",
        f"\\newcommand{{\\HistoryCommitCount}}{{{format_int(len(rows))}}}",
        f"\\newcommand{{\\ExactMeasuredCommitCount}}{{{format_int(state_n('exact_measured'))}}}",
        f"\\newcommand{{\\CommitsWithoutExactAccounting}}{{{format_int(summary['commits_without_exact_accounting'])}}}",
        f"\\newcommand{{\\CommitsBeforeInstrumentation}}{{{format_int(summary['commits_before_instrumentation'])}}}",
        f"\\newcommand{{\\PendingWindowOverlapCommitCount}}{{{format_int(summary['commits_overlapping_pending_windows'])}}}",
        f"\\newcommand{{\\PreInstrumentationCommitCount}}{{{format_int(state_n('unmeasured_pre_instrumentation'))}}}",
        f"\\newcommand{{\\PostInstrumentationUnmeasuredCommitCount}}{{{format_int(state_n('unmeasured_post_instrumentation'))}}}",
        f"\\newcommand{{\\LedgerTurns}}{{{format_int(measured_all['turns'])}}}",
        f"\\newcommand{{\\LedgerOutputTokens}}{{{format_int(measured_all['output_tokens'])}}}",
        f"\\newcommand{{\\LedgerBillableInputTokens}}{{{format_int(measured_all['billable_input_tokens'])}}}",
        f"\\newcommand{{\\PendingSegmentCount}}{{{format_int(len(pending_rows))}}}",
        f"\\newcommand{{\\PendingTurns}}{{{format_int(pending_totals['turns'])}}}",
        f"\\newcommand{{\\LLMEvidenceCommitCount}}{{{format_int(summary['llm_evidence_commits'])}}}",
        f"\\newcommand{{\\LLMEvidenceUnmeasuredCommitCount}}{{{format_int(summary['llm_evidence_unmeasured_commits'])}}}",
        f"\\newcommand{{\\ExtrapolationEligibleCommitCount}}{{{format_int(len(eligible_rows))}}}",
    ]
    (GENERATED / "accounting_macros.tex").write_text("\n".join(macros) + "\n")

    token_lines = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        "\\begin{tabular}{lrrr}",
        "\\toprule",
        "Token kind & Ledger total & Exact-attributed & Pending \\\\",
        "\\midrule",
    ]
    for r in token_breakdown_rows:
        token_lines.append(
            f"{latex_escape(r['label'])} & {r['ledger_total']:,} & {r['exact_commit_attributed_all']:,} & {r['pending_session_level']:,} \\\\")
    token_lines += ["\\bottomrule", "\\end{tabular}"]
    (GENERATED / "measured_token_breakdown_table.tex").write_text("\n".join(token_lines) + "\n")

    state_label = {
        "exact_measured": "Exact commit-attributed measurement",
        "instrumentation_commit_unmeasured": "Instrumentation commit",
        "unmeasured_pre_instrumentation": "Pre-instrumentation, unmeasured",
        "unmeasured_post_instrumentation": "Post-instrumentation, unmeasured",
    }
    table_lines = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        "\\begin{tabular}{lr}",
        "\\toprule",
        "Accounting state & Commits \\\\",
        "\\midrule",
    ]
    for state in sorted(state_counts):
        table_lines.append(f"{latex_escape(state_label.get(state, state))} & {state_counts[state]:,} \\\\")
    table_lines += ["\\bottomrule", "\\end{tabular}"]
    (GENERATED / "accounting_state_table.tex").write_text("\n".join(table_lines) + "\n")

    component_lines = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        "\\begin{tabular}{lrrrr}",
        "\\toprule",
        "Component & Commits & Exact & Pending-window overlap & LLM-evidence unmeasured \\\\",
        "\\midrule",
    ]
    for r in component_rows:
        component_lines.append(
            f"{latex_escape(r['component'].replace('_', ' '))} & {r['commits']:,} & {r['exact_measured']:,} & "
            f"{r['pending_window_overlap']:,} & {r['llm_evidence_unmeasured']:,} \\\\")
    component_lines += ["\\bottomrule", "\\end{tabular}"]
    (GENERATED / "component_accounting_table.tex").write_text("\n".join(component_lines) + "\n")

    print(f"accounting: {len(rows)} commits, {state_n('exact_measured')} exact measured, {len(pending_rows)} pending segments")
    print(f"accounting: outputs written under {GENERATED.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
