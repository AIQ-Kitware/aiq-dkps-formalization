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
    canonical_model_name,
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
    model_provider,
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
SNAPSHOTS = HERE / "snapshots"
DATA = HERE / "data"
CONFIG = json.loads((HERE / "analysis_config.json").read_text())
ROOT = repo_root(HERE)
CUTOFF = CONFIG["history_cutoff_commit"]
PRIMARY_REPOSITORY = CONFIG.get("primary_repository", "aiq-dkps-formalization")
LEDGER_REPOSITORIES = list(CONFIG.get("included_ledger_repositories", {PRIMARY_REPOSITORY: ""}))
EXCLUDED_ONLY_PREFIXES = tuple(CONFIG.get("exclude_commits_if_only_touch", []))
GPT_CHAT_RULE = CONFIG.get("gpt_chat_trailer_rule", {})


def commit_is_excluded_from_study(commit) -> bool:
    """Exclude a commit only when every touched path is explicitly blocklisted."""
    if not commit.files or not EXCLUDED_ONLY_PREFIXES:
        return False
    return all(any(path.startswith(prefix) for prefix in EXCLUDED_ONLY_PREFIXES) for path in commit.files)


def bounded_gpt_chat_resolution(commit, measure: dict | None, trailer_models: set[str]) -> tuple[set[str], str, str]:
    """Resolve the author-confirmed GPT chat labels for this historical study.

    The rule is intentionally narrow: only unledgered commits, only the recorded
    study interval, and only the configured High/Thinking labels.  Raw trailer
    labels remain in the manifest.  Exact ledger attribution always wins.
    """
    if measure and GPT_CHAT_RULE.get("apply_only_without_exact_ledger", True):
        return set(trailer_models), "", ""
    start = GPT_CHAT_RULE.get("start_date", "")
    end = GPT_CHAT_RULE.get("end_date", "")
    # Date-bounded provenance rules follow the Git author timestamp date, not
    # a UTC-converted date; a late-evening US commit can otherwise move a day.
    day = commit.timestamp[:10]
    if start and day < start:
        return set(trailer_models), "", ""
    if end and day > end:
        return set(trailer_models), "", ""
    aliases = {canonical_model_name(x) for x in GPT_CHAT_RULE.get("raw_models", [])}
    if not (set(trailer_models) & aliases):
        return set(trailer_models), "", ""
    resolved = set(trailer_models) - aliases
    resolved.add(canonical_model_name(GPT_CHAT_RULE.get("resolved_model", "gpt-5.6-sol")))
    return resolved, GPT_CHAT_RULE.get("channel", "chat_interface"), "bounded_gpt_chat_trailer_rule"


def infer_assistance(
    commit, override: dict | None, measure: dict | None, heuristic_channel: str = "", heuristic_evidence: str = ""
) -> tuple[str, str, str]:
    """Return assistance_class, channel, evidence with explicit precedence."""
    if override:
        cls = override.get("assistance_class") or "unknown"
        channel = override.get("channel") or "unknown"
        return cls, channel, "manual_override"
    if measure:
        return "llm", "agent_harness", "exact_ledger"
    if heuristic_channel:
        return "llm", heuristic_channel, heuristic_evidence or "bounded_provenance_rule"

    names = commit.llm_coauthors
    author_agent = commit.author_name.strip().lower() in {"agent", "claude", "codex"}
    if names:
        return "llm", "unknown", "llm_coauthor_trailer"
    if author_agent:
        return "llm", "agent_harness", "agent_author"
    return "unknown", "unknown", "none"


def override_models(override: dict | None) -> list[str]:
    if not override:
        return []
    raw = override.get("models") or override.get("model") or ""
    pieces = [piece.strip() for piece in raw.replace(";", "|").split("|") if piece.strip()]
    return sorted({canonical_model_name(piece) for piece in pieces})


def load_pricing(path: pathlib.Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    out = {}
    with path.open(newline="", encoding="utf-8") as file:
        for row in csv.DictReader(file):
            model = canonical_model_name(row.get("model") or "")
            if model:
                out[model] = {k: (v or "").strip() for k, v in row.items()}
    return out


def numeric_rate(row: dict, key: str) -> float | None:
    value = (row.get(key) or "").strip()
    if value == "":
        return None
    return float(value)


def sum_token_rows(rows: list[dict]) -> dict[str, int]:
    totals = {
        "turns": sum(int(r.get("n") or 0) for r in rows),
        "input_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[0]) for r in rows),
        "cache_write_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[1]) for r in rows),
        "cache_read_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[2]) for r in rows),
        "output_tokens": sum(int((r.get("t") or [0, 0, 0, 0])[3]) for r in rows),
    }
    totals["billable_input_tokens"] = (
        totals["input_tokens"] + totals["cache_write_tokens"] + totals["cache_read_tokens"]
    )
    return totals


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    SNAPSHOTS.mkdir(parents=True, exist_ok=True)
    repository_commits = load_commits(ROOT, CUTOFF)
    cutoff_commit = next((c for c in repository_commits if c.commit == CUTOFF), repository_commits[-1])
    cutoff_dt = cutoff_commit.timestamp_dt

    excluded_commits = [c for c in repository_commits if commit_is_excluded_from_study(c)]
    excluded_sha = {c.commit for c in excluded_commits}
    commits = [c for c in repository_commits if c.commit not in excluded_sha]
    commit_by_sha = {c.commit: c for c in commits}

    # Commit-level coverage uses only the primary repository. Program-wide token
    # accounting may include author-confirmed supporting repositories, notably
    # the TauCeti-foundations work retained under another historical repo label.
    exact, primary_pending, _primary_token_rows = load_ledger(
        ROOT, [PRIMARY_REPOSITORY], recorded_before=cutoff_dt
    )
    program_exact, program_pending, program_token_rows = load_ledger(
        ROOT, LEDGER_REPOSITORIES, recorded_before=cutoff_dt
    )
    # Paper-production commits are excluded from the formalization study when
    # they touch only the draft2 paper path. Exact token rows tied to those SHAs
    # are excluded too; ambiguous pending sessions remain measured and visible.
    token_rows = [
        r for r in program_token_rows
        if not (r.get("repository") == PRIMARY_REPOSITORY and str(r.get("c") or "") in excluded_sha)
    ]
    pending = [r for r in program_pending if r in token_rows]
    primary_windows = pending_windows(primary_pending, float(CONFIG.get("pending_window_minutes", 0)))
    program_windows = pending_windows(pending, float(CONFIG.get("pending_window_minutes", 0)))

    inst_sha, inst_dt = instrumentation_commit(ROOT, CUTOFF)
    overrides = load_overrides(DATA / "accounting_overrides.csv")
    patterns = CONFIG["component_patterns"]
    component_names = list(patterns)

    exclusion_rows = [
        {
            "commit": c.commit,
            "date": c.timestamp_dt.date().isoformat(),
            "subject": c.subject,
            "files_changed": len(c.files),
            "paths": " | ".join(c.files),
            "reason": "all touched paths are under exclude_commits_if_only_touch",
        }
        for c in excluded_commits
    ]
    write_csv(
        GENERATED / "study_commit_exclusions.csv",
        exclusion_rows,
        ["commit", "date", "subject", "files_changed", "paths", "reason"],
    )

    rows: list[dict] = []
    for idx, commit in enumerate(commits, 1):
        measure = exact.get(commit.commit)
        pending_matches = matching_pending_windows(commit.timestamp_dt, primary_windows)
        flags = component_flags(commit.files, patterns)
        sflags = subject_flags(commit.subject)
        override = overrides.get(commit.commit)
        llm_names = commit.llm_coauthors
        llm_text = " | ".join(llm_names)
        trailer_models = set(commit.llm_coauthor_models)
        manual_models = set(override_models(override))
        ledger_models = set(measure["models"]) - {"<synthetic>"} if measure else set()
        heuristic_models, heuristic_channel, heuristic_evidence = bounded_gpt_chat_resolution(
            commit, measure, trailer_models
        )
        assistance_class, channel, evidence = infer_assistance(
            commit, override, measure, heuristic_channel, heuristic_evidence
        )

        # Distinguish raw Git provenance from the model used for unmeasured-cost
        # stratification. Exact ledger attribution is authoritative when present;
        # manual model overrides come next; the time-bounded GPT chat rule is
        # used only for otherwise unmetered High/Thinking trailer labels.
        declared_models = trailer_models | manual_models
        if measure:
            resolved_models = set(ledger_models)
            model_resolution_evidence = "exact_ledger"
        elif manual_models:
            resolved_models = set(manual_models)
            model_resolution_evidence = "manual_override"
        elif heuristic_evidence:
            resolved_models = set(heuristic_models)
            model_resolution_evidence = heuristic_evidence
        else:
            resolved_models = set(trailer_models)
            model_resolution_evidence = "git_trailer" if trailer_models else "none"

        if measure and declared_models:
            if ledger_models == declared_models:
                model_provenance_status = "exact_match"
            elif ledger_models & declared_models:
                model_provenance_status = "partial_overlap"
            else:
                model_provenance_status = "disjoint_signals"
        elif measure:
            model_provenance_status = "ledger_only"
        elif declared_models:
            model_provenance_status = "declared_model_without_exact_ledger"
        else:
            model_provenance_status = "no_model_evidence"
        claude = int(any(model.startswith("claude-") for model in (declared_models | resolved_models)))
        openai = int(any(model.startswith("gpt-") or model.startswith("openai-") or model.startswith("codex-") for model in (declared_models | resolved_models)))
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
            "repository": PRIMARY_REPOSITORY,
            "study_included": 1,
            "llm_coauthors": llm_text,
            "trailer_model_labels_raw": llm_text,
            "trailer_models": " | ".join(sorted(trailer_models)),
            "override_models": " | ".join(sorted(manual_models)),
            "heuristic_models": " | ".join(sorted(heuristic_models if heuristic_evidence else [])),
            "declared_models": " | ".join(sorted(declared_models)),
            "resolved_models": " | ".join(sorted(resolved_models)),
            "model_resolution_evidence": model_resolution_evidence,
            "ledger_models": " | ".join(sorted(ledger_models)),
            "model_provenance_status": model_provenance_status,
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

    gpt_rule_rows = [
        {
            "commit": r["commit"],
            "date": r["date"],
            "subject": r["subject"],
            "raw_trailer_labels": r["trailer_model_labels_raw"],
            "trailer_models": r["trailer_models"],
            "resolved_models": r["resolved_models"],
            "channel": r["channel"],
            "rule": r["assistance_evidence"],
        }
        for r in rows
        if r["assistance_evidence"] == "bounded_gpt_chat_trailer_rule"
    ]
    write_csv(
        GENERATED / "gpt_chat_rule_matches.csv",
        gpt_rule_rows,
        ["commit", "date", "subject", "raw_trailer_labels", "trailer_models", "resolved_models", "channel", "rule"],
    )

    # Pending transcript segments: measured usage whose precise commit allocation
    # is unknown. Candidate commits are reported, never silently assigned.
    pending_rows = []
    for w in program_windows:
        r = w["row"]
        repository = r.get("repository", "")
        candidates = (
            [c for c in commits if w["match_start"] <= c.timestamp_dt <= w["match_end"]]
            if repository == PRIMARY_REPOSITORY else []
        )
        tokens = list(r.get("t") or [0, 0, 0, 0])
        pending_rows.append(
            {
                "segment_id": w["segment_id"],
                "repository": repository,
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
                "candidate_scope": (
                    "primary_repository_history"
                    if repository == PRIMARY_REPOSITORY
                    else "cross_repository_history_not_loaded"
                ),
            }
        )
    pending_fields = list(pending_rows[0].keys()) if pending_rows else ["segment_id"]
    write_csv(GENERATED / "pending_segments.csv", pending_rows, pending_fields)

    # Exact ledger rows not represented by an included primary-repository commit.
    # Cross-repository rows are not "missing"; their Git histories are simply
    # outside this checkout and remain part of the program-wide measured total.
    off_history = []
    for sha, m in program_exact.items():
        repository = m.get("repository", "")
        if repository == PRIMARY_REPOSITORY and sha in excluded_sha:
            continue
        if repository == PRIMARY_REPOSITORY and sha in commit_by_sha:
            continue
        off_history.append(
            {
                "repository": repository,
                "commit": sha,
                "scope_relation": (
                    "cross_repository_in_program"
                    if repository != PRIMARY_REPOSITORY
                    else "primary_repository_not_in_included_history"
                ),
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
            "repository",
            "commit",
            "scope_relation",
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
    targets = ["turns", "input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens", "billable_input_tokens"]
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
        resolved_models = {m for m in r["resolved_models"].split(" | ") if m}
        if len(resolved_models) == 1:
            imputation_model = next(iter(resolved_models))
            imputation_model_evidence = r["model_resolution_evidence"]
        elif len(resolved_models) > 1:
            imputation_model = "<multiple>"
            imputation_model_evidence = "multiple_resolved_models"
        else:
            imputation_model = "<unknown>"
            imputation_model_evidence = "no_model_provenance"
        out = {
            "commit": r["commit"],
            "date": r["date"],
            "subject": r["subject"],
            "accounting_state": r["accounting_state"],
            "assistance_class": r["assistance_class"],
            "assistance_evidence": r["assistance_evidence"],
            "channel": r["channel"],
            "trailer_models": r["trailer_models"],
            "override_models": r["override_models"],
            "heuristic_models": r["heuristic_models"],
            "resolved_models": r["resolved_models"],
            "model_resolution_evidence": r["model_resolution_evidence"],
            "imputation_model": imputation_model,
            "imputation_model_evidence": imputation_model_evidence,
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

    # Program-wide measured usage.  This includes every author-confirmed ledger
    # repository in scope, but excludes exact rows tied solely to this paper's
    # own draft2-production commits.
    measured_all = sum_token_rows(token_rows)

    # Repository-level accounting keeps the cross-repository contribution
    # visible rather than letting it disappear into one project-wide scalar.
    repository_stats = []
    for repository in LEDGER_REPOSITORIES:
        repo_rows = [r for r in token_rows if r.get("repository") == repository]
        totals = sum_token_rows(repo_rows)
        repository_stats.append({
            "repository": repository,
            "scope_label": CONFIG.get("included_ledger_repositories", {}).get(repository, ""),
            "token_rows": len(repo_rows),
            "exact_rows": sum(not str(r.get("c") or "").startswith("pending@") for r in repo_rows),
            "pending_rows": sum(str(r.get("c") or "").startswith("pending@") for r in repo_rows),
            **totals,
        })
    write_csv(
        GENERATED / "ledger_repository_summary.csv",
        repository_stats,
        list(repository_stats[0].keys()) if repository_stats else ["repository"],
    )

    # Reconcile the committed lifetime snapshot against the *entire current raw
    # ledger*, not against the paper's scoped/pinned subset.  This keeps the
    # health check logically separate from the study-universe definition.
    _raw_exact, _raw_pending, raw_current_token_rows = load_ledger(ROOT)
    raw_current_totals = sum_token_rows(raw_current_token_rows)
    lifetime_path = ROOT / ".llm_resource_tally/lifetime-totals.json"
    lifetime_snapshot = json.loads(lifetime_path.read_text()) if lifetime_path.exists() else {}
    lifetime_tokens = lifetime_snapshot.get("tokens") or {}
    lifetime_reconciliation = {
        "ledger_rows_current": len((ROOT / ".llm_resource_tally/ledger/ledger.jsonl").read_text().splitlines()),
        "lifetime_ledger_rows": int(lifetime_snapshot.get("ledger_rows") or 0),
        "ledger_turns_current": raw_current_totals["turns"],
        "lifetime_turns": int(lifetime_snapshot.get("turns") or 0),
        "ledger_output_tokens_current": raw_current_totals["output_tokens"],
        "lifetime_output_tokens": int(lifetime_tokens.get("output") or 0),
        "ledger_billable_input_current": raw_current_totals["billable_input_tokens"],
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
    pending_totals = sum_token_rows([r for r in token_rows if str(r.get("c") or "").startswith("pending@")])
    exact_program_rows = [r for r in token_rows if (r.get("c") or "") and not str(r.get("c") or "").startswith("pending@") ]
    exact_all = sum_token_rows(exact_program_rows)

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

    # Exact model attribution for measured tokens. Ledger schema v3 carries a
    # by-model token vector (`bm`) even when a session switched models, so this
    # aggregation does not duplicate mixed-model rows. Turns are intentionally
    # not assigned per model because the ledger has no by-model turn count.
    model_stats = defaultdict(lambda: {
        "ledger_rows": 0,
        "exact_rows": 0,
        "pending_rows": 0,
        "input_tokens": 0,
        "cache_write_tokens": 0,
        "cache_read_tokens": 0,
        "output_tokens": 0,
        "exact_input_tokens": 0,
        "exact_cache_write_tokens": 0,
        "exact_cache_read_tokens": 0,
        "exact_output_tokens": 0,
        "pending_input_tokens": 0,
        "pending_cache_write_tokens": 0,
        "pending_cache_read_tokens": 0,
        "pending_output_tokens": 0,
        "exact_on_history_input_tokens": 0,
        "exact_on_history_cache_write_tokens": 0,
        "exact_on_history_cache_read_tokens": 0,
        "exact_on_history_output_tokens": 0,
    })
    for ledger_row in token_rows:
        commit_label = str(ledger_row.get("c") or "")
        is_pending = commit_label.startswith("pending@")
        is_exact = bool(commit_label) and not is_pending
        on_history = (
            is_exact
            and ledger_row.get("repository") == PRIMARY_REPOSITORY
            and commit_label in commit_by_sha
        )
        for raw_model, raw_values in (ledger_row.get("bm") or {}).items():
            model = canonical_model_name(str(raw_model))
            values = [int(v or 0) for v in raw_values]
            stat = model_stats[model]
            stat["ledger_rows"] += 1
            stat["pending_rows"] += int(is_pending)
            stat["exact_rows"] += int(is_exact)
            for token_name, value in zip(("input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens"), values):
                stat[token_name] += value
                if is_exact:
                    stat[f"exact_{token_name}"] += value
                if is_pending:
                    stat[f"pending_{token_name}"] += value
                if on_history:
                    stat[f"exact_on_history_{token_name}"] += value

    pricing = load_pricing(DATA / "model_pricing.csv")
    model_token_rows = []
    model_cost_rows = []
    for model in sorted(model_stats, key=lambda m: model_stats[m]["output_tokens"], reverse=True):
        stat = model_stats[model]
        row = {"model": model, "provider": model_provider(model), **stat}
        row["billable_input_tokens"] = row["input_tokens"] + row["cache_write_tokens"] + row["cache_read_tokens"]
        row["exact_billable_input_tokens"] = row["exact_input_tokens"] + row["exact_cache_write_tokens"] + row["exact_cache_read_tokens"]
        row["pending_billable_input_tokens"] = row["pending_input_tokens"] + row["pending_cache_write_tokens"] + row["pending_cache_read_tokens"]
        model_token_rows.append(row)

        price = pricing.get(model, {})
        rate_keys = (
            "input_usd_per_million",
            "cache_write_usd_per_million",
            "cache_read_usd_per_million",
            "output_usd_per_million",
        )
        rates = [numeric_rate(price, key) for key in rate_keys]
        complete = all(rate is not None for rate in rates)
        cost = None
        if complete:
            cost = sum(
                tokens * rate / 1_000_000
                for tokens, rate in zip(
                    (row["input_tokens"], row["cache_write_tokens"], row["cache_read_tokens"], row["output_tokens"]),
                    rates,
                )
            )
        model_cost_rows.append({
            "model": model,
            "provider": model_provider(model),
            **{key: price.get(key, "") for key in rate_keys},
            "pricing_effective_date": price.get("effective_date", ""),
            "pricing_source": price.get("source", ""),
            "pricing_notes": price.get("notes", ""),
            "pricing_complete": int(complete),
            "measured_cost_usd": "" if cost is None else f"{cost:.6f}",
            "input_tokens": row["input_tokens"],
            "cache_write_tokens": row["cache_write_tokens"],
            "cache_read_tokens": row["cache_read_tokens"],
            "output_tokens": row["output_tokens"],
        })
    write_csv(
        GENERATED / "model_token_breakdown.csv",
        model_token_rows,
        list(model_token_rows[0].keys()) if model_token_rows else ["model"],
    )
    write_csv(
        GENERATED / "model_cost_breakdown.csv",
        model_cost_rows,
        list(model_cost_rows[0].keys()) if model_cost_rows else ["model"],
    )

    # Reconcile two independent model-provenance channels: Git co-author
    # trailers/manual annotations and exact ledger model attribution.  A missing
    # trailer is not itself an error, so we preserve relation classes rather
    # than collapsing everything into a binary disagreement flag.
    reconciliation_rows = []
    disagreement_rows = []
    chat_candidate_rows = []
    all_models = set(model_stats)
    for r in rows:
        trailer = {m for m in r["trailer_models"].split(" | ") if m}
        manual = {m for m in r["override_models"].split(" | ") if m}
        declared = trailer | manual
        ledger_set = {m for m in r["ledger_models"].split(" | ") if m}
        all_models |= declared | ledger_set
        if declared or ledger_set:
            rec = {
                "commit": r["commit"],
                "date": r["date"],
                "subject": r["subject"],
                "trailer_models": r["trailer_models"],
                "override_models": r["override_models"],
                "heuristic_models": r["heuristic_models"],
                "resolved_models": r["resolved_models"],
                "model_resolution_evidence": r["model_resolution_evidence"],
                "ledger_models": r["ledger_models"],
                "model_provenance_status": r["model_provenance_status"],
                "accounting_state": r["accounting_state"],
                "channel": r["channel"],
                "pending_segment_count": r["pending_segment_count"],
            }
            reconciliation_rows.append(rec)
            if r["model_provenance_status"] in {"partial_overlap", "disjoint_signals"}:
                disagreement_rows.append(rec)
        if (
            "gpt-5.6-sol" in declared
            and r["channel"] == "unknown"
            and "gpt-5.6-sol" not in ledger_set
        ):
            chat_candidate_rows.append({
                "commit": r["commit"],
                "date": r["date"],
                "subject": r["subject"],
                "trailer_models": r["trailer_models"],
                "ledger_models": r["ledger_models"],
                "accounting_state": r["accounting_state"],
                "pending_segment_count": r["pending_segment_count"],
                "has_other_exact_ledger_model": int(bool(ledger_set)),
                "review_status": "candidate_only",
                "reason": "GPT-5.6 Sol is declared in Git/manual provenance but has no exact GPT-5.6 Sol ledger attribution. This is consistent with unmetered chat-interface work but does not prove the channel; confirm before overriding.",
            })
    rec_fields = list(reconciliation_rows[0].keys()) if reconciliation_rows else ["commit"]
    write_csv(GENERATED / "model_provenance_reconciliation.csv", reconciliation_rows, rec_fields)
    write_csv(GENERATED / "model_provenance_disagreements.csv", disagreement_rows, rec_fields)
    write_csv(
        GENERATED / "chat_interface_review_candidates.csv",
        chat_candidate_rows,
        list(chat_candidate_rows[0].keys()) if chat_candidate_rows else ["commit"],
    )

    # Compare raw trailer labels, study-resolved model provenance, and exact
    # ledger attribution without pretending they are the same signal.
    all_models |= {
        m for r in rows for m in r["resolved_models"].split(" | ") if m
    }
    coauthor_model_rows = []
    for model in sorted(all_models):
        trailer_commits = [r for r in rows if model in {m for m in r["trailer_models"].split(" | ") if m}]
        resolved_commits = [r for r in rows if model in {m for m in r["resolved_models"].split(" | ") if m}]
        override_commits = [r for r in rows if model in {m for m in r["override_models"].split(" | ") if m}]
        ledger_commits = [r for r in rows if model in {m for m in r["ledger_models"].split(" | ") if m}]
        raw_overlap = [r for r in trailer_commits if model in {m for m in r["ledger_models"].split(" | ") if m}]
        resolved_overlap = [r for r in resolved_commits if model in {m for m in r["ledger_models"].split(" | ") if m}]
        chat_resolved = [r for r in resolved_commits if r["channel"] == "chat_interface"]
        heuristic_resolved = [r for r in resolved_commits if r["model_resolution_evidence"] == "bounded_gpt_chat_trailer_rule"]
        stat = model_stats.get(model, {})
        coauthor_model_rows.append({
            "model": model,
            "provider": model_provider(model),
            "git_trailer_commits": len(trailer_commits),
            "resolved_provenance_commits": len(resolved_commits),
            "manual_model_override_commits": len(override_commits),
            "exact_ledger_commits": len(ledger_commits),
            "trailer_and_ledger_overlap_commits": len(raw_overlap),
            "resolved_and_ledger_overlap_commits": len(resolved_overlap),
            "trailer_without_same_model_exact_ledger": len(trailer_commits) - len(raw_overlap),
            "ledger_without_same_model_trailer": len(ledger_commits) - len(raw_overlap),
            "confirmed_chat_interface_commits": len(chat_resolved),
            "bounded_gpt_chat_rule_commits": len(heuristic_resolved),
            "measured_output_tokens": int(stat.get("output_tokens", 0)),
            "measured_billable_input_tokens": int(stat.get("input_tokens", 0)) + int(stat.get("cache_write_tokens", 0)) + int(stat.get("cache_read_tokens", 0)),
        })
    write_csv(
        GENERATED / "coauthor_model_summary.csv",
        coauthor_model_rows,
        list(coauthor_model_rows[0].keys()) if coauthor_model_rows else ["model"],
    )

    # Assign exploratory predictions to a model only where the unmeasured commit
    # carries a single declared model (manual override preferred over Git
    # trailer). This makes model-priced extrapolation auditable and leaves
    # unknown/multi-model commits in explicit buckets rather than guessing.
    imputed_by_model = defaultdict(lambda: {
        "commits": 0,
        "predicted_input_tokens": 0.0,
        "predicted_cache_write_tokens": 0.0,
        "predicted_cache_read_tokens": 0.0,
        "predicted_output_tokens": 0.0,
        "predicted_billable_input_tokens": 0.0,
    })
    for r in eligible_rows:
        model = r["imputation_model"]
        stat = imputed_by_model[model]
        stat["commits"] += 1
        for token_name in ("input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens", "billable_input_tokens"):
            stat[f"predicted_{token_name}"] += float(r[f"predicted_{token_name}"])

    imputed_model_rows = []
    for model in sorted(imputed_by_model):
        stat = imputed_by_model[model]
        price = pricing.get(model, {})
        rate_keys = (
            "input_usd_per_million",
            "cache_write_usd_per_million",
            "cache_read_usd_per_million",
            "output_usd_per_million",
        )
        rates = [numeric_rate(price, key) for key in rate_keys]
        complete = model not in {"<unknown>", "<multiple>"} and all(rate is not None for rate in rates)
        cost = None
        if complete:
            cost = sum(
                stat[f"predicted_{kind}"] * rate / 1_000_000
                for kind, rate in zip(("input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens"), rates)
            )
        calibration_exact_ledger_commits = (
            sum(model in {m for m in r["ledger_models"].split(" | ") if m} for r in rows)
            if not model.startswith("<") else 0
        )
        calibration_status = (
            "direct_measured_model" if calibration_exact_ledger_commits > 0
            else "no_direct_measured_model"
        )
        imputed_model_rows.append({
            "model": model,
            "provider": model_provider(model) if not model.startswith("<") else "unresolved",
            "commits": stat["commits"],
            "calibration_exact_ledger_commits": calibration_exact_ledger_commits,
            "calibration_status": calibration_status,
            **{key: round(value, 3) if isinstance(value, float) else value for key, value in stat.items() if key != "commits"},
            "pricing_complete": int(complete),
            "predicted_cost_usd": "" if cost is None else f"{cost:.6f}",
            "pricing_effective_date": price.get("effective_date", ""),
            "pricing_source": price.get("source", ""),
        })
    write_csv(
        GENERATED / "imputed_tokens_by_model.csv",
        imputed_model_rows,
        list(imputed_model_rows[0].keys()) if imputed_model_rows else ["model"],
    )

    # One cost worksheet combines exact measured usage and model-assigned
    # exploratory predictions. Dollar columns remain blank until historically
    # appropriate rates have been entered and sourced in model_pricing.csv.
    measured_by_model = {r["model"]: r for r in model_token_rows}
    imputed_lookup = {r["model"]: r for r in imputed_model_rows}
    cost_summary_rows = []
    for model in sorted((set(measured_by_model) | set(imputed_lookup)) - {"<synthetic>"}):
        measured = measured_by_model.get(model, {})
        imputed = imputed_lookup.get(model, {})
        price = pricing.get(model, {})
        rate_keys = (
            "input_usd_per_million",
            "cache_write_usd_per_million",
            "cache_read_usd_per_million",
            "output_usd_per_million",
        )
        rates = [numeric_rate(price, key) for key in rate_keys]
        complete = model not in {"<unknown>", "<multiple>"} and all(rate is not None for rate in rates)
        measured_cost = None
        imputed_cost = None
        if complete:
            measured_cost = sum(
                float(measured.get(kind, 0)) * rate / 1_000_000
                for kind, rate in zip(("input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens"), rates)
            )
            imputed_cost = sum(
                float(imputed.get(f"predicted_{kind}", 0)) * rate / 1_000_000
                for kind, rate in zip(("input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens"), rates)
            )
        cost_summary_rows.append({
            "model": model,
            "provider": model_provider(model) if not model.startswith("<") else "unresolved",
            "measured_input_tokens": int(measured.get("input_tokens", 0)),
            "measured_cache_write_tokens": int(measured.get("cache_write_tokens", 0)),
            "measured_cache_read_tokens": int(measured.get("cache_read_tokens", 0)),
            "measured_output_tokens": int(measured.get("output_tokens", 0)),
            "imputed_commits": int(imputed.get("commits", 0)),
            "imputation_calibration_exact_ledger_commits": int(imputed.get("calibration_exact_ledger_commits", 0)),
            "imputation_calibration_status": imputed.get("calibration_status", "not_imputed"),
            "imputed_input_tokens": imputed.get("predicted_input_tokens", 0),
            "imputed_cache_write_tokens": imputed.get("predicted_cache_write_tokens", 0),
            "imputed_cache_read_tokens": imputed.get("predicted_cache_read_tokens", 0),
            "imputed_output_tokens": imputed.get("predicted_output_tokens", 0),
            "pricing_complete": int(complete),
            "measured_cost_usd": "" if measured_cost is None else f"{measured_cost:.6f}",
            "imputed_cost_usd": "" if imputed_cost is None else f"{imputed_cost:.6f}",
            "combined_cost_usd": "" if measured_cost is None or imputed_cost is None else f"{measured_cost + imputed_cost:.6f}",
            "pricing_effective_date": price.get("effective_date", ""),
            "pricing_source": price.get("source", ""),
        })
    write_csv(
        GENERATED / "model_cost_summary.csv",
        cost_summary_rows,
        list(cost_summary_rows[0].keys()) if cost_summary_rows else ["model"],
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

    provenance_status_counts = Counter(r["model_provenance_status"] for r in rows)
    confirmed_chat_commits = sum(r["channel"] == "chat_interface" for r in rows)
    bounded_gpt_chat_commits = sum(r["assistance_evidence"] == "bounded_gpt_chat_trailer_rule" for r in rows)
    priced_models = sum(int(r["pricing_complete"]) for r in model_cost_rows if r["model"] != "<synthetic>")
    # Reader-facing dates use the local date recorded in the Git author
    # timestamp.  UTC remains appropriate for interval comparisons and ledger
    # filtering, but converting to UTC can shift an evening commit to tomorrow.
    from datetime import date
    cutoff_date_iso = cutoff_commit.timestamp[:10]
    cutoff_date = date.fromisoformat(cutoff_date_iso)
    cutoff_date_label = f"{cutoff_date.strftime('%B')} {cutoff_date.day}, {cutoff_date.year}"
    inst_author_iso = run_git(ROOT, "show", "-s", "--format=%aI", inst_sha).strip()
    inst_date = date.fromisoformat(inst_author_iso[:10])
    inst_date_label = f"{inst_date.strftime('%B')} {inst_date.day}, {inst_date.year}"
    program_exact_included = {
        sha: m for sha, m in program_exact.items()
        if not (m.get("repository") == PRIMARY_REPOSITORY and sha in excluded_sha)
    }

    summary = {
        "schema": "formalization-draft2/accounting-summary/v3",
        "history_cutoff_commit": CUTOFF,
        "history_cutoff_date": cutoff_date_iso,
        "history_cutoff_date_label": cutoff_date_label,
        "primary_repository": PRIMARY_REPOSITORY,
        "included_ledger_repositories": CONFIG.get("included_ledger_repositories", {}),
        "repository_history_commit_count": len(repository_commits),
        "excluded_paper_only_commits": len(excluded_commits),
        "history_commit_count": len(rows),
        "instrumentation_commit": inst_sha,
        "instrumentation_time_utc": inst_dt.isoformat(),
        "primary_repository_exact_commit_ids": len(exact),
        "ledger_exact_commit_ids": len(program_exact_included),
        "ledger_exact_commits_on_history": sum(sha in commit_by_sha for sha in exact),
        "ledger_exact_commits_off_history": sum(sha not in commit_by_sha for sha in exact),
        "cross_repository_exact_commit_ids": sum(
            m.get("repository") != PRIMARY_REPOSITORY for m in program_exact_included.values()
        ),
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
        "model_provenance_status": dict(provenance_status_counts),
        "model_provenance_disagreement_commits": len(disagreement_rows),
        "chat_interface_review_candidates": len(chat_candidate_rows),
        "confirmed_chat_interface_commits": confirmed_chat_commits,
        "bounded_gpt_chat_rule_commits": bounded_gpt_chat_commits,
        "measured_models": [r["model"] for r in model_token_rows if r["model"] != "<synthetic>"],
        "priced_measured_models": priced_models,
        "model_measured_tokens": {
            r["model"]: {
                "input_tokens": r["input_tokens"],
                "cache_write_tokens": r["cache_write_tokens"],
                "cache_read_tokens": r["cache_read_tokens"],
                "output_tokens": r["output_tokens"],
                "billable_input_tokens": r["billable_input_tokens"],
            }
            for r in model_token_rows
        },
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
            "warning": "Exploratory missing-cost model; missingness is not random, pending session windows are only allocation candidates, and chat-interface provenance is a mix of manual overrides and one explicit time-bounded GPT trailer rule.",
        },
    }
    (GENERATED / "accounting_summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    # Human-readable text report for auditing before any number is quoted.
    report = []
    report.append("# Accounting coverage report")
    report.append("")
    report.append(
        f"Pinned study snapshot: **{cutoff_date_label}** (source commit `{CUTOFF}`; "
        f"{len(rows):,} included primary-repository commits)."
    )
    if excluded_commits:
        report.append(
            f"Excluded from the Git-history study because they touch only blocklisted paper-production paths: **{len(excluded_commits):,}** commits."
        )
    report.append(f"Instrumentation enters history on **{inst_date_label}** (source commit `{inst_sha}`; Git author-date presentation).")
    report.append("")
    report.append("## Study scope")
    report.append("")
    report.append(
        "Commit-level coverage is computed on the primary formalization repository after path-only exclusions. "
        "Measured token totals are program-wide across the explicitly allowlisted ledger repositories."
    )
    for r in repository_stats:
        report.append(
            f"- `{r['repository']}`: **{r['turns']:,}** turns, **{r['output_tokens']:,}** output tokens; {r['scope_label']}"
        )
    report.append("")
    report.append("## Measured lower bound")
    report.append("")
    report.append(f"- ledger model turns: **{measured_all['turns']:,}**")
    report.append(f"- output tokens: **{measured_all['output_tokens']:,}**")
    report.append(f"- billable-input accounting measure: **{measured_all['billable_input_tokens']:,}**")
    report.append(
        f"- exact ledger commit IDs across the in-scope program: **{summary['ledger_exact_commit_ids']:,}**; "
        f"primary-repository exact IDs: **{summary['primary_repository_exact_commit_ids']:,}**; "
        f"on included pinned history: **{summary['ledger_exact_commits_on_history']:,}**"
    )
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
    report.append("## Measured tokens by model")
    report.append("")
    report.append(
        "Ledger schema v3 supplies an exact per-model token vector for every measured row. "
        "This remains exact when a session switched models; model turns are not allocated because the ledger has no by-model turn count."
    )
    for r in model_token_rows:
        if r["model"] == "<synthetic>" and r["output_tokens"] == 0 and r["billable_input_tokens"] == 0:
            continue
        report.append(
            f"- `{r['model']}`: output **{r['output_tokens']:,}**; billable-input measure **{r['billable_input_tokens']:,}** "
            f"({r['ledger_rows']:,} ledger rows)"
        )
    if priced_models == 0:
        report.append(
            "- dollar costs are intentionally not computed yet: `data/model_pricing.csv` has no verified historical rates for measured models"
        )
    report.append("")
    report.append("## Git/ledger model provenance reconciliation")
    report.append("")
    report.append(f"- raw Git/ledger model signals with partial overlap or disjoint labels: **{len(disagreement_rows):,}**")
    report.append(f"- time-bounded GPT-5.6 High/Thinking -> Sol chat-rule commits: **{bounded_gpt_chat_commits:,}**")
    report.append(f"- additional GPT-5.6 Sol chat-interface review candidates: **{len(chat_candidate_rows):,}**")
    report.append(f"- total commits currently classified as chat-interface: **{confirmed_chat_commits:,}**")
    report.append(
        "The GPT High/Thinking rule is an author-confirmed historical convention, applies only to unledgered commits in the configured study interval, and never overrides exact ledger model attribution. "
        "Raw trailer labels remain in the manifest. Other trailer/ledger differences remain review signals rather than errors."
    )
    report.append("")
    report.append("## Provenance warning")
    report.append("")
    report.append(
        "Exact ledger rows establish measured harness model usage. Git co-author trailers are a separate provenance signal and can be stale when a session changes models before committing (notably among Anthropic Opus/Fable sessions). "
        "Outside the explicit bounded GPT chat rule, interface provenance remains unknown unless a manual override or another contemporaneous trace establishes it."
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
    uncalibrated_models = [
        r["model"] for r in imputed_model_rows
        if r["calibration_status"] == "no_direct_measured_model" and not r["model"].startswith("<")
    ]
    if uncalibrated_models:
        report.append(
            "- model-assigned extrapolation has no direct measured calibration for: "
            + ", ".join(f"`{m}`" for m in uncalibrated_models)
        )
    report.append(
        "These model-based values are not part of the measured lower bound and should not be quoted without first auditing the override file, the validation table, model calibration coverage, and the missingness assumptions."
    )
    (GENERATED / "ACCOUNTING_REPORT.md").write_text("\n".join(report) + "\n")

    # LaTeX macros and two small tables used directly by paper.tex.
    def state_n(name: str) -> int:
        return state_counts.get(name, 0)

    macros = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        f"\\newcommand{{\\AccountingCutoffCommitRaw}}{{{CUTOFF}}}",
        f"\\newcommand{{\\AccountingCutoffDate}}{{{cutoff_date_label}}}",
        f"\\newcommand{{\\AccountingSnapshot}}{{\\pdftooltip{{\\AccountingCutoffDate}}{{Git snapshot: {CUTOFF}}}}}",
        f"\\newcommand{{\\InstrumentationDate}}{{{inst_date_label}}}",
        f"\\newcommand{{\\InstrumentationSnapshot}}{{\\pdftooltip{{\\InstrumentationDate}}{{Instrumentation commit: {inst_sha}}}}}",
        f"\\newcommand{{\\RepositoryHistoryCommitCount}}{{{format_int(len(repository_commits))}}}",
        f"\\newcommand{{\\ExcludedPaperOnlyCommitCount}}{{{format_int(len(excluded_commits))}}}",
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
        f"\\newcommand{{\\MeasuredModelCount}}{{{format_int(len([r for r in model_token_rows if r['model'] != '<synthetic>']))}}}",
        f"\\newcommand{{\\ModelProvenanceDisagreementCount}}{{{format_int(len(disagreement_rows))}}}",
        f"\\newcommand{{\\ChatInterfaceCandidateCount}}{{{format_int(len(chat_candidate_rows))}}}",
        f"\\newcommand{{\\ConfirmedChatInterfaceCommitCount}}{{{format_int(confirmed_chat_commits)}}}",
        f"\\newcommand{{\\BoundedGPTChatRuleCommitCount}}{{{format_int(bounded_gpt_chat_commits)}}}",
        f"\\newcommand{{\\LedgerRepositoryCount}}{{{format_int(len(repository_stats))}}}",
        f"\\newcommand{{\\ProgramExactLedgerCommitIdCount}}{{{format_int(summary['ledger_exact_commit_ids'])}}}",
        f"\\newcommand{{\\PrimaryExactLedgerCommitIdCount}}{{{format_int(summary['primary_repository_exact_commit_ids'])}}}",
        f"\\newcommand{{\\CrossRepositoryExactLedgerCommitIdCount}}{{{format_int(summary['cross_repository_exact_commit_ids'])}}}",
        f"\\newcommand{{\\GPTSolTrailerCommitCount}}{{{format_int(next((r['git_trailer_commits'] for r in coauthor_model_rows if r['model'] == 'gpt-5.6-sol'), 0))}}}",
        f"\\newcommand{{\\GPTSolResolvedProvenanceCommitCount}}{{{format_int(next((r['resolved_provenance_commits'] for r in coauthor_model_rows if r['model'] == 'gpt-5.6-sol'), 0))}}}",
        f"\\newcommand{{\\GPTSolExactLedgerCommitCount}}{{{format_int(next((r['exact_ledger_commits'] for r in coauthor_model_rows if r['model'] == 'gpt-5.6-sol'), 0))}}}",
        f"\\newcommand{{\\GPTSolTrailerLedgerOverlapCount}}{{{format_int(next((r['trailer_and_ledger_overlap_commits'] for r in coauthor_model_rows if r['model'] == 'gpt-5.6-sol'), 0))}}}",
    ]
    (SNAPSHOTS / "accounting_macros.tex").write_text("\n".join(macros) + "\n")

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
    (SNAPSHOTS / "measured_token_breakdown_table.tex").write_text("\n".join(token_lines) + "\n")

    model_lines = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        "\\begin{tabular}{lrrrr}",
        "\\toprule",
        "Model & Input & Cache write & Cache read & Output \\\\",
        "\\midrule",
    ]
    for r in model_token_rows:
        total = r["input_tokens"] + r["cache_write_tokens"] + r["cache_read_tokens"] + r["output_tokens"]
        if r["model"] == "<synthetic>" and total == 0:
            continue
        model_lines.append(
            f"{latex_escape(r['model'])} & {r['input_tokens']:,} & {r['cache_write_tokens']:,} & "
            f"{r['cache_read_tokens']:,} & {r['output_tokens']:,} \\\\")
    model_lines += ["\\bottomrule", "\\end{tabular}"]
    (SNAPSHOTS / "model_token_table.tex").write_text("\n".join(model_lines) + "\n")

    repository_lines = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        "\\begin{tabular}{lrrr}",
        "\\toprule",
        "Ledger repository & Turns & Billable-input measure & Output \\\\",
        "\\midrule",
    ]
    for r in repository_stats:
        repository_lines.append(
            f"{latex_escape(r['repository'])} & {r['turns']:,} & {r['billable_input_tokens']:,} & {r['output_tokens']:,} \\\\")
    repository_lines += ["\\bottomrule", "\\end{tabular}"]
    (SNAPSHOTS / "ledger_repository_table.tex").write_text("\n".join(repository_lines) + "\n")

    provenance_lines = [
        "% Generated by scripts/build_accounting.py; do not edit by hand.",
        "\\begin{tabular}{lrrrr}",
        "\\toprule",
        "Model & Raw Git & Resolved & Exact ledger & Chat \\\\",
        "\\midrule",
    ]
    for r in coauthor_model_rows:
        if r["model"] == "<synthetic>":
            continue
        provenance_lines.append(
            f"{latex_escape(r['model'])} & {r['git_trailer_commits']:,} & {r['resolved_provenance_commits']:,} & "
            f"{r['exact_ledger_commits']:,} & {r['confirmed_chat_interface_commits']:,} \\\\")
    provenance_lines += ["\\bottomrule", "\\end{tabular}"]
    (SNAPSHOTS / "model_provenance_table.tex").write_text("\n".join(provenance_lines) + "\n")

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
    (SNAPSHOTS / "accounting_state_table.tex").write_text("\n".join(table_lines) + "\n")

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
    (SNAPSHOTS / "component_accounting_table.tex").write_text("\n".join(component_lines) + "\n")

    print(f"accounting: {len(rows)} commits, {state_n('exact_measured')} exact measured, {len(pending_rows)} pending segments")
    print(f"accounting: working data under {GENERATED.relative_to(ROOT)}; TeX snapshots under {SNAPSHOTS.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
