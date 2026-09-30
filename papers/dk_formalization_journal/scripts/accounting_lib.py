#!/usr/bin/env python3
"""Shared accounting utilities for the formalization_draft2 paper.

The code is deliberately stdlib-only so the accounting snapshot can be rebuilt
without adding a Python dependency stack to the Lean repository.
"""

from __future__ import annotations

import csv
import json
import math
import pathlib
import re
import statistics
import subprocess
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from typing import Iterable, Sequence

TOKEN_NAMES = ("input_tokens", "cache_write_tokens", "cache_read_tokens", "output_tokens")
LLM_NAME_RE = re.compile(r"(?:claude|opus|fable|gpt|openai|codex)", re.I)
COAUTHOR_LINE_RE = re.compile(r"^Co[- ]?Authored[- ]By:\s*(.*?)\s*$", re.I | re.M)
EMAIL_TRAILER_RE = re.compile(r"^(.*?)\s*(?:<([^>]+)>|([^\s<>]+@[^\s<>]+))\s*$")


def parse_coauthors(body: str) -> list[tuple[str, str]]:
    """Parse common Git co-author trailer variants.

    Historical commits contain both canonical ``Name <email>`` trailers and a
    few manually entered ``Name email`` variants.  Treat both as provenance
    evidence rather than silently dropping the latter.
    """
    out: list[tuple[str, str]] = []
    for match in COAUTHOR_LINE_RE.finditer(body):
        payload = match.group(1).strip()
        em = EMAIL_TRAILER_RE.match(payload)
        if em:
            name = em.group(1).strip()
            email = (em.group(2) or em.group(3) or "").strip()
        else:
            name, email = payload, ""
        if name:
            out.append((name, email))
    return out


def canonical_model_name(name: str) -> str:
    """Normalize ledger/model-trailer spellings to a comparison key."""
    raw = name.strip()
    low = raw.lower().replace("_", "-")
    low = re.sub(r"\s+", " ", low)
    if low == "<synthetic>" or "synthetic" in low:
        return "<synthetic>"
    if "claude" in low and "opus" in low and re.search(r"(?:4[ .-]?8|4\.8)", low):
        return "claude-opus-4-8"
    if "claude" in low and "opus" in low and re.search(r"(?:^|\D)5(?:\D|$)", low):
        return "claude-opus-5"
    if "claude" in low and "fable" in low and re.search(r"(?:^|\D)5(?:\D|$)", low):
        return "claude-fable-5"
    if ("gpt" in low or "openai" in low or "codex" in low) and "5.6" in low and "sol" in low:
        return "gpt-5.6-sol"
    if ("gpt" in low or "openai" in low or "codex" in low) and "5.6" in low and "terra" in low:
        return "gpt-5.6-terra"
    if ("gpt" in low or "openai" in low or "codex" in low) and "5.6" in low and "thinking" in low:
        return "gpt-5.6-thinking"
    if ("gpt" in low or "openai" in low or "codex" in low) and "5.6" in low and "high" in low:
        return "gpt-5.6-high"
    if "openai gpt-5.6" in low:
        return "gpt-5.6"
    slug = re.sub(r"[^a-z0-9.<>]+", "-", low).strip("-")
    return slug or raw


def model_provider(model: str) -> str:
    model = canonical_model_name(model)
    if model.startswith("claude-"):
        return "Anthropic"
    if model.startswith("gpt-") or model.startswith("openai-") or model.startswith("codex-"):
        return "OpenAI"
    if model == "<synthetic>":
        return "synthetic"
    return "unknown"


def repo_root(start: pathlib.Path) -> pathlib.Path:
    out = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "--show-toplevel"], cwd=start, text=True
    ).strip()
    return pathlib.Path(out)


def run_git(root: pathlib.Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={root}", *args], cwd=root, text=True, errors="replace"
    )


def parse_dt(value: str | None) -> datetime | None:
    if not value:
        return None
    value = value.replace("Z", "+00:00")
    dt = datetime.fromisoformat(value)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def format_int(value: int | float) -> str:
    return f"{int(round(value)):,}"


def latex_escape(text: str) -> str:
    repl = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(repl.get(ch, ch) for ch in text)


def write_csv(path: pathlib.Path, rows: Iterable[dict], fieldnames: Sequence[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def quantile(values: Sequence[float], q: float) -> float:
    if not values:
        return float("nan")
    xs = sorted(values)
    if len(xs) == 1:
        return xs[0]
    pos = (len(xs) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return xs[lo]
    frac = pos - lo
    return xs[lo] * (1.0 - frac) + xs[hi] * frac


@dataclass
class Commit:
    commit: str
    timestamp: str
    timestamp_dt: datetime
    author_name: str
    author_email: str
    subject: str
    body: str
    files: list[str]
    additions: int
    deletions: int
    binary_files: int
    lean_additions: int
    lean_deletions: int

    @property
    def coauthors(self) -> list[tuple[str, str]]:
        return parse_coauthors(self.body)

    @property
    def llm_coauthors(self) -> list[str]:
        return [name.strip() for name, _ in self.coauthors if LLM_NAME_RE.search(name)]

    @property
    def llm_coauthor_models(self) -> list[str]:
        return sorted({canonical_model_name(name) for name in self.llm_coauthors})


def load_commits(root: pathlib.Path, cutoff: str) -> list[Commit]:
    """Read commit metadata and numstat for the history ending at ``cutoff``."""
    fmt = "%x1e%H%x1f%aI%x1f%an%x1f%ae%x1f%s%x1f%B%x1d"
    raw = run_git(root, "log", cutoff, "--reverse", "--numstat", f"--format={fmt}")
    commits: list[Commit] = []
    for record in raw.split("\x1e"):
        if not record.strip() or "\x1d" not in record:
            continue
        header, numstats = record.split("\x1d", 1)
        parts = header.split("\x1f", 5)
        if len(parts) != 6:
            continue
        commit, ts, author, email, subject, body = [p.strip() for p in parts]
        files: list[str] = []
        additions = deletions = binary_files = lean_additions = lean_deletions = 0
        for line in numstats.splitlines():
            bits = line.split("\t")
            if len(bits) < 3:
                continue
            a, d, path = bits[0], bits[1], bits[2]
            files.append(path)
            if a == "-" or d == "-":
                binary_files += 1
                continue
            try:
                ai, di = int(a), int(d)
            except ValueError:
                continue
            additions += ai
            deletions += di
            if path.endswith(".lean"):
                lean_additions += ai
                lean_deletions += di
        dt = parse_dt(ts)
        assert dt is not None
        commits.append(
            Commit(
                commit=commit,
                timestamp=ts,
                timestamp_dt=dt,
                author_name=author,
                author_email=email,
                subject=subject,
                body=body,
                files=files,
                additions=additions,
                deletions=deletions,
                binary_files=binary_files,
                lean_additions=lean_additions,
                lean_deletions=lean_deletions,
            )
        )
    return commits


def instrumentation_commit(root: pathlib.Path, cutoff: str) -> tuple[str, datetime]:
    raw = run_git(
        root,
        "log",
        cutoff,
        "--reverse",
        "--format=%H%x1f%aI",
        "--",
        ".llm_resource_tally",
    ).splitlines()
    if not raw:
        raise RuntimeError("no .llm_resource_tally commit found")
    commit, ts = raw[0].split("\x1f", 1)
    dt = parse_dt(ts)
    assert dt is not None
    return commit, dt


def ledger_row_identity(row: dict) -> tuple:
    """Return the llm_resource_tally v3 latest-wins row identity.

    Repository/worktree basename is deliberately not part of the identity; the
    tally tool itself treats ``r`` as descriptive provenance, not a stable
    repository identifier.
    """
    agent = row.get("a") or row.get("agent") or "unknown"
    session = row.get("sid") or row.get("session_id")
    if row.get("k") == "cx" or row.get("kind") == "compaction-estimate":
        return ("compaction", agent, session, row.get("bt") or row.get("boundary_ts"))
    commit = row.get("c") or row.get("commit") or ""
    if isinstance(commit, str) and commit.startswith("pending@"):
        span = row.get("tr") or row.get("turn_ts_range") or [None, None]
        end = span[1] if len(span) > 1 else None
        return ("measured", agent, session, commit, end)
    return ("measured", agent, session, commit)


def load_canonical_ledger_rows(
    root: pathlib.Path, repositories: Sequence[str] | None = None
) -> list[dict]:
    """Read published ledger shards using the tally's latest-wins semantics.

    The current retained ledger is intentionally used even when the Git-history
    cutoff is historical: a later publication or backfill may improve our best
    measurement of earlier work.  The caller scopes rows by the time of the
    observed activity, not by ``recorded_at``.
    """
    ledger_dir = root / ".llm_resource_tally/ledger"
    shards = sorted(ledger_dir.glob("ledger*.jsonl"))
    if not shards:
        raise FileNotFoundError(f"no published tally ledger shards under {ledger_dir}")

    order: list[tuple] = []
    best: dict[tuple, dict] = {}
    for shard in shards:
        with shard.open(encoding="utf-8") as file:
            for row_index, line in enumerate(file, 1):
                if not line.strip():
                    continue
                row = json.loads(line)
                copy = dict(row)
                copy["ledger_row"] = f"{shard.name}:{row_index}"
                copy["repository"] = str(row.get("r") or row.get("repo") or "")
                key = ledger_row_identity(row)
                if key not in best:
                    order.append(key)
                current = best.get(key)
                current_rec = parse_dt(current.get("rec") or current.get("recorded_at")) if current else None
                candidate_rec = parse_dt(row.get("rec") or row.get("recorded_at"))
                if current is None or current_rec is None or (candidate_rec is not None and candidate_rec >= current_rec):
                    best[key] = copy

    rows = [best[key] for key in order]
    repo_filter = set(repositories or [])
    if repo_filter:
        rows = [r for r in rows if r.get("repository", "") in repo_filter]
    return rows


def row_is_pending(row: dict) -> bool:
    commit = str(row.get("c") or row.get("commit") or "")
    return commit.startswith("pending@")


def row_is_backfill(row: dict) -> bool:
    activity = str(row.get("act") or row.get("activity") or "").strip().lower()
    return activity == "backfill"


def row_observed_at(row: dict) -> datetime | None:
    """Best timestamp for deciding whether observed work precedes a study cutoff."""
    if row.get("k") == "cx" or row.get("kind") == "compaction-estimate":
        return parse_dt(row.get("bt") or row.get("boundary_ts"))
    if row_is_pending(row):
        span = row.get("tr") or row.get("turn_ts_range") or [None, None]
        end = span[1] if len(span) > 1 else None
        start = span[0] if len(span) > 0 else None
        return parse_dt(end) or parse_dt(start) or parse_dt(row.get("rec") or row.get("recorded_at"))
    return parse_dt(row.get("ct") or row.get("commit_ts")) or parse_dt(row.get("rec") or row.get("recorded_at"))


def aggregate_exact_token_rows(rows: Sequence[dict]) -> dict[str, dict]:
    """Aggregate token-bearing, non-pending rows by commit SHA."""
    exact: dict[str, dict] = {}
    for row in rows:
        if "t" not in row and "tokens" not in row:
            continue
        commit = str(row.get("c") or row.get("commit") or "")
        if not commit or commit.startswith("pending@"):
            continue
        if "t" in row:
            values = [int(v or 0) for v in list(row.get("t") or [0, 0, 0, 0])]
            by_model = row.get("bm") or {}
            turns = int(row.get("n") or 0)
            agent = row.get("a")
            models = row.get("m") or []
        else:
            tok = row.get("tokens") or {}
            values = [int(tok.get(k) or 0) for k in ("input", "cache_write", "cache_read", "output")]
            by_model = row.get("by_model") or {}
            turns = int(row.get("turns") or 0)
            agent = row.get("agent")
            models = row.get("models") or []
        if len(values) != 4:
            continue
        model_sum = [0, 0, 0, 0]
        for raw_model, model_values in by_model.items():
            if isinstance(model_values, dict):
                vals = [int(model_values.get(k) or 0) for k in ("input", "cache_write", "cache_read", "output")]
            else:
                vals = [int(v or 0) for v in model_values]
            if len(vals) != 4:
                raise ValueError(f"bad per-model token vector for {raw_model!r}")
            for i, value in enumerate(vals):
                model_sum[i] += value
        if by_model and model_sum != values:
            raise ValueError(
                f"per-model tokens {model_sum} do not sum to row total {values} for {commit}"
            )
        agg = exact.setdefault(
            commit,
            {
                "repositories": set(),
                "ledger_rows": 0,
                "turns": 0,
                "input_tokens": 0,
                "cache_write_tokens": 0,
                "cache_read_tokens": 0,
                "output_tokens": 0,
                "agents": set(),
                "models": set(),
                "activities": set(),
                "model_tokens": {},
            },
        )
        agg["repositories"].add(str(row.get("repository") or row.get("r") or ""))
        agg["ledger_rows"] += 1
        agg["turns"] += turns
        for name, value in zip(TOKEN_NAMES, values):
            agg[name] += value
        if agent:
            agg["agents"].add(str(agent))
        activity = row.get("act") or row.get("activity")
        if activity:
            agg["activities"].add(str(activity))
        for model in models:
            agg["models"].add(canonical_model_name(str(model)))
        for raw_model, model_values in by_model.items():
            model = canonical_model_name(str(raw_model))
            dest = agg["model_tokens"].setdefault(model, [0, 0, 0, 0])
            if isinstance(model_values, dict):
                vals = [int(model_values.get(k) or 0) for k in ("input", "cache_write", "cache_read", "output")]
            else:
                vals = [int(v or 0) for v in model_values]
            for i, value in enumerate(vals):
                dest[i] += value
    return exact


def load_ledger(
    root: pathlib.Path,
    repositories: Sequence[str] | None = None,
    observed_before: datetime | None = None,
) -> tuple[dict[str, dict], list[dict], list[dict]]:
    """Return canonical exact aggregates, pending rows, and token rows.

    ``observed_before`` is applied to the activity timestamp (commit timestamp
    for attributed rows; turn-range end for pending rows), not ``recorded_at``.
    Thus later publication/backfill can improve an earlier adjustable snapshot.
    """
    rows = load_canonical_ledger_rows(root, repositories)
    if observed_before is not None:
        cutoff = observed_before.astimezone(timezone.utc)
        rows = [r for r in rows if row_observed_at(r) is None or row_observed_at(r) <= cutoff]
    token_rows = [r for r in rows if "t" in r or "tokens" in r]
    pending = [r for r in token_rows if row_is_pending(r)]
    exact = aggregate_exact_token_rows(token_rows)
    return exact, pending, token_rows

def pending_windows(pending: Sequence[dict], pad_minutes: float = 0.0) -> list[dict]:
    windows = []
    pad = timedelta(minutes=pad_minutes)
    for idx, row in enumerate(pending, 1):
        span = row.get("tr") or [None, None]
        start = parse_dt(span[0] if len(span) > 0 else None)
        end = parse_dt(span[1] if len(span) > 1 else None)
        if start is None:
            continue
        if end is None:
            end = start
        if end < start:
            start, end = end, start
        windows.append(
            {
                "segment_id": f"pending-{idx:04d}",
                "start": start,
                "end": end,
                "match_start": start - pad,
                "match_end": end + pad,
                "row": row,
            }
        )
    return windows


def matching_pending_windows(dt: datetime, windows: Sequence[dict]) -> list[dict]:
    return [w for w in windows if w["match_start"] <= dt <= w["match_end"]]


def load_overrides(path: pathlib.Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    out: dict[str, dict] = {}
    with path.open(newline="", encoding="utf-8") as file:
        for row in csv.DictReader(file):
            commit = (row.get("commit") or "").strip()
            if commit:
                out[commit] = {k: (v or "").strip() for k, v in row.items()}
    return out


def component_flags(files: Sequence[str], patterns: dict[str, list[str]]) -> dict[str, int]:
    flags = {}
    for name, prefixes in patterns.items():
        flags[name] = int(any(any(path.startswith(p) or path == p for p in prefixes) for path in files))
    return flags


def subject_flags(subject: str) -> dict[str, int]:
    lower = subject.lower()
    groups = {
        "subject_docs": ("doc", "paper", "readme", "prose"),
        "subject_plan": ("plan", "roadmap", "audit", "survey"),
        "subject_proof": ("prove", "proof", "theorem", "lemma", "corollary", "formaliz"),
        "subject_fix": ("fix", "repair", "correct", "counterexample"),
        "subject_chore": ("chore", "sync", "bump", "cleanup", "refactor"),
        "subject_test": ("test", "ci", "build"),
    }
    return {name: int(any(token in lower for token in tokens)) for name, tokens in groups.items()}


def model_feature_names(component_names: Sequence[str]) -> list[str]:
    return [
        "log1p_additions",
        "log1p_deletions",
        "log1p_files_changed",
        "log1p_lean_changes",
        "lean_file_share",
        "llm_trailer",
        "claude_trailer",
        "openai_trailer",
        "agent_author",
        "model_claude_opus_5",
        "model_claude_opus_4_8",
        "model_claude_fable_5",
        "model_gpt_5_6_sol",
        "model_gpt_5_6_terra",
        "model_gpt_other",
        "model_multiple",
        "subject_docs",
        "subject_plan",
        "subject_proof",
        "subject_fix",
        "subject_chore",
        "subject_test",
        *[f"component_{name}" for name in component_names],
    ]


def feature_vector(row: dict, component_names: Sequence[str]) -> list[float]:
    files = max(int(row["files_changed"]), 1)
    lean_files = int(row["lean_files_changed"])
    ledger_models = {m for m in str(row.get("ledger_models") or "").split(" | ") if m}
    declared_models = {m for m in str(row.get("declared_models") or "").split(" | ") if m}
    models = ledger_models or declared_models
    vals = [
        math.log1p(int(row["additions"])),
        math.log1p(int(row["deletions"])),
        math.log1p(int(row["files_changed"])),
        math.log1p(int(row["lean_additions"]) + int(row["lean_deletions"])),
        lean_files / files,
        float(int(row["llm_trailer"])),
        float(int(row["claude_trailer"])),
        float(int(row["openai_trailer"])),
        float(int(row["agent_author"])),
        float("claude-opus-5" in models),
        float("claude-opus-4-8" in models),
        float("claude-fable-5" in models),
        float("gpt-5.6-sol" in models),
        float("gpt-5.6-terra" in models),
        float(any(m.startswith("gpt-") and m not in {"gpt-5.6-sol", "gpt-5.6-terra"} for m in models)),
        float(len(models) > 1),
        *[float(int(row[k])) for k in ("subject_docs", "subject_plan", "subject_proof", "subject_fix", "subject_chore", "subject_test")],
        *[float(int(row[f"component_{name}"])) for name in component_names],
    ]
    return vals


class RidgeLogModel:
    """Small ridge regression on log1p(target), implemented without numpy."""

    def __init__(self, alpha: float = 5.0):
        self.alpha = alpha
        self.means: list[float] = []
        self.scales: list[float] = []
        self.beta: list[float] = []

    @staticmethod
    def _solve(a: list[list[float]], b: list[float]) -> list[float]:
        n = len(b)
        aug = [row[:] + [b[i]] for i, row in enumerate(a)]
        for col in range(n):
            pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
            if abs(aug[pivot][col]) < 1e-12:
                aug[pivot][col] = 1e-12
            aug[col], aug[pivot] = aug[pivot], aug[col]
            div = aug[col][col]
            aug[col] = [v / div for v in aug[col]]
            for row in range(n):
                if row == col:
                    continue
                factor = aug[row][col]
                if factor == 0:
                    continue
                aug[row] = [x - factor * y for x, y in zip(aug[row], aug[col])]
        return [aug[i][-1] for i in range(n)]

    def fit(self, xs: Sequence[Sequence[float]], ys: Sequence[float]) -> "RidgeLogModel":
        if not xs:
            raise ValueError("cannot fit empty model")
        p = len(xs[0])
        self.means = [statistics.fmean(x[j] for x in xs) for j in range(p)]
        self.scales = []
        for j in range(p):
            sd = statistics.pstdev(x[j] for x in xs)
            self.scales.append(sd if sd > 1e-9 else 1.0)
        design = [[1.0] + [(x[j] - self.means[j]) / self.scales[j] for j in range(p)] for x in xs]
        q = p + 1
        xtx = [[0.0] * q for _ in range(q)]
        xty = [0.0] * q
        logs = [math.log1p(max(0.0, float(y))) for y in ys]
        for xrow, y in zip(design, logs):
            for i in range(q):
                xty[i] += xrow[i] * y
                for j in range(q):
                    xtx[i][j] += xrow[i] * xrow[j]
        for j in range(1, q):
            xtx[j][j] += self.alpha
        self.beta = self._solve(xtx, xty)
        return self

    def predict_one(self, x: Sequence[float]) -> float:
        z = [1.0] + [(x[j] - self.means[j]) / self.scales[j] for j in range(len(x))]
        lp = sum(b * v for b, v in zip(self.beta, z))
        return max(0.0, math.expm1(lp))


def rolling_origin_splits(n: int, folds: int) -> list[tuple[range, range]]:
    """Train on earlier observations and test on successive tail blocks."""
    if n < 20:
        return []
    folds = max(1, min(folds, 5))
    start = n // 2
    remaining = n - start
    block = max(1, remaining // folds)
    splits = []
    for i in range(folds):
        test_start = start + i * block
        test_end = n if i == folds - 1 else min(n, test_start + block)
        if test_start <= 5 or test_start >= test_end:
            continue
        splits.append((range(0, test_start), range(test_start, test_end)))
    return splits
