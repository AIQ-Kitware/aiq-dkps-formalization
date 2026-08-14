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
COAUTHOR_RE = re.compile(r"^Co-authored-by:\s*(.*?)\s*<([^>]+)>\s*$", re.I | re.M)


def repo_root(start: pathlib.Path) -> pathlib.Path:
    out = subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], cwd=start, text=True
    ).strip()
    return pathlib.Path(out)


def run_git(root: pathlib.Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=root, text=True, errors="replace")


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
        return COAUTHOR_RE.findall(self.body)

    @property
    def llm_coauthors(self) -> list[str]:
        return [name.strip() for name, _ in self.coauthors if LLM_NAME_RE.search(name)]


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


def load_ledger(root: pathlib.Path) -> tuple[dict[str, dict], list[dict], list[dict]]:
    """Return exact-commit aggregates, pending summary rows, and all token rows."""
    ledger = root / ".llm_resource_tally/ledger/ledger.jsonl"
    exact: dict[str, dict] = {}
    pending: list[dict] = []
    token_rows: list[dict] = []
    with ledger.open(encoding="utf-8") as file:
        for row_index, line in enumerate(file, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if "t" not in row:
                continue
            token_rows.append(row)
            commit = row.get("c") or ""
            values = list(row.get("t") or [0, 0, 0, 0])
            if len(values) != 4:
                continue
            if commit.startswith("pending@"):
                copy = dict(row)
                copy["ledger_row"] = row_index
                pending.append(copy)
                continue
            if not commit:
                continue
            agg = exact.setdefault(
                commit,
                {
                    "ledger_rows": 0,
                    "turns": 0,
                    "input_tokens": 0,
                    "cache_write_tokens": 0,
                    "cache_read_tokens": 0,
                    "output_tokens": 0,
                    "agents": set(),
                    "models": set(),
                },
            )
            agg["ledger_rows"] += 1
            agg["turns"] += int(row.get("n") or 0)
            for name, value in zip(TOKEN_NAMES, values):
                agg[name] += int(value or 0)
            if row.get("a"):
                agg["agents"].add(str(row["a"]))
            for model in row.get("m") or []:
                agg["models"].add(str(model))
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
