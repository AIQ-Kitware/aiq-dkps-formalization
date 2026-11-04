#!/usr/bin/env python3
"""Record native independent search runs for *human* comparison.

This is deliberately not a merged theorem index, result normalizer, or a
proof/audit checker. It preserves each tool's raw JSON and failure information.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
WORK = Path(os.environ.get("THEOREM_EXPLORATION_WORK_ROOT", str(HERE / ".build")))
BACKENDS = ("loogle", "leanexplore", "leansearch")


def parse_args():
    parser = argparse.ArgumentParser(description="Collect raw results from local theorem-search tools")
    parser.add_argument("--backend", action="append", choices=BACKENDS, help="Repeat to run several; defaults to all")
    parser.add_argument("--case", action="append", help="Case id to run (repeatable); defaults to all")
    parser.add_argument("--limit", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=240, help="Seconds per tool per query")
    parser.add_argument("--queries", type=Path, default=HERE / "queries.json")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def command(backend: str, case: dict, limit: int):
    semantic = case["semantic_query"]
    if backend == "loogle":
        return [str(HERE / "run-loogle.sh"), "--json", "--max-results", str(limit),
                "--module", case["loogle_module"], case["loogle_query"]]
    if backend == "leanexplore":
        return [str(HERE / "run-leanexplore.sh"), "--json", "--limit", str(limit), semantic]
    if backend == "leansearch":
        return [str(HERE / "run-leansearch.sh"), "--json", "--limit", str(limit), semantic]
    raise ValueError(backend)


def run_one(backend: str, case: dict, limit: int, timeout: int) -> dict:
    argv = command(backend, case, limit)
    started = time.perf_counter()
    try:
        proc = subprocess.run(argv, capture_output=True, text=True, timeout=timeout, check=False)
        stdout, stderr, returncode = proc.stdout, proc.stderr, proc.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = (exc.stdout or b"")
        stderr = (exc.stderr or b"")
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
        stderr += f"\nTimed out after {timeout}s"
        returncode = 124
    duration = round(time.perf_counter() - started, 3)
    try:
        native = json.loads(stdout)
        parse_error = None
    except json.JSONDecodeError as exc:
        native = None
        parse_error = str(exc)
    return {
        "backend": backend,
        "case_id": case["id"],
        "command": argv,
        "query": case["loogle_query"] if backend == "loogle" else case["semantic_query"],
        "success": returncode == 0 and parse_error is None,
        "exit_code": returncode,
        "wall_seconds": duration,
        "native_json": native,
        "parse_error": parse_error,
        "stdout_if_not_json": stdout if parse_error else None,
        "stderr": stderr,
    }


def main():
    args = parse_args()
    if args.limit <= 0 or args.timeout <= 0:
        raise SystemExit("--limit and --timeout must be positive")
    spec = json.loads(args.queries.read_text())
    cases = spec["cases"]
    known = {case["id"] for case in cases}
    missing = set(args.case or []) - known
    if missing:
        raise SystemExit(f"Unknown case id(s): {', '.join(sorted(missing))}")
    if args.case:
        cases = [case for case in cases if case["id"] in args.case]
    backends = tuple(dict.fromkeys(args.backend or BACKENDS))
    now = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    output = args.output or WORK / "results" / f"evaluation-{now}.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    revision_files = {
        "loogle": WORK / "loogle/upstream-revision.txt",
        "leansearch": WORK / "leansearch/upstream-revision.txt",
    }
    revisions = {
        key: path.read_text().strip() if path.exists() else None
        for key, path in revision_files.items()
    }
    results = []
    for case in cases:
        for backend in backends:
            print(f"{case['id']}: {backend}", flush=True)
            result = run_one(backend, case, args.limit, args.timeout)
            results.append(result)
            print(f"  exit={result['exit_code']}, seconds={result['wall_seconds']}, "
                  f"valid_json={result['parse_error'] is None}", flush=True)
    active_version_path = WORK / "leanexplore/home/.lean_explore/active_version"
    revisions["leanexplore_data"] = (
        active_version_path.read_text().strip() if active_version_path.exists() else None
    )
    report = {
        "generated_at_utc": now,
        "lean_toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
        "native_results_only": True,
        "revisions": revisions,
        "query_file": str(args.queries),
        "results": results,
    }
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"Saved native results: {output}")
    failed = sum(not row["success"] for row in results)
    if failed:
        print(f"{failed} invocation(s) failed; see stderr in the report.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
