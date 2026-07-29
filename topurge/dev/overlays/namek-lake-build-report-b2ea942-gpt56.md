# Namek Lake build report utility

Base inspected: `b2ea942eabea`

Target worktree for this session:

```text
/home/joncrall/code/aiq-dkps-namek
```

## Purpose

Add a standard-library-only wrapper around `lake -q build` that emits compact,
deduplicated Lean diagnostics for humans and compiler agents.

## Files

- `scripts/lake_build_report.py`
- `scripts/tests/test_lake_build_report.py`

## Default behavior

- invokes Lake in quiet mode;
- reports errors only;
- removes Lake progress and repeated final failure wrappers;
- collapses exact repeated diagnostics;
- groups nearby errors and prints one source-context window per group;
- preserves the underlying build exit status;
- falls back to a raw failure tail when output cannot be parsed.

Warnings, informational diagnostics, traces, JSON output, and full raw logs are
available through explicit flags.

## Verification

```bash
python3 -m py_compile scripts/lake_build_report.py
python3 scripts/tests/test_lake_build_report.py
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization
```
