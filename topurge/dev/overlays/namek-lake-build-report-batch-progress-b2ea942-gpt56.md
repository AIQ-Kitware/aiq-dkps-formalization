# Namek Lake build report: batch progress and global deduplication

Base inspected: `b2ea942eabea`

Target worktree for this session:

```text
/home/joncrall/code/aiq-dkps-namek
```

## Purpose

Improve `scripts/lake_build_report.py` for compiler campaigns spanning several
Lean modules.

## Behavior

With multiple targets, the reporter now builds one target per Lake invocation by
default. Lake's build cache is shared, so successful dependencies are not rebuilt
from scratch. The script writes concise progress to stderr:

```text
[1/3] BUILD Target.One
[1/3] PASS  Target.One (0.42s, warnings=110)
[2/3] BUILD Target.Two
[2/3] FAIL  Target.Two (1.07s, errors=6)
```

After all targets have been attempted, it emits one report that:

- merges diagnostics from every invocation;
- deduplicates exact repeated diagnostics globally;
- records which targets encountered each repeated diagnostic;
- continues after failures by default;
- preserves a nonzero exit status if any target failed.

Use `--fail-fast` to stop on the first failure. Use `--single-invocation` to ask
Lake to build all targets together when parallelism is more important than
per-target progress. Progress goes to stderr, so JSON stdout remains valid.

## Example

```bash
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```

## Verification

```bash
python3 -m py_compile scripts/lake_build_report.py
python3 scripts/tests/test_lake_build_report.py
```
