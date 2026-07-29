# Compiler-agent prompt: verify batch build reporter

Work only in:

```text
/home/joncrall/code/aiq-dkps-namek
```

Inspect the latest commit, then verify the updated build reporter:

```bash
cd /home/joncrall/code/aiq-dkps-namek
python3 -m py_compile scripts/lake_build_report.py
python3 scripts/tests/test_lake_build_report.py

scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```

Expected operational behavior:

- one concise BUILD/PASS/FAIL progress pair per target on stderr;
- all targets attempted unless `--fail-fast` is supplied;
- one final globally deduplicated diagnostic report;
- repeated dependency failures annotated with all targets that encountered them;
- nonzero final exit status if any target failed.

Repair only defects in the reporting utility or its tests. Do not repair the Lean
modules as part of this utility verification unless separately instructed.
