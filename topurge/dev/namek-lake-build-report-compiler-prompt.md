Work only in `/home/joncrall/code/aiq-dkps-namek`.

Inspect the latest commit, then validate the newly added build-report utility:

```bash
python3 -m py_compile scripts/lake_build_report.py
python3 scripts/tests/test_lake_build_report.py
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization
```

The script must preserve the real `lake build` exit code. Its default report
should contain actual Lean errors but omit warnings, info/trace diagnostics,
Lake progress, `Lean exited with code ...`, target-failure lists, `build failed`,
and exact duplicate diagnostic blocks. Do not weaken the parser by hiding an
unrecognized failure: a nonzero build with no parsed error must print a raw
failure tail.

If the installed Lake version rejects the command layout, inspect `lake --help`
and preserve global flags before the `build` subcommand. Keep the script free of
third-party Python dependencies.
