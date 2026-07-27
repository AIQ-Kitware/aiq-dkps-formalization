Inspect the latest commit in `/home/joncrall/code/aiq-dkps-namek` and compile the
three-module shared ideal scratch chain:

```bash
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex \
    DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
```

`TwoWayFactorization` was already reported green. The latest commit repairs
API resolution and proof orientation in the other two modules. Fix any
remaining elaboration errors narrowly in those two files. Do not redesign the
statements, move declarations into production, or modify unrelated files. Do
not use `sorry`, `admit`, `native_decide`, or new axioms.

After all three targets compile, run:

```bash
scripts/lake_build_report.py \
    DavisKahan.Experimental.Scratch.SharedFoundations.All
```

Report exactly which targets compiled and any remaining diagnostics.
