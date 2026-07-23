# Davis--Kahan 1970 full-paper frontier

This directory is an intentionally incomplete signature layer for the
remaining full-paper formalization. It is outside `DavisKahan.All` and does not
change the supported build.

The frontier has three purposes:

1. every remaining paper endpoint should have a declaration;
2. every hard internal bridge should appear as its own declaration rather than
   being hidden in prose or an unconstrained certificate;
3. the manifest and checker should report whether each declaration resolves,
   whether its proof closure contains an admission, and whether every declared
   dependency recursively reaches a grounded foundation.

The intended repair order is:

1. make `DavisKahan.Experimental.Frontier.All` elaborate;
2. complete `Lemma63.lean`;
3. complete the constructive Section 3 crossed-defect and operator-level
   classification results;
4. implement the circle-specific Riesz projection bridge;
5. discharge the Section 8 common-circle and direct-rotation bridges;
6. construct the free-beam closed operator and spectral estimate;
7. replace the conditional Section 9 certificates by constructors derived from
   the analytic model;
8. promote completed declarations into stable modules and update the source
   census.

`Section4.lean` deliberately omits the published Proposition 4.4. The stable
library contains a machine-checked counterexample and a repaired restricted or
Q-norm theory.

Run:

```bash
python3 scripts/check_davis_kahan_frontier.py
python3 scripts/check_davis_kahan_frontier.py --json
python3 scripts/check_davis_kahan_frontier.py --check
python3 scripts/check_davis_kahan_frontier.py --write-report
```

Without a Lean toolchain the checker performs manifest and textual coverage
checks. With `lake` available it additionally resolves every declaration and
runs a transitive axiom audit, distinguishing a stated theorem from a theorem
whose entire proof closure is admission-free.
