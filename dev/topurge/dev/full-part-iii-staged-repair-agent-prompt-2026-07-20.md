# Agent prompt: staged compiler-gated full Part III repair

Read `dev/full-part-iii-staged-repair-plan-2026-07-20.md` completely.

The previous static checker gave a false sense of completion.  The default
`check_full_part_iii_math_ahead.py` now invokes Lean and may report CLEAN only
when the restored modules compile.  `--static-only` protects signatures but is
not proof certification.

Your first action is to negative-test the corrected contract:

1. run `python3 scripts/check_full_part_iii_math_ahead.py --static-only` and
   confirm it says `STATIC CLEAN` and explicitly says Lean was not checked;
2. run `python3 scripts/check_full_part_iii_math_ahead.py` and confirm it exits
   nonzero on the current uncompiled batch;
3. use command exit status, never grepped error-line shapes.

Proceed with Stage 1 only.  Build the missing finite-dimensional self-adjoint
functional calculus and Moore--Penrose inverse as general reusable mathematics,
then compile the first five finite modules.  You are explicitly authorized to
create those APIs because no canonical pinned Mathlib/Spectra equivalent exists
and they are independently useful.

Do not use this authorization to recreate APIs that already exist:

- rewrite `RCLikeUnboundedSpectralTheorem.*` onto production Spectra bridges;
- rewrite placeholder Hilbert--Schmidt/Schatten uses onto production operator
  ideals where possible;
- use the completed continuation stack instead of `Contour.Rectifiable`;
- use current Riccati structures instead of inventing a parallel equation type.

After every target repair run the checker with `--module PATH`.  Preserve every
guarded signature.  If a statement is false, stop with a counterexample; do not
weaken it.

Stage 1 targets, sequentially:

```text
ForMathlib finite-dimensional self-adjoint functional calculus module
ForMathlib finite-dimensional Moore--Penrose inverse module
DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean
DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean
DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean
```

When Stage 1 is green, report the exact API added, every theorem compiled, all
remaining blockers, and a dependency-ordered proposal for the next finite batch.
Do not begin the closed-form/KLMN layer without a paper-correspondence decision.
