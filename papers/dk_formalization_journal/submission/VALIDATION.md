# Validation record: 23 October 2026

## Source baseline

This record retains the user-confirmed build evidence from the earlier
23 October 2026 revision and incorporates the later repository snapshot
`aiq-dkps-formalization-source-2026-10-23T123759-5-3f24ae49b431.tar.gz`
(commit `3f24ae49b431`). The original 29 source-level targets remain 28
proved at source scope and one formally refuted as printed (Proposition 4.4).
Neither the compiler pin nor the source-result inventory was changed.
A new, uncompiled Lean candidate in `TraceOptimality.lean` is excluded from
all verification counts.

## Completed parameterized strengthening

The user provided the output of the pinned Lean build on 23 October 2026:

```bash
lake exe cache get
lake build \
  DavisKahan.FiniteDimensional.DirectRotation.SmallAngleCounterexample \
  DavisKahan.Sources.DavisKahan1970.Section4SmallAngle \
  DavisKahan.Sources.DavisKahan1970.Audits.SmallAngleCounterexample
```

The command completed successfully (3,477 jobs). The audit output identified
`TauCeti.DavisKahan1970.proposition4_4_parameterized_traceNorm_counterexample`,
`proposition4_4_parameterized_principalAngles`, and
`proposition4_4_arbitrarilySmall_refutingPair`. For the inspected declarations,
axiom dependencies were exactly the standard `propext`, `Classical.choice`, and
`Quot.sound`. Four cosmetic `linter.unnecessarySeqFocus` warnings appeared in
`SmallAngleCounterexample.lean`, none blocking compilation. The proof is
reported as verified, not pending, based on that observed user build.

The source-facing aliases are an *additional extension*, not a thirtieth
historical result in the original paper's fixed inventory. The full default
build was not rerun for this manuscript-only change.

## Additional displacement results and current verification boundary

The 23 October 2026 user-confirmed compilation also covers:

- `DavisKahan.FiniteDimensional.DirectRotation.ProjectionDisplacement`, proving
  `projectionDifference_uiNorm_le_displacement` and its Ky Fan formulation;
- `DavisKahan.FiniteDimensional.DirectRotation.TraceRatio`, proving
  `SmallAngleCounterexample.cos_half_mul_directTrace_eq_competitorTrace`.

These are established results; the additional working draft does not supersede
or downgrade them.

`sharp_displacement_unformalized.tex` contains conventional proofs of the
remaining global claims: the universal `sec(alpha/2)` multiplier, the exact
real trace-norm minimum, and the no-acuteness complex trace-norm minimum.
Those three claims are still outside the confirmed Lean development. The
working-draft frame remains red and can be omitted with the
`\includeUnformalizedDisplacementfalse` switch.

The candidate `DavisKahan/FiniteDimensional/DirectRotation/TraceOptimality.lean`
contains source-level implementations for the real trace formula and attained
minimum. This execution environment did not have `lake`, `lean`, or the pinned
Mathlib/TauCeti dependencies, and its network could not resolve GitHub to
install them. Its new declarations have not been compiled, are not imported
by `DirectRotation/All.lean`, and are **not** counted as verified. No new Lean build was possible. A
single-pass TeX syntax check (`pdflatex -draftmode -interaction=nonstopmode
-halt-on-error -file-line-error paper.tex`) succeeded in this environment,
with the expected first-pass unresolved references and citations; it is not a
full bibliography or PDF-publishing build.

## Citation limits

The 1970 Example 4.2 exhibits complex phase improvement in trace norm;
Bolotnikov--Li--Rodman (2001) treats Q-norm minima and Schatten counterexamples;
Qiu--Zhang--Li (2005) repeats the short-angle assertion; Zhang--Qiu (2010)
states general trace-norm nonminimality. The reviewed material does not
establish first-publication priority for the exact real small-angle correction
or the sharp ratio. The new draft does not claim such priority.

## Reproduction

```bash
python3 papers/dk_formalization_journal/scripts/small_angle_symbolic.py
make -C papers/dk_formalization_journal paper
```

On a minimal TeX installation without `bibtex`, use `bibtex8` through a PATH
shim or via `latexmk -e '$bibtex = "bibtex8 %O %B";' -pdf paper.tex` from the
manuscript directory.
