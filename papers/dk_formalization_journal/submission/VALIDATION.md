# Validation record: 23 October 2026

## Source baseline

Manuscript update prepared from the user-provided archive
`aiq-dkps-formalization-source-2026-10-23T113048-5-6d76992edd79.tar.gz`.
The original 29 source-level targets remain 28 proved at source scope and one
formally refuted as printed (Davis--Kahan Proposition 4.4). No Lean source,
compiler pin, result inventory, or theorem statement is changed in the present
manuscript overlay.

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

## Conventional but not Lean-formalized extensions

`sharp_displacement_unformalized.tex` proves, in ordinary mathematical prose:

1. The universal projection-distance lower bound for admissible maps.
2. The `sec(alpha/2)` multiplicative comparison for direct rotations, sharp
   for the real four-dimensional trace-norm family.
3. Global trace-norm optimality of the existing real competitor.
4. The exact complex trace-norm optimum using principal-angle planes.

These proofs are **not** part of the verified Lean development. They appear
only inside a red, breakable `tcolorbox` and are controlled by the switch
`\includeUnformalizedDisplacementtrue` / `false` in `paper.tex`.

Prior to describing those statements as formalized, prove their analogues
using the existing finite-dimensional UI-seminorm and majorization APIs and
run their targeted Lean builds. The suggested dependency order is the
projection lower bound, principal-angle singular values of `I - R`, universal
comparison, equality for the existing `SmallAngleCounterexample`, then the
complex blockwise optimum and realification bridge. Review the resulting
mathematical statements against Bolotnikov--Li--Rodman (2001) and related
minimization literature before claiming novelty.

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
