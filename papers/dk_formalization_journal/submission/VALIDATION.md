# Validation record: 23 October 2026

## Source baseline

This record retains the user-confirmed build evidence from the earlier
23 October 2026 revision and incorporates the later repository snapshot
`aiq-dkps-formalization-source-2026-10-23T123759-5-3f24ae49b431.tar.gz`
(commit `3f24ae49b431`). The original 29 source-level targets remain 28
proved at source scope and one formally refuted as printed (Proposition 4.4).
Neither the compiler pin nor the source-result inventory was changed.
Subsequent 23 October 2026 user-confirmed focused builds established the
additional sharp real/universal theorems and the complex finite-plane model.
These are separate mathematical extensions, not additional source-result rows.

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

## Additional sharp-displacement results: confirmed compilation

The user's sequential focused Lean builds on 23 October 2026 confirmed
successful compilation of the following added result modules and repairs:

- `DavisKahan.FiniteDimensional.DirectRotation.ProjectionDisplacement`,
  universal projector-distance lower bound for every UI seminorm, without
  acuteness;
- `DavisKahan.FiniteDimensional.DirectRotation.TraceRatio`, exact real trace
  ratio;
- `DavisKahan.FiniteDimensional.DirectRotation.TraceOptimality`, real
  projector-distance trace formula and attained global minimum;
- `DavisKahan.FiniteDimensional.DirectRotation.SharpDisplacement`, universal
  real/complex acute-pair estimate for all UI seminorms, the sharp
  fixed-angle factor, the optimal `2 / sqrt(3)` constant under the original
  angle range, and the uniform `sqrt(2)` bound;
- `DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceOptimality`, the
  exact complex planar phase-minimizer through the right-angle endpoint;
- `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockTrace`,
  full-trace additivity on orthogonal blocks;
- `DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceAssembly`, ambient
  planar extension and two-plane assembly; and
- `DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceFiniteModel`, exact
  trace minimization for an arbitrary positive finite number of complex
  principal planes, fixed orthogonal summands, and transport under an
  explicitly supplied ambient unitary equivalence.

**Remaining verification boundary.** The unconditional complex theorem for
*every* equal-dimensional subspace pair is not a theorem in these modules.
It requires construction of the finite Halmos/CS principal-plane equivalence,
including matched right-angle defect subspaces. A conventional proof appears
in the red-framed `sharp_displacement_unformalized.tex`. The mathematical
limit proof that `sqrt(2)` is the least uniform acute-pair constant is included
in `sharp_displacement_verified.tex`; `SharpDisplacementLimit.lean` now adds a
focused declaration for it, outside the previously confirmed build set.

`paper.tex` unconditionally includes `sharp_displacement_verified.tex` and
conditionally includes only the remaining complex global extension via
`\includeUnformalizedDisplacementtrue`; switch this off for a manuscript
containing exclusively fully verified statements. Aggregate imports of the
verified modules and the new limiting corollary are maintained in
`DirectRotation/All.lean`; the aggregate itself requires a fresh build.

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

## Later manuscript switch and source-edition update (23 October 2026)

The main manuscript now includes `sharp_displacement.tex`; `paper_working.tex`
enables **two** independent provisional flags,
`\includeUnformalizedComplexTrace` and `\includeUnformalizedRealTransport`.
This supersedes the obsolete switch name in the older reproducibility text
above. The verified-only version leaves both false. No new Lean proof was
claimed or built by this manuscript edit.

`../PAPER_CONTEXT.md` is the entry point for Davis--Kahan publication claim
boundaries. The separate YWS record is now under
`../../yws_formalization_conference/YWS_VERSION_RECORD.md`.
