# Current mathematical and manuscript scope: 25 October 2026, `427169ce`

The reviewed source snapshot contains the completed finite-dimensional complex
Schatten `1<p<2` **full optimizer classification**, including every angle
multiplicity and right-angle defect, the algebraic normalized/multiplicity
parameter equivalences, exact `2^s` counts under the stated hypotheses, and
the constrained local-to-global theorem. It also contains the all-global-
minimizer Charbonnier classification. The main paper already contains their
mathematical statements and proof outlines in `schatten_transport_verified.tex`
and `smoothed_transport_verified.tex`; this revision promotes them to the
abstract, contributions, related work and conclusion, adds a small optimizer-
family example, and revises the Manim novelty tour accordingly. No Lean sources
or 29-result inventory rows are edited by this documentation overlay.

The user-reported prior aggregate Lean build for the classification is accepted
as verification. This revision's pdfLaTeX/BibTeX builds produced a 54-page
checked manuscript and a 55-page working manuscript, with no unresolved
references or overfull equations. All 24 focused Manim deck, LaTeX-markup,
numeric-model and layout tests passed. These are typesetting/source tests,
not Lean recompilation or an end-to-end graphical Manim render. The
arbitrary-rank real matching,
operator-ideal/infinite-dimensional result, and Grassmannian topological
structure remain separate proof obligations. Mathematical priority is not
established by missing matches in a literature search.

---

# Current manuscript integration: 24 October 2026, `521572a2`

The user-provided incremental git-well source patch was applied to the
verified base `642de34df29a` to reconstruct snapshot `521572a2`.
That snapshot contains compiled unrestricted higher-rank **complex**
Schatten `1<p<2` global optimality and the all-rank canonical cutoff in
`SchattenGlobalLowerBound`, `SchattenGlobalAttainment` and
`SchattenCanonicalOptimality`. The checked journal manuscript now inputs
`schatten_transport_verified.tex`, rather than treating that section as a
working conjecture. These are mathematical extensions, outside the
original 29 Davis--Kahan target inventory.

For a focused local build (not a request for a new routine axiom audit):

```bash
lake exe cache get
lake build \
  DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalLowerBound \
  DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment \
  DavisKahan.FiniteDimensional.DirectRotation.SchattenCanonicalOptimality
```

Manuscript builds are typesetting checks, not re-verification of Lean.
The exact complex theorem covers arbitrary ambient mixing, all physical
principal angles and `1<p<2`. At the earlier `521572a2` revision, classification
of all minimizers was not yet claimed; the 25 October update at the top of this
file supersedes that boundary. Unrestricted real matching and
infinite-dimensional Schatten-ideal optimization remain outside the checked scope.

---

# Validation record: 23 October 2026

## Current all-pairs complex theorem (source snapshot `b00c5c8c35e1`)

The later source archive includes the unconditional Lean theorem
`exists_global_complex_trace_minimizer` in
`DavisKahan/FiniteDimensional/DirectRotation/ComplexPhaseTrace.lean` and its
explicit principal-angle specialization
`exists_global_complex_trace_minimizer_with_principalAngles` in
`ComplexTracePrincipalAngles.lean`. The former proves attainment and global
optimality for **arbitrary equal-rank finite-dimensional complex subspaces**;
it requires neither acuteness nor a supplied CS coordinate equivalence.
`ComplexCrossedDefects.lean` supplies equal-dimensional right-angle crossed
defects. `ForTauCeti/.../Projection/TraceSine.lean` proves the positive
projector-difference modulus decomposition and the full Ky Fan trace identity
in finite-dimensional **real or complex** spaces, without equal ranks.
`DirectRotation/All.lean` imports all these modules. These theorems are
included in the author's updated formalization. This manuscript-only edit
changes no Lean modules; the historical user-confirmed builds remain
established. None of these extension theorems changes the original 29 source
results (28 proved, Proposition 4.4 refuted).

The `paper.tex` checked variant now includes the full complex optimum and
its trace decomposition, with the only optional red-framed working theorem
being the **real** line/hyperplane transport formula.

For targeted local verification, in this order:

```bash
lake exe cache get
lake build \
  ForTauCeti.Analysis.InnerProductSpace.Projection.TraceSine \
  DavisKahan.FiniteDimensional.DirectRotation.ComplexCrossedDefects \
  DavisKahan.FiniteDimensional.DirectRotation.ComplexPhaseTrace \
  DavisKahan.FiniteDimensional.DirectRotation.ComplexTracePrincipalAngles
```

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

**Historical boundary of this earlier build set.** The finite-model
modules listed above did not themselves prove the unconditional complex
all-pairs result. That gap has now been **closed by different modules**:
`ComplexCrossedDefects.lean`, `ComplexPhaseTrace.lean`, `TraceSine.lean`,
and `ComplexTracePrincipalAngles.lean`, as recorded at the top of this file.
The formal proof uses a paired-phase/nonacute-completion argument and does not
require the previously proposed Halmos/CS coordinate-existence theorem.
The `sqrt(2)` limiting-necessity endpoint remains recorded separately in
`SharpDisplacementLimit.lean`.

`paper.tex` includes `sharp_displacement.tex` unconditionally. The former
`sharp_displacement_verified.tex` and `sharp_displacement_unformalized.tex`
are retained older records and are not inputs to either build. The sole
unformalized theorem in the working manuscript is the **real**
line/hyperplane transport formula.

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

The main manuscript includes `sharp_displacement.tex`. With the newer
`b00c5c8` theorem development, the provisional complex flag has been
removed, and `paper_working.tex` enables only
`\includeUnformalizedRealTransport`. The historical text in this validation
record documents earlier checkpoints but does not set the current scope.

`../PAPER_CONTEXT.md` is the entry point for Davis--Kahan publication claim
boundaries. The separate YWS record is now under
`../../yws_formalization_conference/YWS_VERSION_RECORD.md`.
