# Lane claims

Coordination ledger for parallel agents working this repo. Purpose: avoid the
duplicated-effort collisions that occurred on the Sylvester analytic lane
(2026-07-23), where two agents independently proved the same five theorems.

**Identity note (2026-07-23):** agents are identified by their *human*, not by
the model running them (models change mid-session). Rows previously labeled
`opus` were jon's agent; rows labeled `fable` were edward's agent. Edward's
agent stopped after the circle-Riesz definitional layer; jon's agent (also
running Fable 5) inherited and completed that lane. Edward's agent has since
RESUMED (2026-07-23) and claims lanes under `edward (resumed)` below.

## Rules

- **Claim before the first edit.** Add/refresh your row below, commit it, then work.
- A claim covers the **listed declarations**, not the whole file. Two agents may
  work different declarations in one file if both are listed.
- **Release explicitly** when done (set status `done` or remove the row).
- **Unlisted = unclaimed.** If you want something not listed, add a row first.
- If two claims would overlap, the earlier-committed row wins; the other agent
  picks something else.

## Format

`agent | file(s) | declarations | date | status`

## Claims

| agent | file(s) | declarations | date | status |
|-------|---------|-------------|------|--------|
| edward (stopped) | Sylvester/{FourierSemigroup,OrderedSemigroup,CompactIntegral,FiniteBlockReconstruction}.lean | whole Sylvester analytic lane (sorry-free) | 2026-07-23 | done |
| edward (stopped) | Sylvester/Basic.lean | norm_sylvester_le_of_orderedSeparation, compact_mem_of_separatedSylvester_solution | 2026-07-23 | done |
| edward (stopped) | InfiniteDimensional/GraphSubspace.lean | acuteAngularOperator, acuteAngularOperator_spec, acute_iff_exists_bounded_angularOperator | 2026-07-23 | done |
| jon | MathAhead/HiddenFoundations/PolarIsometryFinal.lean | polarIsometry_comp_adjoint_self | 2026-07-23 | done |
| jon | MathAhead/HiddenFoundations/{Section3Nonacute,PolarIsometryFinal}.lean | remaining 5 polar leaves | 2026-07-23 | blocked (missing infra) |
| jon | SinTheta/RCLikeSpectralBridge.lean (new), SinTheta/SpectralBridge.lean (Experimental) | phantom machinery + estimate repair — SpectralBridge now COMPILES | 2026-07-23 | done (3 RCLike leaf sorries) |
| jon | SinTheta/General.lean, DoubleAngle.lean, DirectRotation.lean | Continuation-chain repair: all three elaborate (documented leaf obligations); ContinuationCore → ContinuationSpectralIdentification builds green | 2026-07-23 | done |
| jon | SinTheta/RestrictionCompat.lean | restrictedSpectrum_top_eq_realSpectrum_general, boundedRealSpectrum_eq_realSpectrum, mem_realResolventSet_ofBounded_iff | 2026-07-23 | done |
| jon | Frontier/Core.lean, Frontier/RieszCircle.lean | circle Riesz lane: all 9 obligations closed (RieszCircle sorry-free, incl. the projection identity via the new contour-free SinTheta/CayleySelectorBridge.lean); signatures 4 and 5 gained the necessary `0 ≤ radius` | 2026-07-23 | done |
| edward (resumed) | Frontier/Section8.lean (ContinuationBridge section), Frontier/CircleContour.lean (new) | spectralContinuationWitness_of_circle, spectralContinuationWitness_of_circle_endpoints, selectedBranchProjectionLipschitzConstant_of_circle + the circle instantiation of PiecewiseC1ClosedContour/SpectralSeparatingContour | 2026-07-23 | done — all three proved sorry-free after jon's Continuation-chain repair unblocked SpectralContinuationWitness. Statement repairs along the way: Section8.lean had never elaborated (Complex.abs, missing Inv instance, wrong IsSymmetric.smul, phantom sourceSelectedProjection fields, subtype inner-product coercions in the compression sections — all fixed, sorried bodies of the unclaimed sections untouched); Sources/Section8/Smallness.lean had a dangling docstring parse error (now `/-!`). CircleContinuationData was restated over operatorPath with Ring.inverse; endpoints theorem restated via starProjection of the selected subspaces. Section8.lean now compiles; its remaining 9 sorries are the unclaimed DirectRotationCompression/SourceTheorems sections. |

## Spectral lane — COMPLETE through the Continuation chain (jon, 2026-07-23)

`SinTheta/General.lean`, `DoubleAngle.lean`, and `DirectRotation.lean` all
elaborate; the full chain `General → DoubleAngle → ContinuationCore →
ContinuationTransport → ContinuationAssembly →
ContinuationSpectralIdentification` builds green (8893 jobs), and the default
build stays green (9097 jobs). The remaining mathematical content is isolated
as documented **leaf obligations** inside those three files: the two RCLike
Sylvester engine transports, the measurable `spectralSubspace` triple,
`operatorAbsoluteValue` + ideal-gauge identity + ideal projector-difference
estimate (General); the reflected-subspace transports and double-angle
identities (DoubleAngle); the polar units/commutation and the two
Halmos-decomposition extremal theorems (DirectRotation). Signature note:
`sinTheta_perturbation`/`sinTheta_symmetric`/`spectralProjection_sinTheta`/
`ideal_sinTheta`/`sinTwoTheta_residual` gained necessary `left ≤ right` /
instance hypotheses.

## Parked (claim explicitly before starting)

- `Ideals/Rectangular.lean` (4): Schatten / Hilbert–Schmidt / trace-class rectangular
  families over RCLike — multi-session analytic campaign; Schauder absent from pinned Mathlib.
- Frontier Contour-blocked sections (Section3/8/9): **UNBLOCKED 2026-07-23** —
  the circle contour surface is complete (RieszCircle.lean sorry-free; the
  projection identity is proved through SinTheta/CayleySelectorBridge.lean).
  Consumers should target the RieszCircle signatures; note theorems 4/5 now
  take `0 ≤ radius` (supplied by `CircleSeparatesRealSpectrum.radius_pos`).
- `MathAhead/.../KyFanBochner.lean`: broken on `main` since de30805 (11 errors, pre-existing).
- Polar-decomposition campaign (5 leaves): `adjoint_polarIsometry` needs the abs-adjoint
  closure relation `closure_range_abs_adjoint_eq_closure_range` + partial-adjoint formula;
  Section3Nonacute needs `positiveSupportInverse` + `source_compression_polar_formula` +
  `canonicalPolarFactor_reflection_relation` + the crossed-block structure of
  `IsPaperDirectRotation`. None exist in Mathlib/Spectra/repo yet — a real multi-session
  campaign. `polarIsometry_comp_adjoint_self` (final-projection identity) was the one leaf
  whose supporting infra was already present; now proved (5c7b13c).
