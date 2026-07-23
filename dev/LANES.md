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
| jon | SinTheta/RCLikeSpectralBridge.lean (new), SinTheta/SpectralBridge.lean (Experimental) | phantom machinery + estimate repair; ALL RCLike leaves now closed (pencil invertibility at non-real parameters proved directly, inverse spectral mapping via spectrum.map_inv, false normal-norm leaf removed) — both files sorry-free | 2026-07-23 | done |
| jon | SinTheta/General.lean, DoubleAngle.lean, DirectRotation.lean | Continuation-chain repair: all three elaborate (documented leaf obligations); ContinuationCore → ContinuationSpectralIdentification builds green | 2026-07-23 | done |
| jon | SinTheta/RestrictionCompat.lean | restrictedSpectrum_top_eq_realSpectrum_general, boundedRealSpectrum_eq_realSpectrum, mem_realResolventSet_ofBounded_iff | 2026-07-23 | done |
| jon | Frontier/Core.lean, Frontier/RieszCircle.lean | circle Riesz lane: all 9 obligations closed (RieszCircle sorry-free, incl. the projection identity via the new contour-free SinTheta/CayleySelectorBridge.lean); signatures 4 and 5 gained the necessary `0 ≤ radius` | 2026-07-23 | done |
| edward (resumed) | Frontier/Section8.lean (DirectRotationCompression + SourceTheorems sections — ALL 9 remaining sorries) | directRotationUpper/LowerCompressionData, theorem8_1_upper/lowerCompressionRepulsion_of_directRotation, Theorem81SourceConclusion (restatement), theorem8_1_selectedBranch_and_spectralRepulsion, perturbation/residualHalfGapBridge_of_sourceHypotheses, theorem8_2_perturbation/residualHalfGap_selectedBranch. NOTE: current statements are false as stated (placeholder `id id` blocks force `2‖x‖²=‖x‖²`; 8.1 compression reduces to a sign condition on E; 8.2 bridges lack the quantitative contour link). Honest restatement: the paper's 8.1(i) cosine-block inequality at quadratic-form level needs only the orthogonal target splitting (cross terms vanish since the target branch reduces A+E) + the SpectralOrder.Complex restriction-spectrum form-bound bridges — no direct rotation. 8.2 gains the explicit `radius·‖E‖/margin² < √2/2` hypothesis. | 2026-07-23 | done — Section8.lean is now SORRY-FREE. All 9 restated declarations proved axiom-clean: target-splitting compression certificates (`upper/lowerCompressionRepulsionData_of_targetSplitting`, kernel-side form shifted by the cut so its global bound is the branch form bound), the faithful 8.1(i) compression inequalities, `Theorem81SourceConclusion` (compression fields restated to compare the perturbed form on the old branch with its cosine-block compression into the new branch), the 8.1 assembly, and both 8.2 alternatives via the half-gap bridges with the quantitative circle hypothesis. New helpers: `re_inner_le_of_spectrumIn_Iic`/`le_re_inner_of_spectrumIn_Ici` (SpectrumIn → quadratic-form bound via SpectralOrder.Complex bridges) and `re_inner_splitting_of_invariant` (cross terms vanish through a reducing subspace). Open analytic step recorded in docstrings: constructing the quantitative circle datum from the printed half-gap hypotheses (Krein replacement for the residual case). |
| edward (resumed) | Frontier/Core.lean, Frontier/Section3.lean | genericHalmosCosineSq, genericHalmosSineSq, genericHalmosCosineSq_add_sineSq (Core), crossed_intersections_are_halmos_defects (Section3) — Halmos generic-angle operators via compression to the generic summand | 2026-07-23 | done — all four proved sorry-free, axiom-clean. Defs = compressOperator of the full-space halmosCosineSq/SineSq (the generic part reduces both projections, so compression is the honest restriction); Pythagoras from the full-space resolution of the identity + linearity of compression; crossed intersections are definitional (`⟨rfl, rfl⟩`). Unblocks the Section3 classification statements that consume genericHalmosCosineSq. |
| jon | DoubleAngle.lean | reflection-transport leaf closure: reflectedSubspace_orthogonal (new) + reflectedSubspace_hasOrthogonalProjection + reduces_reflectedSubspace PROVED (self-adjoint involution: (J''U)ᗮ = J''(Uᗮ); conjugated projection is an idempotent with reflected range). DoubleAngle 8→6 leaves; chain + Section8 stay green | 2026-07-23 | done |
| edward (resumed) | Frontier/Section8.lean (ContinuationBridge section), Frontier/CircleContour.lean (new) | spectralContinuationWitness_of_circle, spectralContinuationWitness_of_circle_endpoints, selectedBranchProjectionLipschitzConstant_of_circle + the circle instantiation of PiecewiseC1ClosedContour/SpectralSeparatingContour | 2026-07-23 | done — all three proved sorry-free after jon's Continuation-chain repair unblocked SpectralContinuationWitness. Statement repairs along the way: Section8.lean had never elaborated (Complex.abs, missing Inv instance, wrong IsSymmetric.smul, phantom sourceSelectedProjection fields, subtype inner-product coercions in the compression sections — all fixed, sorried bodies of the unclaimed sections untouched); Sources/Section8/Smallness.lean had a dangling docstring parse error (now `/-!`). CircleContinuationData was restated over operatorPath with Ring.inverse; endpoints theorem restated via starProjection of the selected subspaces. Section8.lean now compiles; its remaining 9 sorries are the unclaimed DirectRotationCompression/SourceTheorems sections. |
| jon | Frontier/Lemma63.lean, MathAhead/Lemma63.lean, AGENTS.md | Section 6 Lemma 6.3 promotion: correct the overstrong block hypothesis to the source-faithful `K∘P = Q∘K∘P`, lift the MathAhead proof up to close both Frontier sorries (approximation-number + finite singular-value forms), slim MathAhead to a re-export shim; codify the scratch→promotion workflow in AGENTS.md | 2026-07-23 | done — both Frontier theorems proved axiom-clean (no sorryAx), 2 sorries removed; the previous `K∘P = Q∘K` signature trivialized leakage (`Q∘K∘(1−P)=0` outright). Machinery ported: prefix-square-energy left-compression bound, paper HS energy domain split (basis-free Pythagoras), rank bounds, opNorm-via-zeroth-approx (needs 0<n), finite singular-value bridge. GeometryAll + Frontier.All green (8899 jobs); default build unaffected (Experimental-only). |
| jon | DoubleAngle.lean | finiteGap_mixedIntervalExterior, internalGap_reflection_transport, sinAngle_reflected_eq_sinTwoAngle, doubleAngle_directedGap_identity + supporting lemmas (restricted-spectrum invariance under reflection conjugation, starProjection of reflectedSubspace, cross-block identity, reflection norm invariance) | 2026-07-23 | done — all four proved axiom-clean. Consequences: sinTwoTheta_reflectionDefect and sinTwoTheta_perturbation are now FULLY PROVED (no sorryAx). DoubleAngle 6→2 leaves (sinAngle_reflected_mem_gauge_eq blocks ideal_sinTwoTheta; reflectionDefect_range_le_residual blocks sinTwoTheta_residual). sinTwoTheta_generalSeparation waits only on General.lean's norm_sylvester_le_of_generalSeparation_rclike. Key steps: units-transfer conjugation for restricted spectra via codRestrict intertwiners; P_{JU} = J P J via eq_starProjection_of_mem_orthogonal; cross-block identity P_{Uᗮ} J P_U = sinTwoAngleOperator; norm_starProjection_sub_eq_max collapses the symmetric gap. |

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

## Scratch overlay (external GPT-5.6 drop) — repaired by jon (2026-07-23)

The never-compiled `DavisKahan/Experimental/Scratch/` drop (ideal Banach
spaces, Hilbert–Schmidt Bochner layer incl. the `HilbertSchmidtComplexFamily`
dependency, free-beam Green identities and smooth kernel) now builds:
`lake build DavisKahan.Experimental.Scratch.All` — zero errors, zero sorries.
Key API decision: `IdealOperator.ofMem` must be used instead of anonymous
constructors in statements (the type-synonym unfolding otherwise leaks the
subtype topology into `Integrable` hypotheses), and the generic Bochner
theorems take `[NormedSpace ℝ (E →L[𝕜] F)]` as an instance argument.
