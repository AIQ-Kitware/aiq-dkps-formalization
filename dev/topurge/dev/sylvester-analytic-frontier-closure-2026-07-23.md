# Sylvester analytic frontier closure — 2026-07-23 (Fable)

Branch: `fable/sylvester-upstream-leaves` (three commits, each build-green and
axiom-clean at `propext, Classical.choice, Quot.sound` on every headline).
Work ran in parallel with the concurrent `SinTheta/General` +
`RestrictionCompat` import-cycle repair and deliberately touched none of that
agent's files (`SinTheta/General`, `SinTheta/RestrictionCompat`,
`SpectralTheory/AbstractSpectrum`, `DoubleAngle` imports) and none of the
Compatibility-layer signatures.

## Closed

### `Sylvester/OrderedSemigroup.lean` — sorry-free (was 10 open obligations)

The constant-one Laplace branch is complete:
`orderedSylvester_reconstruction` (exact reconstruction
`X = ∫_{t≥0} e^{-tA} C e^{tB} dt` under an ordered gap) now rests on

- `restrictedSpectrum_top_eq_realSpectrum` — via the new top-restriction
  spectrum bridge (below);
- `exists_common_cut_of_orderedSeparation` — sSup/sInf cut, using
  `realSpectrum_isCompact`; no nonemptiness hypothesis needed (empty spectra
  handled by case split);
- `semigroup_eq_cfc` — `exp(tT) = cfc (fun z => exp (t z)) T` via
  `cfc_comp_const_mul` + `CFC.complex_exp_eq_normedSpace_exp`.
  Pitfall: prove `IsSelfAdjoint ((t:ℂ) • T)` by
  `rw [isSelfAdjoint_iff, star_smul, …]`; the term-mode `IsSelfAdjoint.smul`
  route sends instance search into a whnf timeout on operator spaces.
  `set_option maxHeartbeats 800000` on the two CFC-facing proofs;
- `norm_semigroup_le_of_spectrum_subset_Iic` / `…_neg_le_of_…_Ici` —
  `norm_cfc_le` + `IsSelfAdjoint.mem_spectrum_eq_re` + `spectrum.neg_eq`.
  Pitfall: keep `-r` as `Neg.neg` (a hidden `Real.neg` from coercion
  normalization defeats `linarith`);
- `orderedSylvester_integrableOn` (new) / `orderedSylvester_integrable` —
  majorized by `exp (-d t) ‖C‖` via `exp_neg_integrableOn_Ioi`. Pitfall: the
  `Integrable (indicator …)` ↔ `IntegrableOn` lemmas live at the
  `ESeminormedAddMonoid.toContinuousENorm` instance path while elaborated
  statements carry `SeminormedAddGroup.toContinuousENorm`; bridge with a
  `have h2 : @IntegrableOn _ _ _ _ ESeminormedAddMonoid.toContinuousENorm … := h`
  coercion (concrete-to-concrete defeq is accepted; metavariable-headed
  unification is not);
- `hasDerivAt_ordered_solution_orbit` — product rule for
  `s ↦ e^{-sA} X e^{sB}`. The Mathlib `HasDerivAt.clm_comp` is unusable here
  (it requires the CLMs to be over the differentiation field ℝ, ours are ℂ);
  route: `isBoundedBilinearMap_comp.hasFDerivAt`, `.restrictScalars ℝ`,
  `.comp_hasDerivAt` against `HasDerivAt.prodMk`, then a pointwise `ext` with
  `B_commute_expBounded`. State the intermediate `HasDerivAt` with the exact
  `restrictScalars`/`deriv` value and finish by `hval ▸ hfd'` — `convert`
  splits instance implicits and drowns;
- `ordered_orbit_sub_eq_integral` — FTC via
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`;
- `tendsto_ordered_solution_orbit_zero` — `squeeze_zero_norm'` (its majorant
  binder is named `a`, not `g`; supply it through the eventually hypothesis);
- final assembly via `intervalIntegral_tendsto_integral_Ioi` +
  `tendsto_nhds_unique`.

### `Sylvester/FourierSemigroup.lean` — sorry-free (was 6 open obligations)

- New `SpectrumBridge` section: `topInclusion`, `topConjAlgEquiv`
  (conjugation by the top-submodule identification as a `ℂ`-algebra
  equivalence; all structure fields close by `ext x; rfl` through structure
  eta), `spectrum_restrict_top` (via `AlgEquiv.spectrum_eq`),
  `restrictedSpectrum_top_eq`, `realSpectrum_isCompact`
  (`Complex.isometry_ofReal.isClosedEmbedding.isProperMap.isCompact_preimage`).
- `exists_finiteSpectralStep` — `finite_cover_balls_of_compact` (centers in
  the spectrum), then `disjointed` directly over `Fin n` (current Mathlib's
  `disjointed` is index-generic: `disjointed_le`, `disjoint_disjointed`,
  `iUnion_disjointed`, `disjointed_apply` all work on `Fin n`; no ℕ-padding
  dance needed). Cell measurability via `disjointed_apply` +
  `Finset.measurableSet_biUnion`.
- `finiteSpectralStep_representatives_separated` — membership transported
  with `(spectrum_restrict_top …).symm.subset`; note `rw` cannot see through
  the `restrictedSpectrum` abbrev/def layers, so work with `Eq.subset` on the
  underlying `spectrum` equality.
- `FiniteSpectralStep.operator_isSelfAdjoint`, `norm_operator_le` (new).
- `continuous_semigroup`, `continuous_unitaryGroup` (in `t`),
  `continuous_unitaryGroup_generator` (in the generator, via
  `NormedSpace.exp_analytic (𝕂 := ℂ)`; the ℚ-algebra `exp_continuous` is not
  applicable to operator algebras).
- `tendsto_unitary_orbit` — composition of the generator-continuity with
  `isBoundedBilinearMap_comp.continuous` and `Tendsto.prodMk_nhds`.
- `tendsto_separated_integral` (new) — the dominated-convergence workhorse:
  bound `‖μ_d t‖ · M`, contraction bound through
  `norm_unitaryGroup_le_one`, pointwise limits from `tendsto_unitary_orbit`.
- `separatedSylvester_reconstruction_complex` — finite spectral steps at
  radius `1/(n+1)`, step operators converge by
  `tendsto_iff_norm_sub_tendsto_zero` + `squeeze_zero`, each step integral
  equals `X` by `finiteSpectralStep_reconstruction`, pass to the limit.
- `separatedSylvester_integrable_complex` — `norm_unitary_left_right`
  majorant.
- `spectral_step_integral_right_inverse` — new algebraic lemma
  `finiteDiagonal_sylvester_solution` in `FiniteBlockReconstruction.lean`
  (explicit blockwise solution `Σᵢⱼ (aᵢ−bⱼ)⁻¹ Pᵢ C Qⱼ`), so each finite
  reciprocal integral solves its finite Sylvester equation exactly
  (`simp only [hdefect]` rewrites under the integral binder); the identity
  passes to the norm limit through `tendsto_separated_integral` with constant
  `C` and two bilinear-composition limits.

### `Ideals/CompactIntegral.lean` — sorry-free (was 1)

`isCompactOperator_integral` via the quotient route: `Submodule.mkQL` into
`(E →L[ℂ] F) ⧸ compactOperatorSubmodule` (normed by
`Submodule.Quotient.normedAddCommGroup` under a `haveI : IsClosed …`), the
composed integrand is a.e. zero, `ContinuousLinearMap.integral_comp_comm`
(named-argument form; the subtype/`subtypeₗᵢ` route dies on
seminormed-instance mismatches), and `Submodule.Quotient.mk_eq_zero`.

## Not attempted (with reasons)

- `Ideals/Rectangular.lean` (4): each sorry is a declared separate analytic
  campaign (rectangular HS/trace/Schatten families over `RCLike`; Schauder's
  theorem absent from pinned Mathlib). Multi-session projects.
- `GraphSubspace.lean` (3): the acute ⇔ bounded-angular-graph Riccati
  equivalence (invert the near-identity compression, graph-range algebra,
  both directions). A coherent single campaign; recommend it as the next
  Fable-grade item.
- `MathAhead/HiddenFoundations/{Section3Nonacute, PolarIsometryFinal}` (6):
  polar-decomposition leaves, untouched.
- `MathAhead/HiddenFoundations/KyFanBochner.lean` is broken on `main`
  (pre-existing, 11 errors from commit de30805's rebase-ahead scaffolding) —
  unrelated to this branch; verified identical failure with this branch's
  changes stashed.
