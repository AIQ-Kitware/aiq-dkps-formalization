# Circle Riesz (contour) lane — status and proof plan, 2026-07-23 (fable)

Lane: `Frontier/Core.lean` `circleRieszProjection` + all 8 `Frontier/RieszCircle.lean`
declarations (claimed in `dev/LANES.md`).

## Landed (this commit, build green)

- `Frontier/Core.lean`: `circleRieszProjection A c r :=
  (2 π i)⁻¹ • ∮ z in C((c:ℂ), r), Ring.inverse (z • 1 - A)` — via Mathlib's
  `circleIntegral`, which is fully general in a complete normed ℂ-space, so it
  applies directly to `H →L[ℂ] H`. `Ring.inverse` keeps the definition total
  (no separation hypothesis needed). Core sorry closed.
- `RieszCircle.lean`: `circleResolventIntegrand` (deriv-weighted resolvent at
  the parametrized circle point, matching `circleIntegral`'s integrand shape),
  `circleRieszProjectionIntegral` (interval-integral form), and
  `circleRieszProjection_eq_integral := rfl` (the two definitions were written
  to be definitionally equal). 3 of 9 obligations closed; 5 sorries remain.

## Survey results (two agent sweeps, 2026-07-23)

Pinned Mathlib (3dffaf2f):
- HAS: `circleIntegral` for operator-valued integrands; `circleMap` API
  (`circleMap_mem_sphere`, `deriv_circleMap`, `continuous_circleMap`);
  `circleIntegral.integral_sub_inv_of_mem_ball` (`∮ (z-w)⁻¹ = 2πi` inside);
  `circleIntegral_eq_zero_of_differentiable_on_off_countable` +
  `DiffContOnCl.circleIntegral_eq_zero` (Cauchy–Goursat);
  `circleIntegral.norm_integral_le_of_norm_le_const` (needs `0 ≤ R`) and
  `norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` (`≤ R·C`, exactly the
  normalized bound); `circleIntegral.integral_sub` (needs `CircleIntegrable`
  both); `NormedRing.inverse_continuousAt`; `Units.isOpen`;
  `spectrum.notMem_iff`; `Algebra.algebraMap_eq_smul_one`;
  `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`;
  `ContinuousLinearMap.intervalIntegral_comp_comm`.
- MISSING (derive locally): outside-closed-ball vanishing of `∮ (z-w)⁻¹`
  (one step from `DiffContOnCl.circleIntegral_eq_zero`); the second resolvent
  identity for `Ring.inverse` (`R' - R = R' E R`); any `‖Ring.inverse x‖`
  bound; any Riesz-projection/holomorphic functional calculus.

Repo/Spectra: the abstract contour identity is ALREADY PROVED —
`SpectralSeparatingContour.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection`
(`SinTheta/ContinuationSpectralIdentification.lean:970`) via the chain
`contourRieszProjection_eq_cfcL` → `spectralCalculus_selector_eq_cfcL`
(Cayley bridge, :843) → `boundedSelfAdjointSpectralProjection_eq_spectralCalculus_selector`
(:154). All the Cayley infrastructure in that file
(`boundedMobiusSymbol`, `cayley_boundedSelfAdjointOperator_eq_cfc`,
`boundedCayleySpectrumInverse`, `inverseMobius_boundedMobiusSymbol_ofReal`, …)
is Γ-independent and reusable; `cfcL_intervalIntegral` (:268) is the
integral/CFC exchange; `ContinuousMap.mkD` + `cfc_eq_cfcL_mkD` bundle symbols.
No PVM operator-integral machinery exists or is needed.

## Proof plan for the remaining 5 sorries

1. `continuous_circleResolventIntegrand`: `deriv_circleMap` is continuous;
   resolvent factor continuous at every θ because
   `hsep.contour_resolvent` + `circleMap_mem_sphere` (+ `mem_sphere_iff_norm`,
   `spectrum.notMem_iff`, `Algebra.algebraMap_eq_smul_one`) make the point a
   unit, then `NormedRing.inverse_continuousAt u |>.comp` the affine map.
2. `scalar_circleIntegral_resolvent_indicator`: inside —
   `integral_sub_inv_of_mem_ball` then `div_self` (`2πI ≠ 0`); outside —
   `DiffContOnCl.circleIntegral_eq_zero` on `(z - x)⁻¹` (differentiable on the
   closed ball since `x` is outside it), then `zero_div`. Translate
   `|x - c|` ↔ `‖(x:ℂ) - c‖` via `Complex.ofReal_sub` + `Complex.norm_ofReal`
   (`Complex.abs` is gone in this Mathlib).
3. `circleRieszProjection_eq_boundedSelfAdjointSpectralProjection` (the big
   one) — cfc route, NOT the SpectralSeparatingContour instantiation (avoids
   Path/breakpoints/winding/margin-compactness work):
   a. Private `ringInverse_eq_cfc_of_notMem_spectrum`:
      `z ∉ spectrum ℂ A → Ring.inverse (z•1 - A) = cfc (fun w => (z-w)⁻¹) A`.
      Mirror `resolventOperator_eq_cfc_resolventSymbol` (:173) with the
      `(z-w)` orientation: `cfc_sub`/`cfc_const`/`cfc_id'`/
      `algebraMap_eq_smul_one` for the shift, `cfc_mul` + `cfc_congr` +
      `cfc_const_one` for both inverse laws, then two-sided-inverse ⇒
      `Ring.inverse` via `Units.mk` + `Ring.inverse_unit`. NOTE the sign: our
      integrand inverts `(z•1 - A)`, so the symbol is `(z - w)⁻¹` and the
      scalar integral comes out as `+∮(z-λ)⁻¹` — no rieszNormalization minus.
   b. Private `circleSymbol A c r θ : C(spectrum ℂ A, ℂ) :=
      ContinuousMap.mkD ((spectrum ℂ A).restrict
        (fun w => deriv (circleMap c r) θ * (circleMap c r θ - w)⁻¹)) 0`;
      pointwise `cfcL (circleSymbol …) = circleResolventIntegrand …` via
      `cfc_eq_cfcL_mkD` + `cfc_const_mul` + (a). Holds for ALL θ (no Icc
      restriction — `circleMap` is global; simpler than the contour case).
   c. Integrability of `circleSymbol`: pull back from the operator side
      (sorry 1 gives continuity ⇒ `Continuous.intervalIntegrable`) through
      `isometry_cfcHom` using
      `LipschitzWith.integrable_comp_iff_of_antilipschitz` — copy the
      `intervalIntegrable_contourResolventSymbol` pattern (:370).
   d. Exchange: `cfcL_intervalIntegral` + `map_smul` give
      `circleRieszProjection = cfcL ((2πi)⁻¹ • ∫ θ in 0..2π, circleSymbol θ)`.
   e. Evaluation at real spectral λ: `ContinuousMap.integral_apply` +
      `ContinuousMap.mkD_apply_of_continuousOn`, the integral is definitionally
      `∮ (z - λ)⁻¹` (smul_eq_mul), apply sorry 2; the boundary hypothesis
      `|λ - c| ≠ radius` follows from `hsep.contour_resolvent` (a spectral
      point on the circle contradicts separation), and
      `hsep.inside_iff_mem` converts the ball indicator to
      `spectralSelector s λ`.
   f. Private `spectralCalculus_selector_eq_cfcL_of_agrees`: generalize
      `spectralCalculus_selector_eq_cfcL` (:843) over any
      `g : C(spectrum ℂ A, ℂ)` with
      `∀ lam (hlam : (lam:ℂ) ∈ spectrum ℂ A), g ⟨lam, hlam⟩ = spectralSelector s lam`
      — the original uses Γ only through `integratedContourResolventSymbol`
      (as the continuity witness in `continuous_cayleySelectorPullback`, :812)
      and the final selector equation; both become `g`/`hg`. All Cayley
      lemmas it invokes are Γ-free and importable. State `hg` with explicit
      spectrum membership, NOT through the `realSpectrum` abbrev (rw cannot
      see through it — see dkps-name-verification-and-cfc).
   g. Chain d+e+f with `boundedSelfAdjointSpectralProjection_eq_spectralCalculus_selector`.
   Requires importing
   `DavisKahan.Experimental.InfiniteDimensional.SinTheta.ContinuationSpectralIdentification`
   into RieszCircle.lean (no cycle: SinTheta does not import Frontier).
4. `norm_circleRieszProjection_sub_le`: SIGNATURE DEFECT — as stated it is
   FALSE for `radius < 0` with `E ≠ 0` (hypotheses quantify over
   `‖z - c‖ = radius`, vacuous for negative radius, while the RHS goes
   negative; LHS is a norm). Add `(hr : 0 ≤ radius)`. Proof: pointwise bound
   `‖R'(z) - R(z)‖ ≤ ‖E‖/margin²` holds in ALL unit/non-unit cases:
   both units → second resolvent identity `R' - R = R' E R` (prove locally);
   both non-units → 0; mixed → the unit side forces `margin ≤ ‖E‖` (else
   `1 - R E` is a unit by geometric series, making the other side a unit too),
   so the single surviving `margin⁻¹ ≤ ‖E‖/margin²`. Integrability of each
   integrand: `Ring.inverse ∘ continuous` is continuous on the open unit
   preimage (`Units.isOpen`) and ZERO off it (`Ring.inverse_non_unit`), hence
   strongly measurable via restrict-decomposition
   (`Measure.restrict_union` on `I ∩ U` / `I \ U`,
   `ContinuousOn.aestronglyMeasurable`, `Measure.integrableOn_of_bounded`) and
   bounded by `margin⁻¹` — package as a private helper. Then
   `circleIntegral.integral_sub` +
   `norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`.
5. `continuous_circleRieszProjection_path`: also add `(hr : 0 ≤ radius)`
   (same vacuity issue). With `hres` units everywhere on `Icc 0 1 × circle`,
   the map `(t, θ) ↦ Ring.inverse (circleMap c r θ • 1 - (A + t•E))` is
   jointly continuous (affine in `(t,θ)` composed with `inverse_continuousAt`
   at units), then
   `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
   (restricted to `Icc 0 1` via `ContinuousOn`; may need the ε-neighborhood
   trick or `ContinuousOn.comp` since the parametric lemma wants global
   continuity in the parameter — restrict to the subtype `Icc 0 1` and use
   `continuousOn_iff_continuous_restrict`).

## Consumer note

Section3/8/9 should target these signatures. The two signature amendments
(nonnegative radius on 4 and 5) are strictly necessary (statements false as
given); `CircleSeparatesRealSpectrum.radius_pos` already supplies positivity
at every intended call site (e.g. `Section8.CircleContinuationData.separates`).
