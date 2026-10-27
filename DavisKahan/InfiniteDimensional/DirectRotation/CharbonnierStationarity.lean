/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierRankOneVariation
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Constrained Charbonnier stationarity in arbitrary Hilbert dimension

Finite-cost global minimizers have vanishing rank-one phase variations
in the source and its orthogonal complement. Polarization turns those
scalar identities into the intrinsic reflection/gradient stationarity
equation. No finite-dimensional trace on the ambient space is used.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open scoped ENNReal InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The phase-gradient quadratic form vanishes on each feasible unit
rank-one direction at a finite-cost global minimizer. -/
theorem re_inner_smoothed_gradient_eq_zero_on_unit_directions
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
    (x : E) (hx : ‖x‖ = 1) (hxK : x ∈ K ∨ x ∈ Kᗮ) :
    (inner ℂ x (smoothedUnitaryGradient tau (U : E →L[ℂ] E) x)).re = 0 := by
  let H := InnerProductSpace.rankOne ℂ x x
  have hcomm (N : Submodule ℂ E) [N.HasOrthogonalProjection] (hNx : x ∈ N) :
      Commute H N.starProjection := by
    ext y
    change inner ℂ x (N.starProjection y) • x = N.starProjection (inner ℂ x y • x)
    rw [map_smul, ← N.inner_starProjection_left_eq_right,
      N.starProjection_eq_self_iff.mpr hNx]
  have hHP : Commute H K.starProjection := by
    rcases hxK with hKx | hKx
    · exact hcomm K hKx
    · have hc := (Commute.one_right H).sub_right (hcomm Kᗮ hKx)
      simpa only [Submodule.starProjection_orthogonal', sub_sub_cancel] using hc
  have hH : IsSelfAdjoint H := InnerProductSpace.adjoint_rankOne x x
  let A (s : ℝ) := (U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H))
  have hExp (s : ℝ) : NormedSpace.exp (s • (Complex.I • H)) ∈ unitary (E →L[ℂ] E) := by
    let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  let W (s : ℝ) := Unitary.linearIsometryEquiv
    (⟨A s, mul_mem (Unitary.linearIsometryEquiv.symm U).property (hExp s)⟩ :
      unitary (E →L[ℂ] E))
  have hUproj := (K.map_eq_iff_conjugate_starProjection L U).mp hmap
  have hWmap (s : ℝ) : K.map (W s).toLinearMap = L := by
    apply (K.map_eq_iff_conjugate_starProjection L (W s)).mpr
    have hEP : Commute (NormedSpace.exp (s • (Complex.I • H))) K.starProjection :=
      ((hHP.smul_left Complex.I).smul_left s).exp_left
    change A s * K.starProjection * star (A s) = L.starProjection
    dsimp only [A]
    rw [star_mul]
    calc
      _ = (U : E →L[ℂ] E) *
          (NormedSpace.exp (s • (Complex.I • H)) * K.starProjection) *
          star (NormedSpace.exp (s • (Complex.I • H))) * star (U : E →L[ℂ] E) :=
        by noncomm_ring
      _ = (U : E →L[ℂ] E) * K.starProjection *
          (NormedSpace.exp (s • (Complex.I • H)) *
            star (NormedSpace.exp (s • (Complex.I • H)))) * star (U : E →L[ℂ] E) := by
        rw [hEP.eq]
        noncomm_ring
      _ = _ := by rw [Unitary.mul_star_self_of_mem (hExp s), mul_one, hUproj]
  have hcurve : IsLocalMin (fun s : ℝ => ((1 - A s).charbonnierCost tau).toReal) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    have hle := hmin (W s) (hWmap s)
    have hcost := charbonnier_unitary_rankOne_variation_ne_top tau hτ U hfinite x hx s
    have hreal := ENNReal.toReal_mono hcost hle
    simpa only [A, W, zero_smul, NormedSpace.exp_zero, mul_one] using hreal
  have hd := hasDerivAt_charbonnier_unitary_rankOne_variation tau hτ U hfinite x hx 0
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at hd
  exact hcurve.hasDerivAt_eq_zero hd

/-- The same quadratic form vanishes on all source and complementary
directions, with normalization justified explicitly. -/
theorem re_inner_smoothed_gradient_eq_zero_on_source_or_orthogonal
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau)
    (x : E) (hxK : x ∈ K ∨ x ∈ Kᗮ) :
    (inner ℂ x (smoothedUnitaryGradient tau (U : E →L[ℂ] E) x)).re = 0 := by
  by_cases hx0 : x = 0
  · simp only [hx0, inner_zero_left, Complex.zero_re]
  let r := ‖x‖⁻¹
  have hr : 0 < r := inv_pos.mpr (norm_pos_iff.mpr hx0)
  let y := (r : ℂ) • x
  have hy : ‖y‖ = 1 := by
    rw [show y = (r : ℂ) • x from rfl, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
  have hyK : y ∈ K ∨ y ∈ Kᗮ := hxK.imp (fun h => K.smul_mem (r : ℂ) h)
    (fun h => Kᗮ.smul_mem (r : ℂ) h)
  have h := re_inner_smoothed_gradient_eq_zero_on_unit_directions tau hτ K L U hmap
    hfinite hmin y hy hyK
  have hscale : (inner ℂ y (smoothedUnitaryGradient tau (U : E →L[ℂ] E) y)).re =
      r ^ 2 * (inner ℂ x (smoothedUnitaryGradient tau (U : E →L[ℂ] E) x)).re := by
    simp only [y, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hscale] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hr.ne')

/-- **Unrestricted Hilbert-space constrained stationarity.** At a
finite-cost global Charbonnier minimizer at positive smoothing, reflection in the
source negates the self-adjoint phase gradient. No rank, separability,
simple-spectrum or nonzero-displacement assumption is imposed. -/
theorem gradient_reflection_conjugate_eq_neg_of_charbonnier_minimal
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau) :
    let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
    ((2 : ℂ) • K.starProjection - 1) * G * ((2 : ℂ) • K.starProjection - 1) = -G := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  have hG : IsSelfAdjoint G := isSelfAdjoint_smoothedUnitaryGradient _ _
  have hdiag (N : Submodule ℂ E) [N.HasOrthogonalProjection]
      (hquad : ∀ x ∈ N, (inner ℂ x (G x)).re = 0) :
      N.starProjection * G * N.starProjection = 0 := by
    let A := N.starProjection * G * N.starProjection
    have hP : IsSelfAdjoint N.starProjection := isStarProjection_starProjection.isSelfAdjoint
    have hA : IsSelfAdjoint A := by
      change star (N.starProjection * G * N.starProjection) = _
      rw [star_mul, star_mul, hP.star_eq, hG.star_eq]
      exact (mul_assoc _ _ _).symm
    have hreal (x : E) : (inner ℂ x (A x)).re = 0 := by
      change (inner ℂ x (N.starProjection (G (N.starProjection x)))).re = 0
      rw [← N.inner_starProjection_left_eq_right]
      exact hquad _ (N.starProjection_apply_mem x)
    have hzero : A.toLinearMap = 0 := by
      apply hA.isSymmetric.inner_map_self_eq_zero.mp
      intro x
      apply inner_eq_zero_symm.mpr
      change inner ℂ x (A x) = 0
      have hfull := hA.isSymmetric.coe_re_inner_self_apply x
      change ((inner ℂ x (A x)).re : ℂ) = inner ℂ x (A x) at hfull
      exact hfull.symm.trans (congrArg Complex.ofReal (hreal x))
    ext x
    exact LinearMap.congr_fun hzero x
  have hK := hdiag K (fun x hx =>
    re_inner_smoothed_gradient_eq_zero_on_source_or_orthogonal tau hτ K L U hmap
      hfinite hmin x (Or.inl hx))
  have hKc := hdiag Kᗮ (fun x hx =>
    re_inner_smoothed_gradient_eq_zero_on_source_or_orthogonal tau hτ K L U hmap
      hfinite hmin x (Or.inr hx))
  rw [Submodule.starProjection_orthogonal'] at hKc
  change ((2 : ℂ) • K.starProjection - 1) * G * ((2 : ℂ) • K.starProjection - 1) = -G
  calc
    _ = -G + (K.starProjection * G * K.starProjection + K.starProjection * G * K.starProjection) +
        ((1 - K.starProjection) * G * (1 - K.starProjection) +
          (1 - K.starProjection) * G * (1 - K.starProjection)) := by
      simp only [two_smul]
      noncomm_ring
    _ = -G := by rw [hK, hKc]; simp

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
