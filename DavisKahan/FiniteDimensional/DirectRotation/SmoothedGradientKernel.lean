/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientPairing
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedTransportRestriction
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedReflectionSecondVariation

/-!
# Local minimality on the actual zero-gradient reflection space

The actual gradient kernel is invariant under both the transporter and
the source projection. Local minimality descends to its reflection
restriction against all unitary competitors on that carrier. No kernel
frame, excluded eigenphase or complementary spectral assumption is supplied.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every actual ambient local minimum induces a local reflection minimum
on its actual gradient kernel, retaining the source projection and the
ambient actions. Empty kernels and right-angle directions are allowed. -/
theorem gradient_kernel_local_reflection_restriction_complex
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let L := (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap.ker
    ∃ (V : L ≃ₗᵢ[ℂ] L) (S P₀ : L →L[ℂ] L),
      IsStarProjection S ∧ IsStarProjection P₀ ∧
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (∀ x : L, (P₀ x : E) = K.starProjection x) ∧
      (V : L →L[ℂ] L) = 1 - (2 : ℂ) • S ∧
      (2 : ℂ) • (S * P₀ * S) = S ∧
      IsLocalMinOn
        (fun W : L →L[ℂ] L => smoothedDisplacementCost tau W.toLinearMap)
        {W | W ∈ unitary (L →L[ℂ] L) ∧
          W * P₀ * star W = (V : L →L[ℂ] L) * P₀ * star (V : L →L[ℂ] L)}
        (V : L →L[ℂ] L) := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let L := G.toLinearMap.ker
  let J := K.reflection
  have hUfunc (x : E) : (Unitary.linearIsometryEquiv U) x = (U : E →L[ℂ] E) x := by
    simpa only [LinearIsometryEquiv.coe_coe''] using
      congrArg (fun T : E →L[ℂ] E => T x) (Unitary.coe_linearIsometryEquiv_apply U)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    tau htau K.starProjection Q hP U htrans hmin
  have hJ : (J : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hJ] at hconj
  have hPN : ∀ x ∈ L, K.starProjection x ∈ L := by
    intro x hx
    have hxG : G x = 0 := LinearMap.mem_ker.mp hx
    have hJG : G (J x) = 0 := by
      apply J.injective
      have h := congrArg (fun A : E →L[ℂ] E => A x) hconj
      change J (G (J x)) = -G x at h
      simpa only [hxG, neg_zero, map_zero] using h
    have hPexpr : K.starProjection = (1 / 2 : ℂ) • (1 + (J : E →L[ℂ] E)) := by
      rw [hJ]
      module
    change G (K.starProjection x) = 0
    rw [hPexpr]
    change G ((1 / 2 : ℂ) • (x + J x)) = 0
    rw [map_smul, map_add, hxG, hJG, add_zero, smul_zero]
  have hTN : ∀ x ∈ L, (Unitary.linearIsometryEquiv U) x ∈ L := by
    intro x hx
    have hxG : G x = 0 := LinearMap.mem_ker.mp hx
    have hcomm := congrArg (fun A : E →L[ℂ] E => A x)
      (commute_smoothedUnitaryGradient tau (U : E →L[ℂ] E)).eq
    change G ((U : E →L[ℂ] E) x) = (U : E →L[ℂ] E) (G x) at hcomm
    have hzero : G ((U : E →L[ℂ] E) x) = 0 := by rw [hcomm, hxG, map_zero]
    change G ((Unitary.linearIsometryEquiv U) x) = 0
    rw [hUfunc]
    exact hzero
  obtain ⟨V, hV, hVmin⟩ := exists_isLocalMinOn_restriction_of_invariant_complex tau
    (Unitary.linearIsometryEquiv U) K.starProjection hP.isSelfAdjoint L hTN hPN (by
      simpa only [Unitary.coe_linearIsometryEquiv_apply, htrans] using hmin)
  let P₀ : L →L[ℂ] L := (K.starProjection.toLinearMap.restrict hPN).toContinuousLinearMap
  have hP₀act (x : L) : (P₀ x : E) = K.starProjection x := rfl
  have hP₀ : IsStarProjection P₀ := by
    constructor
    · ext x
      change K.starProjection (K.starProjection x) = K.starProjection x
      exact DFunLike.congr_fun hP.isIdempotentElem.eq (x : E)
    · apply _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      intro x y
      change inner ℂ (K.starProjection x) y = inner ℂ (x : E) (K.starProjection y)
      exact hP.isSelfAdjoint.isSymmetric x y
  obtain ⟨V₀, S, hS, hV₀, hrepr⟩ := smoothed_gradient_kernel_reflection_representation tau htau U
  have hVV₀ : V = V₀ := by
    ext x
    exact (hV x).trans ((hUfunc x).trans (hV₀ x).symm)
  have hmin₀ := hVmin
  rw [hVV₀] at hmin₀
  have hbalance : (2 : ℂ) • (S * P₀ * S) = S := by
    apply reflection_balance_of_isLocalMinOn_transports_complex tau htau P₀
      ((V₀ : L →L[ℂ] L) * P₀ * star (V₀ : L →L[ℂ] L)) hP₀
      (Unitary.linearIsometryEquiv.symm V₀) ?_ ?_ S hS ?_
    · rw [Unitary.coe_symm_linearIsometryEquiv_apply]
    · simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using hmin₀
    · simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using hrepr
  exact ⟨V₀, S, P₀, hS, hP₀, hV₀, hP₀act, hrepr, hbalance, hmin₀⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
