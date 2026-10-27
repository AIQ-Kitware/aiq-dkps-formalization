/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierGradientHilbert
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Exponential
public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierFinite

/-!
# Actual native Charbonnier first variations on finite supports

The objective is the extended ambient spectral trace, with its baseline
subtracted inside each summand. Finite supports identify it with the
ordinary finite normal spectral trace before differentiation.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

section Finite

variable [FiniteDimensional ℂ E]

/-- On a finite normal operator, the real value of the native smoothed
cost is exactly its spectral trace. Nonnegative smoothing is essential
for the infinite sequence of zero singular values to contribute zero. -/
theorem charbonnierCost_toReal_eq_re_trace_cfc
    (tau : ℝ) (hτ : 0 ≤ tau) (W : E →L[ℂ] E) [IsStarNormal W] :
    ((1 - W).charbonnierCost tau).toReal =
      (LinearMap.trace ℂ E
        (cfc (fun z => (charbonnierDisplacementSymbol tau z : ℂ)) W).toLinearMap).re := by
  have hnonneg (i : Fin (Module.finrank ℂ E)) :
      0 ≤ Real.sqrt (tau ^ 2 + ((1 - W).toLinearMap.singularValues i) ^ 2) - tau :=
    sub_nonneg.mpr (Real.le_sqrt_of_sq_le
      (by nlinarith [sq_nonneg ((1 - W).toLinearMap.singularValues i)]))
  rw [ContinuousLinearMap.charbonnierCost_eq_ofReal_sum tau hτ,
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hnonneg i))]
  let := ContinuousLinearMap.isStarNormal_toLinearMap W
  obtain ⟨e, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal W.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hD (i) : ((LinearMap.id : E →ₗ[ℂ] E) - W.toLinearMap) (e i) =
      (1 - mu i) • e i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  have hlin : (1 - W).toLinearMap = LinearMap.id - W.toLinearMap := by
    ext x
    rfl
  rw [hlin, sum_singularValues_eq_sum_norm_eigenvalues e _ _ hD
    (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau),
    ContinuousLinearMap.re_trace_cfc_eq_sum (charbonnierDisplacementSymbol tau) W e mu hmu]
  apply Finset.sum_congr rfl
  intro i _
  simp only [charbonnierDisplacementSymbol, norm_sub_rev]

/-- Every finite Hermitian exponential variation has its actual native
Charbonnier first derivative at every time, without exclusions at identity. -/
theorem hasDerivAt_charbonnier_finite_unitary_right_variation_at
    (tau : ℝ) (hτ : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((1 - (U : E →L[ℂ] E) *
        NormedSpace.exp (s • (Complex.I • H))).charbonnierCost tau).toReal)
      (LinearMap.trace ℂ E
        (smoothedUnitaryGradient tau ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • H))) * H).toLinearMap).re t := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hd := hasDerivAt_unitary_spectral_right_variation_at
    (charbonnierDisplacementSymbol tau) (charbonnierDisplacementGradient tau)
    (continuous_charbonnierDisplacementGradient tau hτ).continuousOn
    (fun z _ w _ => charbonnierDisplacement_support tau hτ z w) U H hH t
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro s
  have hu : (U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H)) ∈
      unitary (E →L[ℂ] E) := by
    apply mul_mem U.property
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  let := isStarNormal_of_mem_unitary hu
  exact charbonnierCost_toReal_eq_re_trace_cfc tau hτ.le _

end Finite

/-- A finite-rank unitary displacement has its native Charbonnier
rank-one first derivative in any Hilbert dimension. The varied vector
need not lie in the original finite support. -/
theorem hasDerivAt_charbonnier_finite_rank_unitary_rankOne_variation
    (tau : ℝ) (hτ : 0 < tau)
    (U : E ≃ₗᵢ[ℂ] E) (n : ℕ) (hU : (1 - (U : E →L[ℂ] E)).rank ≤ n)
    (x : E) (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (1 - (U : E →L[ℂ] E) *
        NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x))).charbonnierCost tau
        |>.toReal)
      (inner ℂ x (smoothedUnitaryGradient tau
        ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • InnerProductSpace.rankOne ℂ x x))) x)).re t := by
  obtain ⟨M, hM, hxM, _, hUM, _, hfix⟩ :=
    exists_finite_transport_support (⊥ : Submodule ℂ E) (ℂ ∙ x) U n hU
  let : FiniteDimensional ℂ M := hM
  let x₀ : M := ⟨x, hxM (Submodule.mem_span_singleton_self x)⟩
  have hx₀ : ‖x₀‖ = 1 := hx
  obtain ⟨V, hV, _, _⟩ := U.exists_restriction_of_finite_invariant M hUM.mem_invtSubmodule
  let H := InnerProductSpace.rankOne ℂ x x
  let H₀ := InnerProductSpace.rankOne ℂ x₀ x₀
  have hH : IsSelfAdjoint H := InnerProductSpace.adjoint_rankOne x x
  have hH₀ : IsSelfAdjoint H₀ := InnerProductSpace.adjoint_rankOne x₀ x₀
  let A (s : ℝ) := (U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H))
  let A₀ (s : ℝ) := (V : M →L[ℂ] M) * NormedSpace.exp (s • (Complex.I • H₀))
  have hcast {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
      (B : F →L[ℂ] F) (s : ℝ) : s • (Complex.I • B) = ((s : ℂ) * Complex.I) • B := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    rfl
  have hexp (s : ℝ) (y : M) :
      (NormedSpace.exp (s • (Complex.I • H₀)) y : E) =
        NormedSpace.exp (s • (Complex.I • H)) (y : E) := by
    rw [hcast H₀ s, hcast H s,
      InnerProductSpace.exp_smul_rankOne_of_norm_eq_one x₀ hx₀,
      InnerProductSpace.exp_smul_rankOne_of_norm_eq_one x hx]
    rfl
  have hpoint (s : ℝ) (y : M) : (A₀ s y : E) = A s (y : E) := by
    change (V (NormedSpace.exp (s • (Complex.I • H₀)) y) : E) = _
    rw [hV, hexp]
    rfl
  have htail (s : ℝ) (y : E) (hy : y ∈ Mᗮ) : A s y = y := by
    have hHy : H y = 0 := by
      change inner ℂ x y • x = 0
      rw [M.inner_right_of_mem_orthogonal x₀.property hy, zero_smul]
    change U (NormedSpace.exp (s • (Complex.I • H)) y) = y
    rw [hcast H s, InnerProductSpace.exp_smul_rankOne_of_norm_eq_one x hx]
    change U (y + (Complex.exp _ - 1) • H y) = y
    rw [hHy, smul_zero, add_zero, hfix y hy]
  have hdisp (s : ℝ) : 1 - A s = M.subtypeL ∘L (1 - A₀ s) ∘L
      M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro y
      change (y : E) - A s y = (y : E) - (A₀ s y : E)
      rw [hpoint]
    · intro y hy
      change y - A s y = 0
      rw [htail s y hy, sub_self]
  have hvalue (s : ℝ) : ((1 - A s).charbonnierCost tau).toReal =
      ((1 - A₀ s).charbonnierCost tau).toReal := by
    rw [hdisp s, ContinuousLinearMap.charbonnierCost_orthogonal_extension]
  have hunit {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (B : F →L[ℂ] F) (hB : IsSelfAdjoint B) (s : ℝ) :
      NormedSpace.exp (s • (Complex.I • B)) ∈ unitary (F →L[ℂ] F) := by
    let +nondep : NormedAlgebra ℚ (F →L[ℂ] F) := .restrictScalars ℚ ℂ (F →L[ℂ] F)
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hB.star_eq]
  let W := Unitary.linearIsometryEquiv
    (⟨A t, mul_mem (Unitary.linearIsometryEquiv.symm U).property (hunit H hH t)⟩ :
      unitary (E →L[ℂ] E))
  let W₀ := Unitary.linearIsometryEquiv
    (⟨A₀ t, mul_mem (Unitary.linearIsometryEquiv.symm V).property (hunit H₀ hH₀ t)⟩ :
      unitary (M →L[ℂ] M))
  have hgrad := smoothedUnitaryGradient_apply_of_unitary_restriction tau hτ M W W₀
    (hpoint t) x₀
  change (smoothedUnitaryGradient tau (A₀ t) x₀ : E) =
    smoothedUnitaryGradient tau (A t) x at hgrad
  have hcoef : (LinearMap.trace ℂ M
      (smoothedUnitaryGradient tau (A₀ t) * H₀).toLinearMap).re =
        (inner ℂ x (smoothedUnitaryGradient tau (A t) x)).re := by
    change (LinearMap.trace ℂ M ((smoothedUnitaryGradient tau (A₀ t)).toLinearMap *
      (InnerProductSpace.rankOne ℂ x₀ x₀).toLinearMap)).re = _
    rw [InnerProductSpace.trace_mul_rankOne]
    change (inner ℂ x (smoothedUnitaryGradient tau (A₀ t) x₀ : E)).re = _
    rw [hgrad]
  have hd := hasDerivAt_charbonnier_finite_unitary_right_variation_at tau hτ
    (Unitary.linearIsometryEquiv.symm V) H₀ hH₀ t
  simp only [Unitary.coe_symm_linearIsometryEquiv_apply] at hd
  have hd' := hd.congr_deriv hcoef
  apply hd'.congr_of_eventuallyEq
  exact Eventually.of_forall hvalue

end TauCeti
