/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenGradientHilbert
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Exponential
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite

/-!
# Rank-one phase variations of finite-rank unitary perturbations

The ambient Hilbert space is arbitrary. A finite reducing support
containing the varied unit vector carries the actual curve, its complete
displacement spectrum and its gradient pairing. Finite spectral calculus
therefore computes the derivative of the native ambient Schatten cost.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The native ambient Schatten cost of a finite-rank unitary
perturbation has the rank-one phase derivative at every real time.
The ambient space need not be finite-dimensional or separable. -/
theorem hasDerivAt_schatten_finite_rank_unitary_rankOne_variation
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (U : E ≃ₗᵢ[ℂ] E) (n : ℕ) (hU : (1 - (U : E →L[ℂ] E)).rank ≤ n)
    (x : E) (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E) *
          NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x)))) ^
            p.toReal |>.toReal)
      (inner ℂ x (schattenUnitaryGradient p.toReal
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
  have hvalue (s : ℝ) :
      ((OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - A s) ^ p.toReal).toReal =
        UnitarilyInvariantSeminorm.schatten ℂ M M p
          (LinearMap.id - (A₀ s).toLinearMap) ^ p.toReal := by
    rw [hdisp s, OperatorIdealFamily.gauge_orthogonal_extension,
      OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
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
  have hgrad := schattenUnitaryGradient_apply_of_unitary_restriction p.toReal hp1 M W W₀
    (hpoint t) x₀
  change (schattenUnitaryGradient p.toReal (A₀ t) x₀ : E) =
    schattenUnitaryGradient p.toReal (A t) x at hgrad
  have hcoef : (LinearMap.trace ℂ M
      (schattenUnitaryGradient p.toReal (A₀ t) * H₀).toLinearMap).re =
        (inner ℂ x (schattenUnitaryGradient p.toReal (A t) x)).re := by
    change (LinearMap.trace ℂ M ((schattenUnitaryGradient p.toReal (A₀ t)).toLinearMap *
      (InnerProductSpace.rankOne ℂ x₀ x₀).toLinearMap)).re = _
    rw [InnerProductSpace.trace_mul_rankOne]
    change (inner ℂ x (schattenUnitaryGradient p.toReal (A₀ t) x₀ : E)).re = _
    rw [hgrad]
  have hd := hasDerivAt_schatten_unitary_right_variation_at p hp hp1
    (Unitary.linearIsometryEquiv.symm V) H₀ hH₀ t
  simp only [Unitary.coe_symm_linearIsometryEquiv_apply] at hd
  have hd' := hd.congr_deriv hcoef
  apply hd'.congr_of_eventuallyEq
  exact Eventually.of_forall hvalue

end TauCeti
