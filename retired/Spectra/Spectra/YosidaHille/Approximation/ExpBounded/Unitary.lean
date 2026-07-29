/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.ExpBounded.Adjoint

/-!
# Unitarity of exponentials of skew-adjoint operators

The exponential of a skew-adjoint operator is unitary, and the bounded exponential has the expected
derivative formulas. Specializing to `I • Aₙˢʸᵐ` (skew-adjoint, since `Aₙˢʸᵐ` is self-adjoint) gives
that `exp(i·Aₙˢʸᵐ·t)` is an isometry — the unitary approximants whose limit is the evolution group.

## Main statements

* `expBounded_skewAdjoint_unitary` — for `B* = -B`, both composites of `exp(tB)` with its adjoint
  are the identity.
* `expBounded_mem_unitary` — `exp(tB) ∈ unitary` when `B` is skew-adjoint.
* `smul_I_skewSelfAdjoint` — `I •` of a self-adjoint operator is skew-adjoint.
* `expBounded_yosidaApproxSym_unitary` / `expBounded_yosidaApproxSym_isometry` — `exp(i·Aₙˢʸᵐ·t)`
  preserves inner products and norms.
* `expBounded_hasDerivAt` — the derivative of the exponential.
-/
open Complex Filter Topology InnerProductSpace
open Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.YosidaHille.Approximation

noncomputable section

/-! ### Skew-adjoint implies unitary exponential -/

/-- If `B` is skew-adjoint (`B* = -B`), then `exp(tB)` is two-sided unitary: both composites with
its adjoint are the identity. -/
lemma expBounded_skewAdjoint_unitary (B : H →L[ℂ] H) (hB : B.adjoint = -B) (t : ℝ) :
    (expBounded B t).adjoint.comp (expBounded B t) = ContinuousLinearMap.id ℂ H ∧
    (expBounded B t).comp (expBounded B t).adjoint = ContinuousLinearMap.id ℂ H := by
  -- exp(tB)* = exp(tB*) = exp(t(-B)) = exp(-tB)
  have h_adj : (expBounded B t).adjoint = expBounded B (-t) := by
    rw [adjoint_expBounded]
    rw [hB]
    unfold expBounded
    congr 1
    ext k
    congr 2
    ext x
    simp only [ofReal_neg, neg_smul, smul_neg]
  have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
              (fun k : ℕ => if k = 0 then 1 else 0) := by
    ext k
    cases k with
    | zero => simp
    | succ k => simp [pow_succ]
  constructor
  · -- exp(tB)* ∘ exp(tB) = exp(-tB) ∘ exp(tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_add_smul B (-t) t]
    simp only [neg_add_cancel]
    unfold expBounded
    simp only [ofReal_zero, zero_smul]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]
  · -- exp(tB) ∘ exp(tB)* = exp(tB) ∘ exp(-tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_add_smul B t (-t)]
    simp only [add_neg_cancel]
    unfold expBounded
    simp only [ofReal_zero, zero_smul]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]

/-- For skew-adjoint `B`, `exp(tB)` lies in the unitary group. -/
lemma expBounded_mem_unitary (B : H →L[ℂ] H) (hB : B.adjoint = -B) (t : ℝ) :
    expBounded B t ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
  exact ⟨(expBounded_skewAdjoint_unitary B hB t).1, (expBounded_skewAdjoint_unitary B hB t).2⟩

/-! ### Unitarity for Yosida approximants -/

/-- If `A` is self-adjoint then `I • A` is skew-adjoint: `(I·A)* = -(I·A)`. -/
lemma smul_I_skewSelfAdjoint (A : H →L[ℂ] H) (hA : A.adjoint = A) :
    (I • A).adjoint = -(I • A) := by
  have h := ContinuousLinearMap.adjoint.map_smulₛₗ I A
  rw [h, hA, starRingEnd_apply, star_def, conj_I]
  simp only [neg_smul]

/-- `exp(i·Aₙˢʸᵐ·t)` preserves the inner product. -/
lemma expBounded_yosidaApproxSym_unitary {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (t : ℝ) (ψ φ : H) :
    ⟪expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ,
     expBounded (I • yosidaApproxSym hsym hplus hminus n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_skew := I_smul_yosidaApproxSym_skewAdjoint hsym hplus hminus n
  have h_unitary :=
    expBounded_skewAdjoint_unitary (I • yosidaApproxSym hsym hplus hminus n) h_skew t
  let U := expBounded (I • yosidaApproxSym hsym hplus hminus n) t
  calc ⟪U ψ, U φ⟫_ℂ
      = ⟪ψ, U.adjoint (U φ)⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right U ψ (U φ)).symm
    _ = ⟪ψ, (U.adjoint.comp U) φ⟫_ℂ := rfl
    _ = ⟪ψ, (ContinuousLinearMap.id ℂ H) φ⟫_ℂ := by rw [h_unitary.1]
    _ = ⟪ψ, φ⟫_ℂ := by simp

/-- `exp(i·Aₙˢʸᵐ·t)` is an isometry: it preserves norms. -/
theorem expBounded_yosidaApproxSym_isometry {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) (t : ℝ) (ψ : H) :
    ‖expBounded (I • yosidaApproxSym hsym hplus hminus n) t ψ‖ = ‖ψ‖ := by
  set U := expBounded (I • yosidaApproxSym hsym hplus hminus n) t with _hU
  have h_inner := expBounded_yosidaApproxSym_unitary hsym hplus hminus n t ψ ψ
  have h1 : ‖U ψ‖^2 = re ⟪U ψ, U ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) (U ψ)).symm
  have h2 : ‖ψ‖^2 = re ⟪ψ, ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) ψ).symm
  have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by
    rw [h1, h2, h_inner]
  have h_nonneg1 : 0 ≤ ‖U ψ‖ := norm_nonneg _
  have h_nonneg2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U ψ‖ - ‖ψ‖), sq_nonneg (‖U ψ‖ + ‖ψ‖), h_sq, h_nonneg1, h_nonneg2]

/-! ### Derivatives of exponential -/

-- Mathlib currently exposes both generic bounded-convergence structures and
-- operator-norm structures on continuous linear maps.  The direct generic parent
-- instances otherwise win before the normed instances can provide their parents,
-- so select the coherent operator-norm parents explicitly for these calculus facts.
local instance operatorNormAddCommGroup : AddCommGroup (H →L[ℂ] H) :=
  ContinuousLinearMap.toNormedAddCommGroup.toAddCommGroup

local instance operatorNormRealModule : Module ℝ (H →L[ℂ] H) :=
  ContinuousLinearMap.toNormedSpace.toModule

local instance operatorNormTopologicalSpace : TopologicalSpace (H →L[ℂ] H) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Differentiate the complex exponential curve and restrict it along `ℝ ↪ ℂ`.
This avoids installing a second real normed-algebra structure on the operator space. -/
private lemma expBounded_hasDerivAt_left (B : H →L[ℂ] H) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => expBounded B t) ((expBounded B τ).comp B) τ := by
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  haveI : IsScalarTower ℝ ℂ (H →L[ℂ] H) :=
    ⟨fun r c f => ContinuousLinearMap.ext fun x => smul_assoc r c (f x)⟩
  have h_complex :
      HasDerivAt (fun z : ℂ => NormedSpace.exp (z • B))
        (NormedSpace.exp ((τ : ℂ) • B) * B) (τ : ℂ) :=
    hasDerivAt_exp_smul_const B (τ : ℂ)
  have h_real_comp :
      HasDerivAt
        ((fun z : ℂ => NormedSpace.exp (z • B)) ∘ Complex.ofReal)
        (NormedSpace.exp ((τ : ℂ) • B) * B) τ := by
    unfold operatorNormAddCommGroup operatorNormRealModule operatorNormTopologicalSpace
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] using
      h_complex.scomp τ Complex.ofRealCLM.hasDerivAt
  have h_real :
      HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • B))
        (NormedSpace.exp ((τ : ℂ) • B) * B) τ :=
    h_real_comp.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  have h_expBounded :
      HasDerivAt (fun t : ℝ => expBounded B t)
        (NormedSpace.exp ((τ : ℂ) • B) * B) τ :=
    h_real.congr_of_eventuallyEq
      (Eventually.of_forall fun t => expBounded_eq_exp B t)
  have h_deriv :
      NormedSpace.exp ((τ : ℂ) • B) * B = (expBounded B τ).comp B := by
    rw [expBounded_eq_exp]
    ext x
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  exact h_expBounded.congr_deriv h_deriv

/-- The base case that `expBounded_hasDerivAt` bootstraps from: at `τ = 0`,
the derivative of `t ↦ exp(tB)` is `B`. -/
lemma expBounded_hasDerivAt_zero (B : H →L[ℂ] H) :
    HasDerivAt (fun τ : ℝ => expBounded B τ) B 0 := by
  apply (expBounded_hasDerivAt_left B 0).congr_deriv
  rw [expBounded_at_zero']
  ext x
  simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self]

/-- Derivative of the bounded exponential at any point. -/
lemma expBounded_hasDerivAt (B : H →L[ℂ] H) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => expBounded B t) (B.comp (expBounded B τ)) τ := by
  have h_left := expBounded_hasDerivAt_left B τ
  have h_comm : (expBounded B τ).comp B = B.comp (expBounded B τ) := by
    ext ψ
    simp only [ContinuousLinearMap.comp_apply]
    have h := B_commute_expBounded B τ
    unfold Commute SemiconjBy at h
    exact congrFun (congrArg DFunLike.coe h.symm) ψ
  exact h_left.congr_deriv h_comm

end

end Spectra.YosidaHille.Approximation
