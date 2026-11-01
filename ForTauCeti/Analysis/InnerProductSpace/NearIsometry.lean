/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5, GPT-6

Staged for Tau Ceti, roadmap topic T02.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
a proposed new file `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean`.

Original formalization by Claude Fable 5 and Claude Opus 4.8; subsequently redesigned
by Claude Opus 5. This version consumes TauCeti's independently proved polar factor.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Unitary
public import TauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Near-isometry paper-facing bounds via the native polar factor

A real finite-dimensional map whose Gram form differs from the identity by at
most a relative defect `delta` is close to a linear isometric equivalence.
The historical factorization theorem records both an isometry `W` and a
symmetric Gram square root `S` satisfying `M = W ∘ S`. The sharp pointwise
error is bounded by the same defect, rather than twice the defect.

TauCeti now supplies the finite-dimensional unitary polar factorization and the
modulus square-root estimate in
`TauCeti.Analysis.InnerProductSpace.Polar.Unitary` (PR #16127). The earlier
local eigenbasis, diagonal, and inverse-square-root construction is no longer
maintained. The proof below specializes the accepted TauCeti API to the
historical real-inner-product statement consumed by Acharyya and challenge
proofs. The remaining weaker-constant statements are still used as paper-facing
formulations.

## Provenance

* Original DKPS module: `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`,
  introduced in Davis--Kahan commit `fc38eb4` (Kitware, Apache-2.0).
* Original proof development: Claude Fable 5 and Claude Opus 4.8; a later
  polar-factor redesign by Claude Opus 5 is retained in Git history.
* Accepted upstream API: TauCeti PR #16127, integration commit
  `2b69ec4d36`, present in the pinned TauCeti main tree. The PR explicitly
  describes its proof as independent of the DKPS implementation, not an adapted
  or copied proof.
* November 1, 2026 consumption removes the 15 private helper declarations
  used exclusively by the old construction, while preserving all five public
  theorem statements for their existing consumers.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Polar factorization of a near-isometry.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (`|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`, with `δ < 1`), then `M` factors
as `M = W ∘ S`
where

* `W` is a linear isometry equivalence of `E`,
* `S` is the modulus of `M`: symmetric, with `S ∘ S = Mᵀ ∘ M`, and
* `S` moves no vector by more than `δ`: `‖S x - x‖ ≤ δ * ‖x‖`.

The proof takes `S = M.operatorAbs`, the positive square root of the Gram
operator, and uses TauCeti's accepted unitary polar factor to obtain `W`.
The norm estimate follows directly from the native modulus bound. The
original diagonal construction remains recoverable from Git history.

The historical hypothesis `δ < 1` is retained in the statement; TauCeti's
unitary polar factorization and modulus bound do not require that restriction. -/
theorem exists_linearIsometryEquiv_comp_polarFactor (M : E →ₗ[ℝ] E) {δ : ℝ} (_hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ (W : E ≃ₗᵢ[ℝ] E) (S : E →ₗ[ℝ] E),
      (∀ x : E, M x = W (S x)) ∧ S.IsSymmetric ∧ S ∘ₗ S = M.adjoint ∘ₗ M ∧
        ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
  have hnorm : ∀ x : E, |‖M x‖ ^ 2 - ‖x‖ ^ 2| ≤ δ * ‖x‖ ^ 2 := by
    intro x
    simpa only [real_inner_self_eq_norm_sq] using hM x
  obtain ⟨W, hW⟩ := M.exists_linearIsometryEquiv_comp_operatorAbs_eq rfl
  refine ⟨W, M.operatorAbs, ?_, M.isSymmetric_operatorAbs, M.operatorAbs_sq, ?_⟩
  · intro x
    have hWfun : (⇑(W : E →ₗ[ℝ] E) : E → E) = W := by
      rfl
    calc
      M x = ((W : E →ₗ[ℝ] E) ∘ₗ M.operatorAbs) x :=
        (LinearMap.congr_fun hW x).symm
      _ = W (M.operatorAbs x) := by
        rw [LinearMap.comp_apply]
        exact congrFun hWfun (M.operatorAbs x)
  · intro x
    exact M.norm_operatorAbs_apply_sub_le hnorm x

/-- **The sharp near-isometry estimate.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (with `δ < 1`), then `M` lies within `δ` — not `2 * δ` — of a genuine linear isometry
equivalence.

This is immediate from `exists_linearIsometryEquiv_comp_polarFactor`: `M x - W x` is the image
under the isometry `W` of `S x - x`. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, S, hMS, -, -, hSest⟩ := exists_linearIsometryEquiv_comp_polarFactor M hδ hM
  refine ⟨W, fun x => ?_⟩
  rw [hMS x, ← map_sub, W.norm_map]
  exact hSest x

/-- **Quantitative polar factor for a near-isometry**, historical form.

The accepted TauCeti polar-factor theorem gives the stronger constant `δ`.
This historical factor-two statement remains the form quoted downstream
(`Acharyya2025.PolarFactor`) and by the challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_norm_sub_apply_le M (by linarith) hM
  refine ⟨W, fun x => (hW x).trans ?_⟩
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · simp [Subsingleton.elim x (0 : E)]
  · have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
      exact nonneg_of_mul_nonneg_left
        (le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)) hvpos
    have := norm_nonneg x
    nlinarith

end LinearMap

namespace ContinuousLinearMap

/-- The operator-norm hypothesis `‖Mᵀ M - 1‖ ≤ δ` implies the pointwise quadratic-form
hypothesis, by Cauchy--Schwarz. -/
private theorem abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le (M : E →L[ℝ] E) {δ : ℝ}
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) (x : E) :
    |⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ| ≤
      δ * ⟪x, x⟫_ℝ := by
  have hid : ⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ
      = ⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ := by
    rw [sub_apply, mul_apply_eq_comp, one_apply_eq_self, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp
  rw [← hid]
  calc |⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ|
      ≤ ‖(ContinuousLinearMap.adjoint M * M - 1) x‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖ContinuousLinearMap.adjoint M * M - 1‖ * ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.adjoint M * M - 1).le_opNorm x) (norm_nonneg x)
    _ ≤ δ * ‖x‖ * ‖x‖ := by gcongr
    _ = δ * ⟪x, x⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]; ring

/-- **The sharp near-isometry estimate, operator-norm form.**  If a continuous linear map `M` on
a finite-dimensional real inner product space satisfies `‖Mᵀ M - 1‖ ≤ δ` with `δ < 1`,
then `M`
lies within `δ` of a genuine linear isometry equivalence.

See `ContinuousLinearMap.norm_sub_polarIsometryOfIsUnitModulus_le` in
`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean` for the version over arbitrary
`RCLike` Hilbert spaces, which additionally names the isometry. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, hW⟩ :=
    LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

/-- **Quantitative polar factor, operator-norm form**, historical statement.

The sharp operator-norm estimate above gives the stronger constant `δ`.
This historical factor-two statement remains for the downstream paper and the
challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := LinearMap.exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

end ContinuousLinearMap

end TauCeti

end
