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

/-! # Near-isometry paper-facing bounds

The finite real statements with constant `2 * δ` serve Acharyya's
polar-factor lemma and the challenge signatures. The linear-map proof
uses TauCeti's sharp unitary polar bound.

## Provenance

The original DKPS construction is recoverable at `fc38eb4` under
`ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`.
TauCeti PR #16127 (integration `2b69ec4d36`) reports independent
development of the unitary polar decomposition and the sharp bound.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Quantitative polar factor for a near-isometry**, historical form.

The accepted TauCeti polar-factor theorem gives the stronger constant `δ`.
This historical factor-two statement remains the form quoted downstream
(`Acharyya2025.PolarFactor`) and by the challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} :
    (hδ : δ ≤ 1 / 2) →
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) →
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  intro _ hM
  have hnorm (x : E) : |‖M x‖ ^ 2 - ‖x‖ ^ 2| ≤ δ * ‖x‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hM x
  obtain ⟨W, _, hW⟩ :=
    M.exists_linearIsometryEquiv_comp_operatorAbs_eq_and_norm_apply_sub_le rfl hnorm
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

/-- **Quantitative polar factor, operator-norm form**, historical statement.

The operator-norm hypothesis supplies the quadratic-form bound for the
paper and challenge statement. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := LinearMap.exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

end ContinuousLinearMap

end TauCeti

end
