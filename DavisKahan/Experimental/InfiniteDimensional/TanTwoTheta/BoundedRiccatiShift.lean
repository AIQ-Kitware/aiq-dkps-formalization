/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedRiccatiNorm

/-!
# Centered form-gap version of the sharp bounded Riccati estimate

The near-singular-pair argument is naturally stated after shifting the lower
block so its quadratic form is nonpositive.  This leaf proves that a common
real scalar shift leaves the Riccati equation unchanged and packages the sharp
norm estimate directly from an ordered quadratic-form gap with an arbitrary
center `c`.

The remaining ambient off-diagonal bridge only needs to construct the block
coordinates and obtain such a center from the ordered restricted spectra.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Shift both diagonal blocks by the same real scalar.  The off-diagonal
couplings are unchanged. -/
noncomputable def shiftBlockOperatorData
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1)) (c : ℝ) :
    BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1) where
  A0 := H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c
  A1 := H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c
  B01 := H.B01
  B10 := H.B10
  selfAdjoint0 := by
    have hA0 : IsSelfAdjoint H.A0 :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
    have hshift : IsSelfAdjoint
        (H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c) :=
      hA0.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hshift
  selfAdjoint1 := by
    have hA1 : IsSelfAdjoint H.A1 :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
    have hshift : IsSelfAdjoint
        (H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c) :=
      hA1.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hshift
  offDiagonalAdjoint := H.offDiagonalAdjoint

/-- The Riccati defect is invariant under a common real shift of the two
diagonal blocks. -/
theorem riccatiDefect_shiftBlockOperatorData
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c : ℝ) (X : E0 →L[ℂ] E1) :
    riccatiDefect (shiftBlockOperatorData H c) X = riccatiDefect H X := by
  let C0 : E0 →L[ℂ] E0 := algebraMap ℝ (E0 →L[ℂ] E0) c
  let C1 : E1 →L[ℂ] E1 := algebraMap ℝ (E1 →L[ℂ] E1) c
  have hscalar : C1 ∘L X = X ∘L C0 := by
    apply ContinuousLinearMap.ext
    intro u
    simp [C0, C1, Algebra.algebraMap_eq_smul_one]
  change
    (H.A1 - C1) ∘L X - X ∘L (H.A0 - C0) -
          X ∘L H.B01 ∘L X + H.B10 =
      H.A1 ∘L X - X ∘L H.A0 - X ∘L H.B01 ∘L X + H.B10
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hscalar]
  abel

/-- Solving the Riccati equation is invariant under a common real shift. -/
theorem solvesRiccati_shiftBlockOperatorData_iff
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c : ℝ) (X : E0 →L[ℂ] E1) :
    SolvesRiccati (shiftBlockOperatorData H c) X ↔ SolvesRiccati H X := by
  unfold SolvesRiccati
  rw [riccatiDefect_shiftBlockOperatorData]

private theorem re_inner_real_scalar_id
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (c : ℝ) (z : F) :
    RCLike.re
        ⟪(algebraMap ℝ (F →L[ℂ] F) c) z, z⟫_ℂ = c * ‖z‖ ^ 2 := by
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- An upper form bound at `c` becomes nonpositivity after shifting by `c`. -/
theorem shiftBlockOperatorData_A0_nonpos
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c : ℝ)
    (hA0 : ∀ z : E0,
      RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2) :
    ∀ z : E0,
      RCLike.re ⟪(shiftBlockOperatorData H c).A0 z, z⟫_ℂ ≤ 0 := by
  intro z
  have hscalar := re_inner_real_scalar_id c z
  change RCLike.re
      ⟪(H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c) z, z⟫_ℂ ≤ 0
  rw [sub_apply, inner_sub_left, map_sub, hscalar]
  linarith [hA0 z]

/-- A lower form bound at `c + d` becomes a lower bound by `d` after shifting
by `c`. -/
theorem shiftBlockOperatorData_A1_lower
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (c d : ℝ)
    (hA1 : ∀ z : E1,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ) :
    ∀ z : E1,
      d * ‖z‖ ^ 2 ≤
        RCLike.re ⟪(shiftBlockOperatorData H c).A1 z, z⟫_ℂ := by
  intro z
  have hscalar := re_inner_real_scalar_id c z
  change d * ‖z‖ ^ 2 ≤
      RCLike.re
        ⟪(H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c) z, z⟫_ℂ
  rw [sub_apply, inner_sub_left, map_sub, hscalar]
  linarith [hA1 z]

/-- Sharp norm inequality for a contractive Riccati solution under an ordered
quadratic-form gap centered at an arbitrary real scalar `c`. -/
theorem sharp_riccati_norm_bound_of_form_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {c d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0,
      RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2)
    (hA1 : ∀ z : E1,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    d * ‖X‖ ≤ ‖H.B01‖ * (1 - ‖X‖ ^ 2) := by
  have hXshift : SolvesRiccati (shiftBlockOperatorData H c) X :=
    (solvesRiccati_shiftBlockOperatorData_iff H c X).2 hX
  have hbound := sharp_riccati_norm_bound
    (shiftBlockOperatorData H c) hd0
    (shiftBlockOperatorData_A0_nonpos H c hA0)
    (shiftBlockOperatorData_A1_lower H c d hA1)
    hXshift hXc
  simpa [shiftBlockOperatorData] using hbound

end DavisKahanExt
end TauCeti