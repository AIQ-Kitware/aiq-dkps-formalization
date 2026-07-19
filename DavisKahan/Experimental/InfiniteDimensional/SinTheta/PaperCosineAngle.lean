/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.OperatorModulusApproximation
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperOperatorAngleBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# The source definition of the directed Davis--Kahan angle

The paper defines `Theta_0` from the cosine block, not from a previously named
sine block.  If `U` is the trial subspace and `V` is the exact subspace, the
cosine block is the overlap map from `U` to `V`; its positive source modulus is
`cos Theta_0`.  The angle is `arccos (cos Theta_0)` on the coordinate Hilbert
space `U`.

This module keeps the coordinate space explicit.  In particular, it does not
extend the cosine modulus by zero to the ambient orthogonal complement, where
`arccos 0 = pi/2` would create spurious angles.  It then proves that applying
sine to the source-defined angle has the complete singular-value sequence of
the cross projection into `V`'s orthogonal complement.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The overlap block whose singular values are the principal cosines. -/
noncomputable def paperCosineBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] V :=
  V.subtypeL.adjoint ∘L U.subtypeL

/-- The complementary overlap block whose singular values are the directed
principal sines. -/
noncomputable def paperSineBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] Vᗮ :=
  Vᗮ.subtypeL.adjoint ∘L U.subtypeL

/-- The positive cosine operator on the trial coordinate space. -/
noncomputable def paperCosineModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  rectangularOperatorModulus (paperCosineBlockC U V)

/-- The positive directed sine modulus on the trial coordinate space. -/
noncomputable def paperSineModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  rectangularOperatorModulus (paperSineBlockC U V)

/-- The cosine modulus is a positive contraction. -/
theorem norm_paperCosineModulusC_le_one
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖paperCosineModulusC U V‖ ≤ 1 := by
  rw [paperCosineModulusC]
  calc
    ‖rectangularOperatorModulus (paperCosineBlockC U V)‖ =
        ‖paperCosineBlockC U V‖ := norm_rectangularOperatorModulus _
    _ ≤ ‖V.subtypeL.adjoint‖ * ‖U.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      gcongr
      · rw [ContinuousLinearMap.norm_adjoint]
        exact opNorm_le_one_of_isometry V.isometry_subtype
      · exact opNorm_le_one_of_isometry U.isometry_subtype
    _ = 1 := by ring

/-- The real spectrum of the cosine modulus lies in `[0,1]`. -/
theorem spectrum_paperCosineModulusC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperCosineModulusC U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg
    (rectangularOperatorModulus_nonneg (paperCosineBlockC U V)) hx, ?_⟩
  have habs : |x| ≤ ‖paperCosineModulusC U V‖ :=
    spectrum.norm_le_norm_of_mem hx
  exact (le_abs_self x).trans
    (habs.trans (norm_paperCosineModulusC_le_one U V))

/-- The literal directed angle of Section 1 and Section 6 of the paper. -/
noncomputable def paperSourceDirectedAngleC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.arccos (paperCosineModulusC U V)

/-- The paper's literal `cos Theta_0`. -/
noncomputable def paperSourceDirectedCosC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.cos (paperSourceDirectedAngleC U V)

/-- The paper's literal `sin Theta_0`. -/
noncomputable def paperSourceDirectedSinC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.sin (paperSourceDirectedAngleC U V)

/-- Applying cosine to the source-defined angle recovers the overlap modulus. -/
theorem paperSourceDirectedCosC_eq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedCosC U V = paperCosineModulusC U V := by
  have hsa : IsSelfAdjoint (paperCosineModulusC U V) :=
    isSelfAdjoint_rectangularOperatorModulus _
  rw [paperSourceDirectedCosC, paperSourceDirectedAngleC,
    ← cfc_comp Real.cos Real.arccos (paperCosineModulusC U V)
      hsa.isStarNormal Real.continuous_cos.continuousOn
      Real.continuous_arccos.continuousOn]
  calc
    cfc (Real.cos ∘ Real.arccos) (paperCosineModulusC U V) =
        cfc (fun x : ℝ => x) (paperCosineModulusC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_paperCosineModulusC_subset_Icc U V hx
      exact Real.cos_arccos hxi.1 hxi.2
    _ = paperCosineModulusC U V := cfc_id' ℝ _

/-- Operator Pythagoras on the trial coordinate space. -/
theorem paperSineModulus_sq_add_paperCosineModulus_sq
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSineModulusC U V * paperSineModulusC U V +
      paperCosineModulusC U V * paperCosineModulusC U V =
        ContinuousLinearMap.id ℂ U := by
  rw [paperSineModulusC, paperCosineModulusC,
    rectangularOperatorModulus_mul_self,
    rectangularOperatorModulus_mul_self]
  ext x
  apply Subtype.ext
  change Vᗮ.starProjection (x : E) + V.starProjection (x : E) = (x : E)
  simpa [add_comm] using Submodule.starProjection_add_starProjection_orthogonal V (x : E)

/-- The source-defined sine is the positive square root complementary to the
cosine modulus. -/
theorem paperSourceDirectedSinC_eq_paperSineModulusC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedSinC U V = paperSineModulusC U V := by
  have hnonneg : 0 ≤ paperSourceDirectedSinC U V := by
    rw [paperSourceDirectedSinC]
    apply cfc_nonneg
    intro x hx
    exact Real.sin_nonneg_of_nonneg_of_le_pi
      (by
        obtain ⟨y, hy, rfl⟩ := spectrum_cfc_subset_image hx
        exact Real.arccos_nonneg y)
      (by
        obtain ⟨y, hy, rfl⟩ := spectrum_cfc_subset_image hx
        exact Real.arccos_le_pi y)
  have hsquare :
      paperSourceDirectedSinC U V * paperSourceDirectedSinC U V =
        (paperSineBlockC U V).adjoint ∘L paperSineBlockC U V := by
    rw [paperSourceDirectedSinC, ← cfc_mul _ _ _
      Real.continuous_sin.continuousOn Real.continuous_sin.continuousOn]
    have htrig :
        cfc (fun x : ℝ => Real.sin x * Real.sin x)
            (paperSourceDirectedAngleC U V) =
          ContinuousLinearMap.id ℂ U -
            paperCosineModulusC U V * paperCosineModulusC U V := by
      rw [← paperSourceDirectedCosC_eq U V,
        paperSourceDirectedCosC, ← cfc_mul _ _ _
          Real.continuous_cos.continuousOn Real.continuous_cos.continuousOn,
        ← cfc_sub _ _ _ continuous_const.continuousOn
          (Real.continuous_cos.mul Real.continuous_cos).continuousOn]
      apply cfc_congr
      intro x _
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [htrig]
    have hp := paperSineModulus_sq_add_paperCosineModulus_sq U V
    have hs := rectangularOperatorModulus_mul_self (paperSineBlockC U V)
    rw [← hs]
    exact eq_sub_of_add_eq hp
  show paperSourceDirectedSinC U V =
    CFC.sqrt ((paperSineBlockC U V).adjoint ∘L paperSineBlockC U V)
  exact (CFC.sqrt_unique hsquare hnonneg).symm

/-- The literal source `sin Theta_0` has exactly the singular values of the
cross projection printed in the paper. -/
theorem paperSourceDirectedSin_same_paperSineBlock
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    SameApproximationSingularValues
      (paperSourceDirectedSinC U V) (paperSineBlockC U V) := by
  rw [paperSourceDirectedSinC_eq_paperSineModulusC]
  exact sameApproximationSingularValues_rectangularOperatorModulus _


end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
