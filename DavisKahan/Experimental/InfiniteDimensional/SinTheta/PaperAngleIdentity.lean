/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCosineAngle
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCosineAngleReal

/-!
# Equality of the cosine-defined and sine-defined directed angles

Davis and Kahan define the directed angle from the positive cosine overlap.
A modern projection formulation often starts from the positive complementary
sine modulus.  On the canonical range `[0, pi/2]` these are not merely
operators with matching singular data: functional calculus shows that they
produce exactly the same angle operator.
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

/-- The source cosine-defined directed angle has spectrum in `[0, pi/2]`. -/
theorem spectrum_paperSourceDirectedAngleC_subset_Icc
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (paperSourceDirectedAngleC U V) ⊆
      Set.Icc 0 (Real.pi / 2) := by
  have hsa : IsSelfAdjoint (paperCosineModulusC U V) :=
    isSelfAdjoint_rectangularOperatorModulus _
  intro y hy
  rw [paperSourceDirectedAngleC,
    cfc_map_spectrum (R := ℝ) Real.arccos (paperCosineModulusC U V)
      hsa Real.continuous_arccos.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_paperCosineModulusC_subset_Icc U V hx
  exact ⟨Real.arccos_nonneg x,
    (Real.arccos_le_pi_div_two).2 hxi.1⟩

/-- The angle reconstructed from the positive sine modulus. -/
noncomputable def paperSineDefinedDirectedAngleC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : U →L[ℂ] U :=
  cfc Real.arcsin (paperSineModulusC U V)

/-- The angle reconstructed from the sine modulus is exactly the source
cosine-defined angle. -/
theorem paperSineDefinedDirectedAngleC_eq_source
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSineDefinedDirectedAngleC U V = paperSourceDirectedAngleC U V := by
  have hangle : IsSelfAdjoint (paperSourceDirectedAngleC U V) :=
    cfc_predicate Real.arccos (paperCosineModulusC U V)
  rw [paperSineDefinedDirectedAngleC,
    ← paperSourceDirectedSinC_eq_paperSineModulusC U V,
    paperSourceDirectedSinC,
    ← cfc_comp Real.arcsin Real.sin (paperSourceDirectedAngleC U V)
      hangle Real.continuous_arcsin.continuousOn
      Real.continuous_sin.continuousOn]
  calc
    cfc (Real.arcsin ∘ Real.sin) (paperSourceDirectedAngleC U V) =
        cfc (fun x : ℝ => x) (paperSourceDirectedAngleC U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_paperSourceDirectedAngleC_subset_Icc U V hx
      exact Real.arcsin_sin
        (by linarith [hxi.1, Real.pi_pos]) hxi.2
    _ = paperSourceDirectedAngleC U V := cfc_id' ℝ _

/-- Equivalent formulation with the source angle on the left. -/
theorem paperSourceDirectedAngleC_eq_arcsin_sineModulus
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedAngleC U V =
      cfc Real.arcsin (paperSineModulusC U V) :=
  (paperSineDefinedDirectedAngleC_eq_source U V).symm

section Real

variable {F : Type v}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- For real subspaces, the sine-reconstructed angle on the canonical
complexification equals the source cosine-defined angle. -/
theorem paperSourceDirectedAngleR_eq_arcsin_sineModulus
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    paperSourceDirectedAngleR U V =
      cfc Real.arcsin
        (paperSineModulusC
          (Foundation.complexifySubmodule U)
          (Foundation.complexifySubmodule V)) :=
  paperSourceDirectedAngleC_eq_arcsin_sineModulus _ _

end Real

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
