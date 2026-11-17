/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.DoubleAngle.QuarterAcute
import ForTauCeti.Analysis.InnerProductSpace.Complexification.Projection
import ForTauCeti.Analysis.InnerProductSpace.Complexification.FormBounds

/-!
# The real quarter-angle branch

The ordered form gap and full off-diagonality force a strict quarter-angle
bound also on real Hilbert spaces. Complexify the operators and subspaces,
apply the complex theorem, and use preservation of the projection gap.

Adapted from the real transfer in
`DavisKahan/InfiniteDimensional/TanTwoTheta/SelectedBranchSymmetricNormingReal.lean`
and its form/projection transport modules (Kitware, Jon Crall and Claude Opus 5;
Apache-2.0). This proof uses Tau Ceti's native Hilbert complexification throughout.
-/

public section

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The ordered form gap and an off-diagonal perturbation imply the strict quarter-angle
bound on an arbitrary real Hilbert space. -/
theorem projectionGap_lt_sqrt_two_div_two_of_orderedFormGap_real
    (U V : Submodule ℝ E) (A H : E →L[ℝ] E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : A.LowerFormBoundOn U b) (hUperpLow : A.UpperFormBoundOn Uᗮ a)
    (hVhigh : (A + H).LowerFormBoundOn V b)
    (hVperpLow : (A + H).UpperFormBoundOn Vᗮ a)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    U.projectionGap V < Real.sqrt 2 / 2 := by
  have maps {T : E →L[ℝ] E} {S W : Submodule ℝ E}
      (h : ∀ x ∈ S, T x ∈ W) :
      ∀ z ∈ S.complexifyL2, T.complexifyL2 z ∈ W.complexifyL2 := by
    intro z hz
    rw [mem_complexifyL2] at hz ⊢
    simpa using And.intro (h _ hz.1) (h _ hz.2)
  have h := projectionGap_lt_sqrt_two_div_two_of_orderedFormGap
    U.complexifyL2 V.complexifyL2 A.complexifyL2 H.complexifyL2
    (ContinuousLinearMap.isSelfAdjoint_complexifyL2_iff.mpr hA)
    (ContinuousLinearMap.isSelfAdjoint_complexifyL2_iff.mpr hH)
    (maps hAU) (by simpa using maps hAplusH_V) hab
    ((A.lowerFormBoundOn_complexifyL2_iff U b).mpr hUhigh)
    (by simpa only [complexifyL2_orthogonal] using
      (A.upperFormBoundOn_complexifyL2_iff Uᗮ a).mpr hUperpLow)
    (by simpa only [ContinuousLinearMap.complexifyL2_add] using
      ((A + H).lowerFormBoundOn_complexifyL2_iff V b).mpr hVhigh)
    (by simpa only [ContinuousLinearMap.complexifyL2_add, complexifyL2_orthogonal] using
      ((A + H).upperFormBoundOn_complexifyL2_iff Vᗮ a).mpr hVperpLow)
    (by simpa using maps hHU) (by simpa using maps hHUperp)
  simpa only [projectionGap_complexifyL2] using h

end Submodule
