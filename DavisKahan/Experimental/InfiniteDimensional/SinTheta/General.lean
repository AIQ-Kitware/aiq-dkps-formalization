/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Basic
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Bounded
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection

/-!
# Infinite-dimensional `sin Θ` theorems

The proofs are all reductions to Sylvester inversion.  Ordered separation gives
constant one, arbitrary separated spectra give the universal `π/2` multiplier,
and interval/exterior separation is handled by the centered bound/inverse
construction.  The symmetric-ideal endpoint uses the corresponding double
operator integral directly, so it does not lose a factor by estimating the two
directed blocks separately.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- The projected residual satisfies the restricted Sylvester equation. -/
theorem directedResidual_sylvesterEquation
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U)
    {X : F →L[𝕜] E} {M : F →L[𝕜] F} :
    let Y := complementaryProjection U ∘L X
    let C := complementaryProjection U ∘L residual A X M
    (A.restrictToOrthogonal hU) ∘L Y.corestrict Uᗮ -
      Y.corestrict Uᗮ ∘L M = C.corestrict Uᗮ := by
  dsimp
  ext x
  simp [residual, ContinuousLinearMap.comp_assoc,
    projection_apply_comm_of_reduces A U hU]

/-- Residual `sin Θ` theorem for an isometric trial map. -/
theorem sinTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U)
    {X : F →L[𝕜] E} (hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated M ⊤ A Uᗮ d) :
    d * ‖sinThetaEmbedding U X‖ ≤ ‖residual A X M‖ := by
  let Y : F →L[𝕜] Uᗮ :=
    (complementaryProjection U ∘L X).corestrict Uᗮ
  let C : F →L[𝕜] Uᗮ :=
    (complementaryProjection U ∘L residual A X M).corestrict Uᗮ
  have hEq : sylvesterOperator (A.restrictToOrthogonal hU) M Y = C :=
    directedResidual_sylvesterEquation hA hU
  have hsep' : OrderedSpectraSeparated M ⊤
      (A.restrictToOrthogonal hU) ⊤ d :=
    restrictedSpectrum_orthogonal_eq hA hU ▸ hsep
  have hbound := norm_sylvester_le_of_orderedSeparation
    (hA.restrictToOrthogonal hU) hM hd hsep' hEq
  have hY : ‖Y‖ = ‖sinThetaEmbedding U X‖ :=
    corestrict_norm_eq_of_range _
  have hC : ‖C‖ ≤ ‖residual A X M‖ := by
    calc
      ‖C‖ = ‖complementaryProjection U ∘L residual A X M‖ :=
        corestrict_norm_eq_of_range _
      _ ≤ ‖residual A X M‖ :=
        projection_comp_opNorm_le Uᗮ _
  simpa [hY] using hbound.trans hC

/-- The directed perturbation block satisfies a Sylvester equation between the
selected restriction of `A` and the complementary restriction of `B`. -/
theorem directedPerturbation_sylvesterEquation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V) :
    let X : U →L[𝕜] Vᗮ :=
      (complementaryProjection V ∘L U.subtypeL).corestrict Vᗮ
    let C : U →L[𝕜] Vᗮ :=
      (complementaryProjection V ∘L (B - A) ∘L U.subtypeL).corestrict Vᗮ
    (B.restrictToOrthogonal hV) ∘L X - X ∘L (A.restrict hU.1) = C := by
  dsimp
  ext x
  simp [ContinuousLinearMap.comp_assoc,
    projection_apply_comm_of_reduces A U hU,
    projection_apply_comm_of_reduces B V hV]

/-- One-sided perturbation theorem for spectral subspaces. -/
theorem sinTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    d * directedGap U V ≤ ‖B - A‖ := by
  let X : U →L[𝕜] Vᗮ :=
    (complementaryProjection V ∘L U.subtypeL).corestrict Vᗮ
  let C : U →L[𝕜] Vᗮ :=
    (complementaryProjection V ∘L (B - A) ∘L U.subtypeL).corestrict Vᗮ
  have hEq := directedPerturbation_sylvesterEquation hA hB hU hV
  have hgap' : ExactSinTheta.IntervalExteriorGap
      (B.restrictToOrthogonal hV) (A.restrict hU.1)
      left right d := by
    exact intervalExteriorSeparated_restrictions hA hB hU hV hgap
  have hsolve := ExactSinTheta.sylvester_mem_and_gauge_le_of_intervalExteriorGap
    ExactSinTheta.RectangularSymmetricIdealFamily.operatorNorm
    (hB.restrictToOrthogonal hV) (hA.restrict hU.1)
    (le_of_mem_Icc hgap) hd hgap' hEq trivial
  have hX : ‖X‖ = directedGap U V :=
    directedGap_eq_restrictedBlock_norm U V
  have hC : ‖C‖ ≤ ‖B - A‖ :=
    restricted_projection_sandwich_norm_le _ _ _
  simpa [ExactSinTheta.RectangularSymmetricIdealFamily.operatorNorm, hX]
    using hsolve.2.trans hC

theorem sinTheta_directed_coercive
    {A B : E →L[𝕜] E} (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hVc : ∀ x ∈ V, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(projection V ∘L projection U : E →L[𝕜] E)‖ ≤ ‖B - A‖ / g := by
  set P := projection U with hP
  set Q := projection V with hQ
  set A' : E →L[𝕜] E := A ∘L P + ((c + g : ℝ) : 𝕜) • (1 - P) with hA'
  set B' : E →L[𝕜] E := B ∘L Q + ((c : ℝ) : 𝕜) • (1 - Q) with hB'
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E := P ∘L (A - B) ∘L Q with hY
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hAsa : IsSelfAdjoint A := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA
  have hBsa : IsSelfAdjoint B := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hcgsa : IsSelfAdjoint ((c + g : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hcsa : IsSelfAdjoint ((c : ℝ) : 𝕜) := isSelfAdjoint_iff.mpr (RCLike.conj_ofReal _)
  have hone : IsSelfAdjoint (1 : E →L[𝕜] E) := IsSelfAdjoint.one _
  -- commutations
  have hcommA : A ∘L P = P ∘L A := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (projection_apply_comm_of_reduces A U hU x).symm
  have hcommB : B ∘L Q = Q ∘L B := by
    ext x; simp only [ContinuousLinearMap.comp_apply]
    exact (projection_apply_comm_of_reduces B V hV x).symm
  -- self-adjointness of A', B'
  have hA'sa : IsSelfAdjoint A' := by
    have h1 : IsSelfAdjoint (A ∘L P) := (IsSelfAdjoint.commute_iff hAsa hPsa).mp hcommA
    have h2 : IsSelfAdjoint (((c + g : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - P)) := by
      rw [isSelfAdjoint_iff, star_smul, hcgsa.star_eq, (hone.sub hPsa).star_eq]
    exact hA' ▸ h1.add h2
  have hB'sa : IsSelfAdjoint B' := by
    have h1 : IsSelfAdjoint (B ∘L Q) := (IsSelfAdjoint.commute_iff hBsa hQsa).mp hcommB
    have h2 : IsSelfAdjoint (((c : ℝ) : 𝕜) • ((1 : E →L[𝕜] E) - Q)) := by
      rw [isSelfAdjoint_iff, star_smul, hcsa.star_eq, (hone.sub hQsa).star_eq]
    exact hB' ▸ h1.add h2
  have hA'sym : IsSelfAdjointOperator A' := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hA'sa
  have hB'sym : IsSelfAdjointOperator B' := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hB'sa
  -- coercivity of A'
  have hA'c : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A' x, x⟫_𝕜 := by
    intro x
    have hpx : P x ∈ U := U.starProjection_apply_mem x
    have hrest : x - P x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
    have hAxeq : A' x = A (P x) + ((c + g : ℝ) : 𝕜) • (x - P x) := by
      simp only [hA', add_apply, ContinuousLinearMap.comp_apply,
        smul_apply, sub_apply, one_apply_eq_self]
    have hre : RCLike.re ⟪A' x, x⟫_𝕜
        = RCLike.re ⟪A (P x), x⟫_𝕜 + (c + g) * RCLike.re ⟪x - P x, x⟫_𝕜 := by
      rw [hAxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪A (P x), x⟫_𝕜 = RCLike.re ⟪A (P x), P x⟫_𝕜 := by
      have hz : ⟪A (P x), x - P x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hU.1 _ hpx) hrest
      have : ⟪A (P x), x⟫_𝕜 = ⟪A (P x), P x⟫_𝕜 + ⟪A (P x), x - P x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [this, hz, add_zero]
    have h2 : RCLike.re ⟪x - P x, x⟫_𝕜 = ‖x - P x‖ ^ 2 := by
      have hz : ⟪x - P x, P x⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hpx hrest
      have : ⟪x - P x, x⟫_𝕜 = ⟪x - P x, x - P x⟫_𝕜 := by
        have h' : ⟪x - P x, x⟫_𝕜 = ⟪x - P x, P x⟫_𝕜 + ⟪x - P x, x - P x⟫_𝕜 := by
          rw [← inner_add_right]; congr 1; abel
        rw [h', hz, zero_add]
      rw [this, inner_self_eq_norm_sq]
    have hpyth : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
      have h0 : RCLike.re ⟪P x, x - P x⟫_𝕜 = 0 := by
        rw [Submodule.inner_right_of_mem_orthogonal hpx hrest]; simp
      have hns := norm_add_sq (𝕜 := 𝕜) (P x) (x - P x)
      rw [show P x + (x - P x) = x by abel, h0] at hns
      linarith
    rw [hre, h1, h2, hpyth]
    nlinarith [hUc (P x) hpx]
  -- upper bound for B'
  have hB'c : ∀ x, RCLike.re ⟪B' x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
    intro x
    have hqx : Q x ∈ V := V.starProjection_apply_mem x
    have hrest : x - Q x ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
    have hBxeq : B' x = B (Q x) + ((c : ℝ) : 𝕜) • (x - Q x) := by
      simp only [hB', add_apply, ContinuousLinearMap.comp_apply,
        smul_apply, sub_apply, one_apply_eq_self]
    have hre : RCLike.re ⟪B' x, x⟫_𝕜
        = RCLike.re ⟪B (Q x), x⟫_𝕜 + c * RCLike.re ⟪x - Q x, x⟫_𝕜 := by
      rw [hBxeq, inner_add_left, inner_smul_left, RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul]
    have h1 : RCLike.re ⟪B (Q x), x⟫_𝕜 = RCLike.re ⟪B (Q x), Q x⟫_𝕜 := by
      have hz : ⟪B (Q x), x - Q x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hV.1 _ hqx) hrest
      have : ⟪B (Q x), x⟫_𝕜 = ⟪B (Q x), Q x⟫_𝕜 + ⟪B (Q x), x - Q x⟫_𝕜 := by
        rw [← inner_add_right]; congr 1; abel
      rw [this, hz, add_zero]
    have h2 : RCLike.re ⟪x - Q x, x⟫_𝕜 = ‖x - Q x‖ ^ 2 := by
      have hz : ⟪x - Q x, Q x⟫_𝕜 = 0 := Submodule.inner_left_of_mem_orthogonal hqx hrest
      have : ⟪x - Q x, x⟫_𝕜 = ⟪x - Q x, x - Q x⟫_𝕜 := by
        have h' : ⟪x - Q x, x⟫_𝕜 = ⟪x - Q x, Q x⟫_𝕜 + ⟪x - Q x, x - Q x⟫_𝕜 := by
          rw [← inner_add_right]; congr 1; abel
        rw [h', hz, zero_add]
      rw [this, inner_self_eq_norm_sq]
    have hpyth : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
      have h0 : RCLike.re ⟪Q x, x - Q x⟫_𝕜 = 0 := by
        rw [Submodule.inner_right_of_mem_orthogonal hqx hrest]; simp
      have hns := norm_add_sq (𝕜 := 𝕜) (Q x) (x - Q x)
      rw [show Q x + (x - Q x) = x by abel, h0] at hns
      linarith
    rw [hre, h1, h2, hpyth]
    nlinarith [hVc (Q x) hqx]
  -- Sylvester relation A' X - X B' = Y
  have hsylv : sylvesterOperator A' B' X = Y := by
    show A' ∘L X - X ∘L B' = Y
    ext x
    have hQxV : Q x ∈ V := V.starProjection_apply_mem x
    have hPP : P (P (Q x)) = P (Q x) :=
      U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem (Q x))
    have hQrest : Q (x - Q x) = 0 := by
      have hQQ : Q (Q x) = Q x := V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
      rw [map_sub, hQQ, sub_self]
    have hQBQ : Q (B (Q x)) = B (Q x) := V.starProjection_eq_self_iff.mpr (hV.1 _ hQxV)
    have hAP : A (P (Q x)) = P (A (Q x)) :=
      (projection_apply_comm_of_reduces A U hU (Q x)).symm
    have hAX : (A' ∘L X) x = A (P (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hA', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, hPP, sub_self, smul_zero, add_zero]
    have hXB : (X ∘L B') x = P (B (Q x)) := by
      simp only [ContinuousLinearMap.comp_apply, hX, hB', add_apply,
        smul_apply, sub_apply,
        one_apply_eq_self, map_add, map_smul, hQBQ, hQrest, map_zero, smul_zero, add_zero]
    have hYx : Y x = P (A (Q x)) - P (B (Q x)) := by
      simp only [hY, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    rw [sub_apply, hAX, hXB, hYx, hAP]
  -- norm bound
  have hYnorm : ‖Y‖ ≤ ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hc : ‖P ((A - B) (Q x))‖ ≤ ‖(A - B) (Q x)‖ := by
      rw [hP]; exact U.norm_starProjection_apply_le _
    calc ‖Y x‖ = ‖P ((A - B) (Q x))‖ := by simp only [hY, ContinuousLinearMap.comp_apply]
      _ ≤ ‖(A - B) (Q x)‖ := hc
      _ = ‖(B - A) (Q x)‖ := by rw [show A - B = -(B - A) by abel, neg_apply, norm_neg]
      _ ≤ ‖B - A‖ * ‖Q x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B - A‖ * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hQ]; exact V.norm_starProjection_apply_le x
  have hXbound : ‖X‖ ≤ ‖B - A‖ / g :=
    (norm_sylvester_le_of_coercive hA'sym hB'sym hg hA'c hB'c hsylv).trans (by gcongr)
  have hstar : star (Q ∘L P : E →L[𝕜] E) = P ∘L Q := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      hPsa.star_eq, hQsa.star_eq]
  have : ‖(Q ∘L P : E →L[𝕜] E)‖ = ‖X‖ := by rw [hX, ← hstar]; exact (norm_star _).symm
  calc ‖(projection V ∘L projection U : E →L[𝕜] E)‖ = ‖(Q ∘L P : E →L[𝕜] E)‖ := by rw [hP, hQ]
    _ = ‖X‖ := this
    _ ≤ ‖B - A‖ / g := hXbound


/-- Symmetric projector-difference form requiring both mixed gaps. -/
theorem sinTheta_symmetric
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d) :
    d * subspaceGap U V ≤ ‖B - A‖ := by
  have hdirUV := sinTheta_perturbation hA hB hU hV hd hUV
  have hdirVU := sinTheta_perturbation hB hA hV hU hd hVU
  rw [subspaceGap, Submodule.norm_starProjection_sub_eq_max U V,
    mul_max_of_nonneg _ hd.le]
  apply max_le
  · simpa [directedGap] using hdirUV
  · simpa [directedGap, norm_neg] using hdirVU

/-- General separated-spectrum form with the optimal universal `π / 2`
Sylvester constant. -/
theorem sinTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : HybridGap A B U V d) :
    d * directedGap U V ≤ (Real.pi / 2) * ‖B - A‖ := by
  let X : U →L[𝕜] Vᗮ :=
    (complementaryProjection V ∘L U.subtypeL).corestrict Vᗮ
  let C : U →L[𝕜] Vᗮ :=
    (complementaryProjection V ∘L (B - A) ∘L U.subtypeL).corestrict Vᗮ
  have hEq := directedPerturbation_sylvesterEquation hA hB hU hV
  have hsep : SpectraSeparated (B.restrictToOrthogonal hV) ⊤
      (A.restrict hU.1) ⊤ d :=
    hybridGap_restrictions hA hB hU hV hgap
  have hsol := norm_sylvester_le_of_generalSeparation
    (hB.restrictToOrthogonal hV) (hA.restrict hU.1) hd hsep hEq
  have hX : ‖X‖ = directedGap U V :=
    directedGap_eq_restrictedBlock_norm U V
  have hC : ‖C‖ ≤ ‖B - A‖ :=
    restricted_projection_sandwich_norm_le _ _ _
  simpa [hX] using hsol.trans (mul_le_mul_of_nonneg_left hC (by positivity))

/-- Canonical spectral-projection form. -/
theorem spectralProjection_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hAs : SpectrumIn A (spectralSubspace A s) (Set.Icc left right))
    (hBt : SpectrumIn B (spectralSubspace B t)ᗮ
      {x | x ≤ left - d ∨ right + d ≤ x})
    (hBs : SpectrumIn B (spectralSubspace B t) (Set.Icc left' right'))
    (hAt : SpectrumIn A (spectralSubspace A s)ᗮ
      {x | x ≤ left' - d ∨ right' + d ≤ x}) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤
      ‖B - A‖ := by
  let U := spectralSubspace A s
  let V := spectralSubspace B t
  have hredA := reduces_spectralSubspace A hA s hs
  have hredB := reduces_spectralSubspace B hB t ht
  have hUV : IntervalExteriorSeparated A U B Vᗮ left right d :=
    ⟨hAs, hBt⟩
  have hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d :=
    ⟨hBs, hAt⟩
  have h := sinTheta_symmetric hA hB hredA hredB hd hUV hVU
  simpa [U, V, subspaceGap, projection_spectralSubspace_eq] using h

/-- The interval/exterior divided-difference double operator integral sends the
perturbation to the difference of the two selected spectral projections. -/
theorem projectionDifference_ideal_intervalExterior
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : I.mem (B - A)) :
    I.mem (projection U - projection V) ∧
      d * I.gauge (projection U - projection V) ≤ I.gauge (B - A) := by
  let k : ℝ → ℝ → ℝ := intervalExteriorProjectionDividedDifference
    left right left' right' d
  have hk : ∀ λ μ, spectralMixedSupport U V λ μ →
      |k λ μ| ≤ d⁻¹ :=
    intervalExteriorProjectionDividedDifference_bound hd hUV hVU
  have hformula : projection U - projection V =
      doubleOperatorIntegral A B k (B - A) :=
    projectionDifference_doubleOperatorIntegral hA hB hU hV hUV hVU
  have hdoi := symmetricIdeal_doubleOperatorIntegral_bound I hA hB k hk hmem
  rw [hformula]
  refine ⟨hdoi.1, ?_⟩
  have := hdoi.2
  have hd0 : 0 ≤ d := hd.le
  calc
    d * I.gauge (doubleOperatorIntegral A B k (B - A))
        ≤ d * (d⁻¹ * I.gauge (B - A)) :=
          mul_le_mul_of_nonneg_left this hd0
    _ = I.gauge (B - A) := by field_simp [ne_of_gt hd]

/-- Symmetric-ideal `sin Θ` theorem. -/
theorem ideal_sinTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : I.mem (B - A)) :
    I.mem (sinAngleOperator U V) ∧
      d * I.gauge (sinAngleOperator U V) ≤ I.gauge (B - A) := by
  have hdiff := projectionDifference_ideal_intervalExterior
    I hA hB hU hV hd hUV hVU hmem
  have habs := I.operatorAbsoluteValue_mem_and_gauge_eq hdiff.1
  simpa [sinAngleOperator, habs.2] using
    And.intro habs.1 hdiff.2

end DavisKahanExt
end ForMathlib
