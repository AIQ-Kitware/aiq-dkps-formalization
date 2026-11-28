/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import DavisKahan.InfiniteDimensional.Sylvester.Basic
public import ForTauCeti.Analysis.Normed.Operator.Restriction
public import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
public import DavisKahan.SpectralTheory.AbstractSpectrum
public import DavisKahan.SinTheta.SpectralBridge
import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Restricted blocks for the infinite-dimensional sine theorems

The rectangular residual and perturbation blocks use Mathlib's `codRestrict`
and `restrict` directly. Their Sylvester equations and spectral separation
properties feed the infinite-dimensional sine estimates.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

omit [CompleteSpace E] in
/-- The bounded-realization real spectrum used by the `sin Θ` interval/exterior
bridge coincides with the Banach-algebra real spectrum used by the abstract
separation predicates. -/
theorem boundedRealSpectrum_eq_realSpectrum (X : E →L[𝕜] E) :
    TauCeti.DavisKahan.ExactSinTheta.boundedRealSpectrum X =
      TauCeti.DavisKahan.Foundation.realSpectrum X := by
  ext lam
  change lam ∈ _root_.LinearPMap.realSpectrum
      (X.toLinearMap.toPMap (⊤ : Submodule 𝕜 E)) ↔
    (lam : 𝕜) ∈ spectrum 𝕜 X
  rw [_root_.LinearPMap.mem_realSpectrum_iff, X.spectrum_toPMap_top]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The rectangular projection--operator--inclusion block is contractive. -/
theorem restricted_projection_sandwich_norm_le
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] F) :
    ‖((Vᗮ.starProjection ∘L T ∘L U.subtypeL)).codRestrict Vᗮ
      (fun _x => Vᗮ.starProjection_apply_mem _)‖ ≤ ‖T‖ := by
  have h := ContinuousLinearMap.singularValue_orthogonalProjectionOnto_comp_comp_subtypeL_le
    Vᗮ U T 0
  rw [ContinuousLinearMap.singularValue_zero, ContinuousLinearMap.singularValue_zero] at h
  exact_mod_cast h

omit [CompleteSpace E] in
/-- The directed projection gap is the norm of the rectangular cross block. -/
theorem directedGap_eq_restrictedBlock_norm
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
      (fun _x => Vᗮ.starProjection_apply_mem _)‖ = U.directedProjectionGap V := by
  have hrange : U.subtypeL.range = U := by
    ext x
    simp
  let : U.subtypeL.range.HasOrthogonalProjection :=
    hrange.symm ▸ (inferInstance : U.HasOrthogonalProjection)
  have h := V.norm_starProjection_orthogonal_comp (X := U.subtypeL)
    (AddMonoidHomClass.isometry_iff_norm U.subtypeL |>.2 fun _ => rfl)
  rw [Submodule.directedProjectionGap_def, Submodule.starProjection_congr hrange] at h
  rw [ContinuousLinearMap.opNorm_codRestrict_eq (Vᗮ.starProjection ∘L U.subtypeL) Vᗮ
    (fun _ => Vᗮ.starProjection_apply_mem _), Submodule.directedProjectionGap_def]
  exact h

omit [CompleteSpace E] [CompleteSpace F] in
/-- The directed residual block satisfies the restricted Sylvester equation. -/
theorem directedResidual_sylvesterEquation
    {A : E →L[𝕜] E} (_hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A)
    {X : F →L[𝕜] E} {M : F →L[𝕜] F} :
    ContinuousLinearMap.sylvester (A.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      _).mp hU.orthogonal_mem_invtSubmodule)) M
      (((Uᗮ.starProjection ∘L X)).codRestrict Uᗮ (fun _x => Uᗮ.starProjection_apply_mem _)) =
      ((Uᗮ.starProjection ∘L A.sylvester M X)).codRestrict Uᗮ
        (fun _x => Uᗮ.starProjection_apply_mem _) := by
  simp only [ContinuousLinearMap.sylvester_apply]
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun
    (hU.sylvester_starProjection_orthogonal_comp X.toLinearMap M.toLinearMap) x

omit [CompleteSpace E] in
/-- The directed perturbation block satisfies its restricted Sylvester
equation. -/
theorem directedPerturbation_sylvesterEquation
    {A B : E →L[𝕜] E}
    (_hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B) :
    ContinuousLinearMap.sylvester (B.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      _).mp hV.orthogonal_mem_invtSubmodule))
      (A.restrict hU.mem_invtSubmodule)
      (((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _)) =
      ((Vᗮ.starProjection ∘L (B - A) ∘L U.subtypeL)).codRestrict Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousLinearMap.sylvester_apply, sub_apply]
  have hVperp : Submodule.IsReducing Vᗮ B :=
    (LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule hB _).mpr
    hV.orthogonal_mem_invtSubmodule
  have hcomm := (show ∀ x, Vᗮ.starProjection (B x) = B (Vᗮ.starProjection x) from
      fun x => DFunLike.congr_fun ((Submodule.isReducing_coe_iff_commute_starProjection (U := Vᗮ)
        (A := B)).mp hVperp).eq x) (x : E)
  change B (Vᗮ.starProjection (x : E)) - Vᗮ.starProjection (A (x : E)) =
    Vᗮ.starProjection (B (x : E) - A (x : E))
  rw [map_sub, hcomm]

omit [CompleteSpace E] in
/-- Hybrid separation transports to the two actual restricted operators. -/
theorem hybridGap_restrictions
    {A B : E →L[𝕜] E}
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hA : A.IsSymmetric) (_hB : B.IsSymmetric)
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B)
    {d : ℝ} (hgap : HybridGap A B U V d) :
    SpectraSeparated (B.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      hV.orthogonal_mem_invtSubmodule)) ⊤
      (A.restrict hU.mem_invtSubmodule) ⊤ d := by
  refine ⟨by intro x hx; trivial, by intro x hx; trivial, ?_⟩
  intro b hb a ha
  have hb' : b ∈ restrictedSpectrum B Vᗮ := by
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum B Vᗮ
      hV.orthogonal_mem_invtSubmodule]
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_top] at hb
    exact hb
  have ha' : a ∈ restrictedSpectrum A U := by
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum A U
      hU.mem_invtSubmodule]
    rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_top] at ha
    exact ha
  simpa [abs_sub_comm] using hgap.2.2 a ha' b hb'

omit [CompleteSpace E] in
/-- Interval/exterior data transports to the restriction-level gap used by the
rectangular ideal theorem. -/
theorem intervalExteriorSeparated_restrictions
    {A B : E →L[𝕜] E}
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hA : A.IsSymmetric) (_hB : B.IsSymmetric)
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B)
    {left right d : ℝ}
    (hgap : IntervalExteriorSeparated A U B Vᗮ left right d) :
    TauCeti.DavisKahan.ExactSinTheta.IntervalExteriorGap
      (B.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
        hV.orthogonal_mem_invtSubmodule)) (A.restrict
        ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hU.mem_invtSubmodule))
      left right d := by
  right
  constructor
  · intro a ha
    have ha' : a ∈ restrictedSpectrum A U := by
      rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum A U
        hU.mem_invtSubmodule]
      rw [boundedRealSpectrum_eq_realSpectrum] at ha
      exact ha
    exact hgap.1.subset ha'
  · intro b hb
    have hb' : b ∈ restrictedSpectrum B Vᗮ := by
      rw [TauCeti.DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum B Vᗮ
        hV.orthogonal_mem_invtSubmodule]
      rw [boundedRealSpectrum_eq_realSpectrum] at hb
      exact hb
    exact hgap.2.subset hb'

end
end DavisKahanExt
end TauCeti
