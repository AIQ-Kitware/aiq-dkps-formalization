/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.AngleGeometry
import ForMathlib.Analysis.InnerProductSpace.IntertwiningUnitary

/-!
# Canonical finite direct rotation: construction and intertwining

This module contains the proof-complete foundation of the Davis--Kahan direct
rotation.  For an acute pair of finite-dimensional subspaces, it specializes
the canonical polar-factor intertwining unitary for the two projection blocks
`U` and `U orthogonal`.

The resulting unitary maps `U` onto `V` and satisfies `W P_U = P_V W`.
Trigonometric formulas, the reflection-square identity, uniqueness, and the
extremal properties from the 1970 paper remain downstream developments and are
not imported here.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem projection_comp_complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    projection U ∘ₗ complementaryProjection U = 0 := by
  apply LinearMap.ext
  intro x
  change U.starProjection (Uᗮ.starProjection x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact Uᗮ.starProjection_apply_mem x

private theorem complementaryProjection_comp_projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    complementaryProjection U ∘ₗ projection U = 0 := by
  apply LinearMap.ext
  intro x
  change Uᗮ.starProjection (U.starProjection x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact U.le_orthogonal_orthogonal (U.starProjection_apply_mem x)

variable [FiniteDimensional 𝕜 E]

private theorem isStarProjection_projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsStarProjection (projection U) := by
  rw [LinearMap.isStarProjection_iff_isSymmetricProjection]
  constructor
  · apply LinearMap.ext
    intro x
    change U.starProjection (U.starProjection x) = U.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr
      (U.starProjection_apply_mem x)
  · intro x y
    change ⟪U.starProjection x, y⟫_𝕜 = ⟪x, U.starProjection y⟫_𝕜
    exact U.inner_starProjection_left_eq_right x y

/-- The complete orthogonal projection family for `E = U direct-sum U orthogonal`. -/
private noncomputable def twoBlockProjectionFamily (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : OrthoProjFamily 𝕜 E 2 where
  proj i := if i = 0 then projection U else complementaryProjection U
  isStarProjection' i := by
    fin_cases i
    · simpa using isStarProjection_projection (𝕜 := 𝕜) U
    · simpa [complementaryProjection] using
        isStarProjection_projection (𝕜 := 𝕜) Uᗮ
  orthogonal' j k hjk := by
    fin_cases j <;> fin_cases k
    · exact (hjk rfl).elim
    · simpa using projection_comp_complementaryProjection (𝕜 := 𝕜) U
    · simpa using complementaryProjection_comp_projection (𝕜 := 𝕜) U
    · exact (hjk rfl).elim
  complete' := by
    rw [Fin.sum_univ_two]
    apply LinearMap.ext
    intro x
    change U.starProjection x + Uᗮ.starProjection x = x
    rw [Submodule.starProjection_orthogonal_val]
    abel

private theorem twoBlockProjectionFamily_nonDegenerate
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (twoBlockProjectionFamily U).NonDegenerate (twoBlockProjectionFamily V) := by
  intro j x hx hne
  fin_cases j
  · change V.starProjection x ≠ 0
    have hxU : x ∈ U := by
      apply Submodule.starProjection_eq_self_iff.mp
      simpa [twoBlockProjectionFamily, projection] using hx
    intro hV
    exact hne (hacute.1 x hxU hV)
  · change Vᗮ.starProjection x ≠ 0
    have hxUperp : x ∈ Uᗮ := by
      apply Submodule.starProjection_eq_self_iff.mp
      simpa [twoBlockProjectionFamily, complementaryProjection, projection]
        using hx
    intro hVperp
    have hxV : x ∈ V := by
      have hxVV : x ∈ (Vᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hVperp
      simpa using hxVV
    have hU : U.starProjection x = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff U).mpr hxUperp
    exact hne (hacute.2 x hxV hU)

/-- The canonical direct rotation from `U` to `V`. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E ≃ₗᵢ[𝕜] E :=
  OrthoProjFamily.intertwiningUnitary
    (twoBlockProjectionFamily_nonDegenerate U V hacute)

private theorem directRotation_comp_projection_aux (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ projection U =
      projection V ∘ₗ (directRotation U V hacute).toLinearMap := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (OrthoProjFamily.intertwiningUnitary_comp_proj
      (twoBlockProjectionFamily_nonDegenerate U V hacute) (0 : Fin 2)) x
  simpa [directRotation, twoBlockProjectionFamily, LinearMap.comp_apply] using h

/-- The direct rotation maps `U` onto `V`. -/
theorem directRotation_map_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    U.map (directRotation U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro _ ⟨x, hxU, rfl⟩
    apply Submodule.starProjection_eq_self_iff.mp
    have h := LinearMap.congr_fun
      (directRotation_comp_projection_aux U V hacute) x
    have hxproj : projection U x = x := by
      change U.starProjection x = x
      exact Submodule.starProjection_eq_self_iff.mpr hxU
    simp only [LinearMap.comp_apply] at h
    rw [hxproj] at h
    change V.starProjection (directRotation U V hacute x) =
      directRotation U V hacute x
    simpa [projection] using h.symm
  · intro y hyV
    refine ⟨(directRotation U V hacute).symm y, ?_, by simp⟩
    apply Submodule.starProjection_eq_self_iff.mp
    apply (directRotation U V hacute).injective
    let W := directRotation U V hacute
    have h := LinearMap.congr_fun
      (directRotation_comp_projection_aux U V hacute) (W.symm y)
    have hyproj : projection V y = y := by
      change V.starProjection y = y
      exact Submodule.starProjection_eq_self_iff.mpr hyV
    have hleft : W (projection U (W.symm y)) = y := by
      calc
        W (projection U (W.symm y)) = projection V (W (W.symm y)) := by
          simpa [W, LinearMap.comp_apply] using h
        _ = projection V y := by rw [W.apply_symm_apply]
        _ = y := hyproj
    change W (U.starProjection (W.symm y)) = W (W.symm y)
    calc
      W (U.starProjection (W.symm y)) = W (projection U (W.symm y)) := rfl
      _ = y := hleft
      _ = W (W.symm y) := (W.apply_symm_apply y).symm

/-- The intertwining identity `W P_U = P_V W`. -/
theorem directRotation_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ projection U =
      projection V ∘ₗ (directRotation U V hacute).toLinearMap :=
  directRotation_comp_projection_aux U V hacute

end DavisKahanTheory
end ForMathlib
