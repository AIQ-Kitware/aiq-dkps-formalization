/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.FiniteDimensional.Core.AngleGeometry
import ForMathlib.Analysis.InnerProductSpace.PolarDecomposition
import ForMathlib.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus

/-!
# Canonical finite direct rotation

For an acute pair of finite-dimensional subspaces, the canonical direct
rotation is the unitary polar factor of

`S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`.

This global polar definition is equivalent to the blockwise Davis
intertwining-unitary construction, but exposes the identities needed in Part
III without a fictional principal-plane API.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

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

private theorem projection_comp_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    projection U ∘ₗ projection U = projection U := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)

private theorem complementaryProjection_comp_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    complementaryProjection U ∘ₗ complementaryProjection U =
      complementaryProjection U := by
  simpa [complementaryProjection] using projection_comp_self (𝕜 := 𝕜) Uᗮ

/-- The canonical two-projection intertwiner. -/
noncomputable def canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection V ∘ₗ projection U +
    complementaryProjection V ∘ₗ complementaryProjection U

/-- The ordered product of the target and source reflections. -/
noncomputable def reflectionProduct (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E ≃ₗᵢ[𝕜] E :=
  U.reflection.trans V.reflection

@[simp] theorem reflectionProduct_apply (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    reflectionProduct U V x = V.reflection (U.reflection x) := rfl

/-- `2S = I + J_V J_U`. -/
theorem two_smul_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (2 : 𝕜) • canonicalIntertwiner U V =
      LinearMap.id + (reflectionProduct U V).toLinearMap := by
  ext x
  simp only [canonicalIntertwiner, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply, reflectionProduct_apply,
    Submodule.reflection_apply]
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_orthogonal_val]
  module

/-- The adjoint reverses the ordered pair. -/
theorem adjoint_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (canonicalIntertwiner U V).adjoint = canonicalIntertwiner V U := by
  rw [canonicalIntertwiner, canonicalIntertwiner, LinearMap.adjoint_add,
    LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    projection_selfAdjoint, projection_selfAdjoint,
    complementaryProjection_selfAdjoint, complementaryProjection_selfAdjoint]

/-- Gram operator of the canonical intertwiner, displayed in source blocks. -/
theorem canonicalIntertwiner_adjoint_comp_self (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V =
      (projection U ∘ₗ projection V ∘ₗ projection U) +
        (complementaryProjection U ∘ₗ complementaryProjection V ∘ₗ
          complementaryProjection U) := by
  rw [adjoint_canonicalIntertwiner, canonicalIntertwiner, canonicalIntertwiner]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [map_add, map_add]
  simp only [LinearMap.comp_apply]
  rw [projection_comp_self, complementaryProjection_comp_self,
    projection_comp_complementaryProjection,
    complementaryProjection_comp_projection]
  simp

/-- The Gram operator is block diagonal relative to `U`. -/
theorem projection_comm_canonicalIntertwiner_gram (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection U ∘ₗ ((canonicalIntertwiner U V).adjoint ∘ₗ
      canonicalIntertwiner U V) =
      ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) ∘ₗ
        projection U := by
  rw [canonicalIntertwiner_adjoint_comp_self]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [projection_comp_self, projection_comp_complementaryProjection,
    complementaryProjection_comp_projection]
  simp

/-- The canonical intertwiner sends source blocks to target blocks. -/
theorem canonicalIntertwiner_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V ∘ₗ projection U =
      projection V ∘ₗ canonicalIntertwiner U V := by
  ext x
  simp only [canonicalIntertwiner, LinearMap.comp_apply, LinearMap.add_apply,
    map_add]
  rw [projection_comp_self, complementaryProjection_comp_projection,
    projection_comp_self, projection_comp_complementaryProjection]
  simp

/-- Acuteness makes the canonical intertwiner injective. -/
theorem canonicalIntertwiner_injective_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Function.Injective (canonicalIntertwiner U V) := by
  rw [LinearMap.injective_iff_map_eq_zero]
  intro x hx
  have hU : projection U x = 0 := by
    have hVproj := congrArg (projection V) hx
    have hcross : projection V (complementaryProjection V
        (complementaryProjection U x)) = 0 := by
      change V.starProjection (Vᗮ.starProjection
        (Uᗮ.starProjection x)) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact Vᗮ.starProjection_apply_mem _
    have hzero : projection V (projection U x) = 0 := by
      simpa [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
        hcross] using hVproj
    exact hacute.1 (projection U x) (U.starProjection_apply_mem x) hzero
  have hUperp : complementaryProjection U x = 0 := by
    have hVperp := congrArg (complementaryProjection V) hx
    have hcross : complementaryProjection V (projection V (projection U x)) = 0 := by
      change Vᗮ.starProjection (V.starProjection (U.starProjection x)) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact V.le_orthogonal_orthogonal (V.starProjection_apply_mem _)
    have hzero : complementaryProjection V (complementaryProjection U x) = 0 := by
      simpa [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
        hcross] using hVperp
    have hyV : complementaryProjection U x ∈ V := by
      have : complementaryProjection U x ∈ (Vᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hzero
      simpa using this
    have hyU : projection U (complementaryProjection U x) = 0 := by
      change U.starProjection (Uᗮ.starProjection x) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact Uᗮ.starProjection_apply_mem x
    exact hacute.2 (complementaryProjection U x) hyV hyU
  calc
    x = projection U x + complementaryProjection U x := by
      symm
      exact U.starProjection_add_starProjection_orthogonal x
    _ = 0 := by rw [hU, hUperp, add_zero]

/-- Acuteness makes the canonical intertwiner invertible. -/
theorem canonicalIntertwiner_isUnit_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : IsUnit (canonicalIntertwiner U V) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact canonicalIntertwiner_injective_of_acute U V hacute

/-- The canonical intertwiner is normal for an acute pair. -/
theorem canonicalIntertwiner_normal_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V =
      canonicalIntertwiner U V ∘ₗ (canonicalIntertwiner U V).adjoint := by
  let R := reflectionProduct U V
  have hS := two_smul_canonicalIntertwiner U V
  have hSrev := two_smul_canonicalIntertwiner V U
  have hRrev : (reflectionProduct V U).toLinearMap = R.symm.toLinearMap := by
    ext x
    simp [R, reflectionProduct]
  rw [← hRrev] at hSrev
  have hstar := adjoint_canonicalIntertwiner U V
  rw [hstar]
  apply LinearMap.ext
  intro x
  have h1 := LinearMap.congr_fun hS x
  have h2 := LinearMap.congr_fun hSrev x
  have hfour : (4 : 𝕜) ≠ 0 := by norm_num
  apply (smul_left_cancel₀ hfour)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, map_add]
  rw [h1, h2]
  simp [R]
  module

/-- The positive modulus of the intertwiner commutes with the source
projection. -/
theorem projection_comm_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection U ∘ₗ ForMathlib.abs (canonicalIntertwiner U V) =
      ForMathlib.abs (canonicalIntertwiner U V) ∘ₗ projection U := by
  exact FiniteDimensional.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V))
    (projection_comm_canonicalIntertwiner_gram U V)


/-- If the two projections agree on a vector, the canonical intertwiner fixes
that vector. -/
theorem canonicalIntertwiner_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : projection U x = projection V x) :
    canonicalIntertwiner U V x = x := by
  simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
    complementaryProjection, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hx]
  have hp : projection V (projection V x) = projection V x :=
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  rw [hp]
  module

/-- The adjoint canonical intertwiner also fixes a vector on which the two
projections agree. -/
theorem adjoint_canonicalIntertwiner_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : projection U x = projection V x) :
    (canonicalIntertwiner U V).adjoint x = x := by
  rw [adjoint_canonicalIntertwiner]
  exact canonicalIntertwiner_apply_eq_self_of_projection_eq V U hx.symm

/-- The positive cosine `|S|` fixes every zero-angle direction. -/
theorem abs_canonicalIntertwiner_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : projection U x = projection V x) :
    ForMathlib.abs (canonicalIntertwiner U V) x = x := by
  let S := canonicalIntertwiner U V
  have hS : S x = x :=
    canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hSstar : S.adjoint x = x :=
    adjoint_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hsq : (S.adjoint ∘ₗ S) x = ((1 : ℝ) : 𝕜) • x := by
    simp [LinearMap.comp_apply, hS, hSstar]
  exact (LinearMap.isPositive_adjoint_comp_self S).sqrt_apply_eq_of_sq
    (by norm_num) hsq

/-- The canonical direct rotation from `U` to `V`, defined as the unitary polar
factor of the canonical intertwiner. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E ≃ₗᵢ[𝕜] E :=
  polarUnitaryEquiv (canonicalIntertwiner_isUnit_of_acute U V hacute)

@[simp] theorem directRotation_toLinearMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      polarFactor (canonicalIntertwiner U V) := rfl


/-- The direct rotation fixes every zero-angle direction. -/
theorem directRotation_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : E}
    (hx : projection U x = projection V x) :
    directRotation U V hacute x = x := by
  let S := canonicalIntertwiner U V
  have hS : S x = x :=
    canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hC : ForMathlib.abs S x = x :=
    abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hpolar := LinearMap.congr_fun (polar_decomposition S) x
  simpa [directRotation, LinearMap.comp_apply, hS, hC] using hpolar.symm

/-- The canonical direct rotation commutes with its positive cosine factor. -/
theorem directRotation_comm_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ
        ForMathlib.abs (canonicalIntertwiner U V) =
      ForMathlib.abs (canonicalIntertwiner U V) ∘ₗ
        (directRotation U V hacute).toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := ForMathlib.abs S
  let R := (directRotation U V hacute).toLinearMap
  have hSC : S ∘ₗ C = C ∘ₗ S :=
    abs_comm_of_normal (canonicalIntertwiner_normal_of_acute U V hacute)
  have hCinj : Function.Injective C := by
    rw [← LinearMap.ker_eq_bot, ker_abs,
      LinearMap.isUnit_iff_ker_eq_bot.mp
        (canonicalIntertwiner_isUnit_of_acute U V hacute)]
  have hCsurj : Function.Surjective C :=
    LinearMap.injective_iff_surjective.mp hCinj
  have hdecomp : S = R ∘ₗ C := by
    simpa [R, directRotation, S, C] using polar_decomposition S
  rw [hdecomp] at hSC
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hCsurj x
  exact LinearMap.congr_fun hSC y

/-- The intertwining identity `W P_U = P_V W`. -/
theorem directRotation_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ projection U =
      projection V ∘ₗ (directRotation U V hacute).toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := ForMathlib.abs S
  let W := (directRotation U V hacute).toLinearMap
  have hpolar : S = W ∘ₗ C := by
    simpa [S, C, W, directRotation] using
      polar_decomposition_of_isUnit (canonicalIntertwiner_isUnit_of_acute U V hacute)
  have hCP := projection_comm_abs_canonicalIntertwiner U V
  have hSP := canonicalIntertwiner_comp_projection U V
  have hCsurj : Function.Surjective C := by
    have hCin : Function.Injective C := by
      rw [← LinearMap.ker_eq_bot, ker_abs,
        LinearMap.isUnit_iff_ker_eq_bot.mp
          (canonicalIntertwiner_isUnit_of_acute U V hacute)]
    exact LinearMap.injective_iff_surjective.mp hCin
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hCsurj x
  have hCPy := LinearMap.congr_fun hCP y
  have hSPy := LinearMap.congr_fun hSP y
  have hpolar_y := LinearMap.congr_fun hpolar y
  have hpolar_Py := LinearMap.congr_fun hpolar (projection U y)
  calc
    W (projection U (C y)) = W (C (projection U y)) := by
      rw [show projection U (C y) = C (projection U y) by
        simpa [LinearMap.comp_apply] using hCPy]
    _ = S (projection U y) := by
      simpa [LinearMap.comp_apply] using hpolar_Py.symm
    _ = projection V (S y) := by
      simpa [LinearMap.comp_apply] using hSPy
    _ = projection V (W (C y)) := by rw [← hpolar_y]


/-- The canonical intertwiner is the reflection product times its adjoint. -/
theorem canonicalIntertwiner_eq_reflectionProduct_comp_adjoint
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V =
      (reflectionProduct U V).toLinearMap ∘ₗ
        (canonicalIntertwiner U V).adjoint := by
  have hS := two_smul_canonicalIntertwiner U V
  have hSrev := two_smul_canonicalIntertwiner V U
  have hstar := adjoint_canonicalIntertwiner U V
  have hRrev : (reflectionProduct V U).toLinearMap =
      (reflectionProduct U V).symm.toLinearMap := by
    ext x
    simp [reflectionProduct]
  rw [hstar, hRrev] at hSrev
  apply LinearMap.ext
  intro x
  have htwo : (2 : 𝕜) ≠ 0 := by norm_num
  apply (smul_left_cancel₀ htwo)
  have h1 := LinearMap.congr_fun hS x
  have h2 := LinearMap.congr_fun hSrev x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    LinearMap.add_apply, LinearMap.id_apply] at h1 h2 ⊢
  rw [h1, h2]
  simp

/-- The reflection product commutes with the Gram operator of the canonical
intertwiner. -/
theorem reflectionProduct_comm_canonicalIntertwiner_gram
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (reflectionProduct U V).toLinearMap ∘ₗ
        ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) =
      ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) ∘ₗ
        (reflectionProduct U V).toLinearMap := by
  have hS := two_smul_canonicalIntertwiner U V
  have hSrev := two_smul_canonicalIntertwiner V U
  have hRrev : (reflectionProduct V U).toLinearMap =
      (reflectionProduct U V).symm.toLinearMap := by
    ext x
    simp [reflectionProduct]
  rw [hRrev] at hSrev
  apply LinearMap.ext
  intro x
  have hscale : (8 : 𝕜) ≠ 0 := by norm_num
  apply (smul_left_cancel₀ hscale)
  have h1 := LinearMap.congr_fun hS x
  have h2 := LinearMap.congr_fun hSrev x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, map_add,
    LinearMap.add_apply, LinearMap.id_apply] at h1 h2 ⊢
  rw [h1, h2]
  simp
  module

/-- The reflection product commutes with the positive modulus of the canonical
intertwiner. -/
theorem reflectionProduct_comm_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (reflectionProduct U V).toLinearMap ∘ₗ
        ForMathlib.abs (canonicalIntertwiner U V) =
      ForMathlib.abs (canonicalIntertwiner U V) ∘ₗ
        (reflectionProduct U V).toLinearMap := by
  exact FiniteDimensional.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V))
    (reflectionProduct_comm_canonicalIntertwiner_gram U V)

/-- The square of the canonical direct rotation is the ordered product of the
reflections. -/
theorem directRotation_sq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ
        (directRotation U V hacute).toLinearMap =
      (reflectionProduct U V).toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := ForMathlib.abs S
  let W := (directRotation U V hacute).toLinearMap
  let R := (reflectionProduct U V).toLinearMap
  have hpolar : S = W ∘ₗ C := by
    simpa [S, C, W, directRotation] using
      polar_decomposition_of_isUnit
        (canonicalIntertwiner_isUnit_of_acute U V hacute)
  have hstar : S.adjoint = C ∘ₗ W.adjoint := by
    rw [hpolar, LinearMap.adjoint_comp, (isPositive_abs S).adjoint_eq]
  have hRSstar : S = R ∘ₗ S.adjoint := by
    simpa [S, R] using
      canonicalIntertwiner_eq_reflectionProduct_comp_adjoint U V
  have hRC : R ∘ₗ C = C ∘ₗ R := by
    simpa [S, C, R] using
      reflectionProduct_comm_abs_canonicalIntertwiner U V
  have hCsurj : Function.Surjective C := by
    have hCin : Function.Injective C := by
      rw [← LinearMap.ker_eq_bot, ker_abs,
        LinearMap.isUnit_iff_ker_eq_bot.mp
          (canonicalIntertwiner_isUnit_of_acute U V hacute)]
    exact LinearMap.injective_iff_surjective.mp hCin
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hCsurj x
  have hpolar_y := LinearMap.congr_fun hpolar y
  have hRS_y := LinearMap.congr_fun hRSstar y
  have hstar_y := LinearMap.congr_fun hstar y
  have hRC_y := LinearMap.congr_fun hRC (W.adjoint y)
  have hWWstar : W (W.adjoint y) = y := by
    change directRotation U V hacute ((directRotation U V hacute).symm y) = y
    simp [W]
  calc
    W (W (C y)) = W (S y) := by rw [← hpolar_y]
    _ = W (R (S.adjoint y)) := by rw [← hRS_y]
    _ = W (R (C (W.adjoint y))) := by rw [hstar_y]
    _ = W (C (R (W.adjoint y))) := by rw [← hRC_y]
    _ = S (R (W.adjoint y)) := by
      rw [show W (C (R (W.adjoint y))) = S (R (W.adjoint y)) by
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun hpolar (R (W.adjoint y))]
    _ = R (W (C (W.adjoint y))) := by
      have hnormal := canonicalIntertwiner_normal_of_acute U V hacute
      have hSC : S ∘ₗ C = C ∘ₗ S := by
        simpa [S, C] using abs_comm_of_normal hnormal.symm
      have hSR : S ∘ₗ R = R ∘ₗ S := by
        have htwo := two_smul_canonicalIntertwiner U V
        apply LinearMap.ext
        intro z
        have hz := LinearMap.congr_fun htwo z
        have hRz := LinearMap.congr_fun htwo (R z)
        simp only [LinearMap.smul_apply, LinearMap.add_apply,
          LinearMap.id_apply] at hz hRz
        have h2 : (2 : 𝕜) ≠ 0 := by norm_num
        apply (smul_left_cancel₀ h2)
        simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
        rw [hz, hRz]
        simp [R]
      rw [show S (R (W.adjoint y)) = R (S (W.adjoint y)) by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hSR (W.adjoint y)]
      rw [show S (W.adjoint y) = W (C (W.adjoint y)) by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hpolar (W.adjoint y)]
    _ = R (C y) := by rw [hWWstar]

/-- The positive modulus is the real part of the direct rotation. -/
theorem two_smul_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (2 : 𝕜) • ForMathlib.abs (canonicalIntertwiner U V) =
      (directRotation U V hacute).toLinearMap +
        (directRotation U V hacute).symm.toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := ForMathlib.abs S
  let W := (directRotation U V hacute).toLinearMap
  have hpolar : S = W ∘ₗ C := by
    simpa [S, C, W, directRotation] using
      polar_decomposition_of_isUnit
        (canonicalIntertwiner_isUnit_of_acute U V hacute)
  have htwo := two_smul_canonicalIntertwiner U V
  have hsq := directRotation_sq U V hacute
  have hWinj : Function.Injective W := by
    intro x y hxy
    change directRotation U V hacute x = directRotation U V hacute y at hxy
    exact (directRotation U V hacute).injective hxy
  apply LinearMap.ext
  intro x
  apply hWinj
  have hpolar_x := LinearMap.congr_fun hpolar x
  have htwo_x := LinearMap.congr_fun htwo x
  have hsq_x := LinearMap.congr_fun hsq x
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, W, C, S] at hpolar_x htwo_x hsq_x ⊢
  rw [map_smul, hpolar_x, htwo_x, hsq_x]
  simp

/-- The direct rotation maps `U` onto `V`. -/
theorem directRotation_map_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    U.map (directRotation U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro _ ⟨x, hxU, rfl⟩
    apply Submodule.starProjection_eq_self_iff.mp
    have h := LinearMap.congr_fun
      (directRotation_comp_projection U V hacute) x
    have hxproj : projection U x = x :=
      Submodule.starProjection_eq_self_iff.mpr hxU
    simpa [LinearMap.comp_apply, hxproj] using h.symm
  · intro y hyV
    refine ⟨(directRotation U V hacute).symm y, ?_, by simp⟩
    apply Submodule.starProjection_eq_self_iff.mp
    apply (directRotation U V hacute).injective
    have h := LinearMap.congr_fun
      (directRotation_comp_projection U V hacute)
      ((directRotation U V hacute).symm y)
    have hyproj : projection V y = y :=
      Submodule.starProjection_eq_self_iff.mpr hyV
    simpa [LinearMap.comp_apply, hyproj] using h

end DavisKahanTheory
end ForMathlib
