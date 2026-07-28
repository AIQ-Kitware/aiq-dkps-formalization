/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.FiniteDimensional.DirectRotation.Majorization
import DavisKahan.FiniteDimensional.SinTheta.UnitarilyInvariant
import ForTauCeti.Analysis.InnerProductSpace.MoorePenroseInverse

/-!
# Finite direct rotation: trigonometric and extremal formulas

This module completes the finite Section 4 route from the canonical polar
intertwiner.  It deliberately does not reintroduce the historical
`FiniteTwoProjection` namespace: the trigonometric factorization is obtained
from the positive cosine `|S|`, the full sine `|P_U-P_V|`, and the
Moore--Penrose initial projection.

The valid extremal endpoints are the full displacement-square majorization
and the unrestricted source-restricted displacement theorem.  The historical
real `pi / 3` claim for the full displacement is false when principal-angle
multiplicity spaces are mixed by the competitor; it is not reintroduced.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The global positive cosine of the direct rotation.  Unlike
`cosAngleOperator = |P_VP_U|`, this operator is the identity on the common
orthogonal complement and therefore participates in the full-space formula
`R = C + J S`. -/
noncomputable def directRotationCosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.abs (canonicalIntertwiner U V)

/-- The partial complex structure on the nonzero-angle space.  Total
Moore--Penrose inversion makes it zero on the zero-angle space. -/
noncomputable def angleComplexStructure (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →ₗ[𝕜] E :=
  ((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
    FiniteDimensional.moorePenroseInverse (sinAngleOperator U V)

/-- The zero-angle space of the full sine is contained in the zero space of
`R-C`. -/
theorem ker_sinAngleOperator_le_ker_directRotation_sub_cosine
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (sinAngleOperator U V).ker ≤
      ((directRotation U V hacute).toLinearMap - directRotationCosine U V).ker := by
  intro x hx
  have hxD : x ∈ (projection U - projection V).ker := by
    simpa [sinAngleOperator, ker_abs] using hx
  have hproj : projection U x = projection V x :=
    sub_eq_zero.mp (by
      simpa [LinearMap.sub_apply] using LinearMap.mem_ker.mp hxD)
  have hR := directRotation_apply_eq_self_of_projection_eq U V hacute hproj
  have hC := abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hproj
  apply LinearMap.mem_ker.mpr
  have hRx : polarFactor (canonicalIntertwiner U V) x = x := hR
  simp [LinearMap.sub_apply, directRotationCosine, hRx, hC]

/-- Reversing the pair gives the inverse rotation. -/
theorem directRotation_symm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotation V U hacute.symm = (directRotation U V hacute).symm := by
  have hstar : (canonicalIntertwiner U V).adjoint = canonicalIntertwiner V U :=
    adjoint_canonicalIntertwiner U V
  have hpolar := polarFactor_adjoint_of_isUnit
    (canonicalIntertwiner_isUnit_of_acute U V hacute)
  apply LinearIsometryEquiv.ext
  intro x
  have h1 : directRotation V U hacute.symm x
      = polarFactor (canonicalIntertwiner V U) x := rfl
  have h2 : (directRotation U V hacute).symm x
      = LinearMap.adjoint (polarFactor (canonicalIntertwiner U V)) x :=
    (LinearMap.congr_fun
      (directRotation U V hacute).adjoint_toLinearMap_eq_symm x).symm
  rw [h1, h2, ← hstar, hpolar]

/-- The direct rotation is the identity on the common and doubly-orthogonal
parts. -/
theorem directRotation_apply_eq_self_of_mem_common (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : E}
    (hx : x ∈ U ⊓ V ⊔ (U ⊔ V)ᗮ) :
    directRotation U V hacute x = x := by
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hx
  have hproj0 : projection U x₀ = projection V x₀ := by
    simp [projection_apply_of_mem hx₀.1, projection_apply_of_mem hx₀.2]
  have hx₁U : x₁ ∈ Uᗮ := Submodule.orthogonal_le le_sup_left hx₁
  have hx₁V : x₁ ∈ Vᗮ := Submodule.orthogonal_le le_sup_right hx₁
  have hproj1 : projection U x₁ = projection V x₁ := by
    simp [projection_apply_of_mem_orthogonal hx₁U,
      projection_apply_of_mem_orthogonal hx₁V]
  rw [map_add,
    directRotation_apply_eq_self_of_projection_eq U V hacute hproj0,
    directRotation_apply_eq_self_of_projection_eq U V hacute hproj1]

/-- The direct rotation is definitionally the polar factor of the canonical
intertwiner. -/
theorem directRotation_eq_polarFactor (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      polarFactor (canonicalIntertwiner U V) :=
  rfl

/-- Full-space trigonometric factorization `R = C + J sin Θ`. -/
theorem directRotation_eq_cos_add_J_sin (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      directRotationCosine U V +
        angleComplexStructure U V hacute ∘ₗ sinAngleOperator U V := by
  let A := sinAngleOperator U V
  let B := (directRotation U V hacute).toLinearMap - directRotationCosine U V
  have hfactor : B ∘ₗ FiniteDimensional.moorePenroseInverse A ∘ₗ A = B :=
    FiniteDimensional.comp_moorePenroseInverse_comp_eq_of_ker_le A B
      (ker_sinAngleOperator_le_ker_directRotation_sub_cosine U V hacute)
  ext x
  have hx := LinearMap.congr_fun hfactor x
  simpa [A, B, angleComplexStructure, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply] using congrArg
      (fun y => directRotationCosine U V x + y) hx.symm

/-- The direct rotation commutes with the global positive cosine. -/
theorem directRotation_comm_cosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ directRotationCosine U V =
      directRotationCosine U V ∘ₗ (directRotation U V hacute).toLinearMap := by
  simpa [directRotationCosine] using
    directRotation_comm_abs_canonicalIntertwiner U V hacute

/-- Polar uniqueness: any unitary-positive factorization of the canonical
intertwiner uses the direct rotation as its unitary factor. -/
theorem directRotation_unique (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E) (H : E →ₗ[𝕜] E)
    (hH : H.IsPositive)
    (hdecomp : canonicalIntertwiner U V = W.toLinearMap ∘ₗ H) :
    W = directRotation U V hacute := by
  have hpolar := polarFactor_eq_of_isUnit_eq_comp_positive
    (canonicalIntertwiner_isUnit_of_acute U V hacute) W hH hdecomp
  apply LinearIsometryEquiv.ext
  intro x
  exact LinearMap.congr_fun hpolar.symm x

/-- Davis--Kahan Proposition 4.3: the direct rotation minimizes every UI norm
of the positive displacement square. -/
theorem directRotation_minimizes_displacementSquare_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (displacementSquare (directRotation U V hacute).toLinearMap) ≤
      N (displacementSquare W.toLinearMap) :=
  directRotation_displacementSquare_uiNorm N U V hacute W hmap

/-- Davis--Kahan Corollary 4.1: the direct rotation minimizes every unitarily
invariant norm of the displacement restricted to the source subspace.

This is the sound replacement for the historical full-displacement `pi / 3`
candidate: what is dropped is the *largest-angle threshold*, not every angle
condition.  `IsAcute` remains, and is not a weakening of the result — it is the
hypothesis under which `directRotation U V hacute` exists at all
(`IsAcute` says no principal angle is a quarter turn, in either direction; see
`DavisKahan.FiniteDimensional.IsAcute`). -/
theorem directRotation_minimizes_restrictedDisplacement_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U) ≤
      N ((LinearMap.id - W.toLinearMap) ∘ₗ projection U) :=
  uiNorm_restrictedDisplacement_le N U V hacute W hmap

/-- Pointwise maximum-displacement extremality, obtained from Proposition 4.3
with the operator norm and `‖A⋆A‖ = ‖A‖²`. -/
theorem directRotation_minimizes_max_displacement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    ‖((directRotation U V hacute).toLinearMap - LinearMap.id).toContinuousLinearMap‖ ≤
      ‖(W.toLinearMap - LinearMap.id).toContinuousLinearMap‖ := by
  have h := directRotation_minimizes_displacementSquare_uiNorm
    (UnitarilyInvariantNorm.opNorm 𝕜 E) U V hacute W hmap
  have key : ∀ X : E →ₗ[𝕜] E,
      UnitarilyInvariantNorm.opNorm 𝕜 E (displacementSquare X) =
        ‖(X - LinearMap.id).toContinuousLinearMap‖ ^ 2 := by
    intro X
    haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    have hD : displacementSquare X =
        LinearMap.adjoint (LinearMap.id - X) ∘ₗ (LinearMap.id - X) := by
      simp only [displacementSquare, map_sub, LinearMap.adjoint_id]
    have hCLM : (LinearMap.adjoint (LinearMap.id - X) ∘ₗ
          (LinearMap.id - X)).toContinuousLinearMap =
        ContinuousLinearMap.adjoint
            (LinearMap.id - X).toContinuousLinearMap ∘L
          (LinearMap.id - X).toContinuousLinearMap := by
      ext x
      rfl
    have hneg : (X - LinearMap.id).toContinuousLinearMap
        = -((LinearMap.id - X).toContinuousLinearMap) := by
      ext x
      simp
    show ‖(displacementSquare X).toContinuousLinearMap‖ = _
    rw [hD, hCLM, ContinuousLinearMap.norm_adjoint_comp_self, hneg, norm_neg, sq]
  rw [key, key] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Orthonormal-basis displacement energy is minimized by the direct rotation.
This is Proposition 4.2, equivalently the nuclear-norm specialization of the
positive displacement-square majorization. -/
theorem directRotation_minimizes_sum_sq_basis_angles
    {n : ℕ} (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    ∑ i, ‖directRotation U V hacute (b i) - b i‖ ^ 2 ≤
      ∑ i, ‖W (b i) - b i‖ ^ 2 := by
  have hn : n = finrank 𝕜 E := by
    simpa using (Module.finrank_eq_card_basis b.toBasis).symm
  subst hn
  let R := (directRotation U V hacute).toLinearMap
  let AR := LinearMap.id - R
  let AW := LinearMap.id - W.toLinearMap
  let N : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.nuclear
      (𝕜 := 𝕜) (E := E) (F := E)).toSquare
  have h := directRotation_minimizes_displacementSquare_uiNorm
    N U V hacute W hmap
  have hdispR : displacementSquare R = AR.adjoint ∘ₗ AR := by
    ext x
    simp [displacementSquare, AR, R, map_sub,
      LinearMap.adjoint_id, LinearMap.comp_apply]
  have hdispW : displacementSquare W.toLinearMap = AW.adjoint ∘ₗ AW := by
    ext x
    simp [displacementSquare, AW, map_sub,
      LinearMap.adjoint_id, LinearMap.comp_apply]
  change RectangularUnitarilyInvariantNorm.nuclear (displacementSquare R) ≤
    RectangularUnitarilyInvariantNorm.nuclear
      (displacementSquare W.toLinearMap) at h
  rw [hdispR, hdispW,
    RectangularUnitarilyInvariantNorm.nuclear_adjoint_comp_self_eq_sum_sq_norm AR b,
    RectangularUnitarilyInvariantNorm.nuclear_adjoint_comp_self_eq_sum_sq_norm AW b] at h
  have h' : (∑ i, ‖b i - directRotation U V hacute (b i)‖ ^ 2)
      ≤ ∑ i, ‖b i - W (b i)‖ ^ 2 := h
  simpa [norm_sub_rev] using h'

end DavisKahanTheory
end TauCeti