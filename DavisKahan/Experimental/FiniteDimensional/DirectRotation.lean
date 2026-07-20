/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.DirectRotation.Basic
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.TanTheta
import DavisKahan.Experimental.FiniteDimensional.Core.AngleOperators

/-!
# Experimental direct-rotation formulas and extremality

The canonical finite direct rotation, its subspace mapping theorem, and its
projection-intertwining identity are stable in
`DavisKahan.FiniteDimensional.DirectRotation.Basic`.

This module retains the unfinished operator-angle formula, inverse and square
identities, uniqueness characterization, and the qualified extremal results
from Section 4 of Davis--Kahan (1970).
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The partial complex structure on the nontrivial two-subspace planes. -/
noncomputable def angleComplexStructure (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  FiniteTwoProjection.angleComplexStructure U V

/-- Reversing the pair gives the inverse rotation.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from the experimental direct-rotation module through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_symm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotation V U hacute.symm = (directRotation U V hacute).symm := by
  classical
  let S := projection V ∘ₗ projection U +
    complementaryProjection V ∘ₗ complementaryProjection U
  let Srev := projection U ∘ₗ projection V +
    complementaryProjection U ∘ₗ complementaryProjection V
  have hSstar : LinearMap.adjoint S = Srev := by
    ext x
    simp [S, Srev, LinearMap.adjoint_add, LinearMap.adjoint_comp,
      projection_selfAdjoint, complementaryProjection_selfAdjoint]
  have hunit : IsUnit S := canonicalIntertwiner_isUnit_of_acute U V hacute
  have hpolar : polarFactor Srev = (polarFactor S).adjoint := by
    rw [← hSstar]
    exact polarFactor_adjoint_of_isUnit hunit
  apply LinearIsometryEquiv.ext
  intro x
  simpa [directRotation, S, Srev, hpolar] using congrArg (fun T : E →ₗ[𝕜] E => T x) hpolar

/-- The direct rotation is the identity on the common and doubly-orthogonal
parts.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from the experimental direct-rotation module through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_apply_eq_self_of_mem_common (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : E}
    (hx : x ∈ U ⊓ V ⊔ (U ⊔ V)ᗮ) :
    directRotation U V hacute x = x := by
  classical
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hx
  have hx₀U : x₀ ∈ U := hx₀.1
  have hx₀V : x₀ ∈ V := hx₀.2
  have hx₁U : x₁ ∈ Uᗮ := by
    intro u hu
    exact hx₁ (Submodule.mem_sup_left hu)
  have hx₁V : x₁ ∈ Vᗮ := by
    intro v hv
    exact hx₁ (Submodule.mem_sup_right hv)
  have hS0 :
      (projection V ∘ₗ projection U +
        complementaryProjection V ∘ₗ complementaryProjection U) x₀ = x₀ := by
    simp [projection_apply_of_mem hx₀U, projection_apply_of_mem hx₀V,
      complementaryProjection_apply_of_mem_orthogonal hx₀U,
      complementaryProjection_apply_of_mem_orthogonal hx₀V]
  have hS1 :
      (projection V ∘ₗ projection U +
        complementaryProjection V ∘ₗ complementaryProjection U) x₁ = x₁ := by
    simp [projection_apply_of_mem_orthogonal hx₁U,
      projection_apply_of_mem_orthogonal hx₁V,
      complementaryProjection_apply_of_mem hx₁U,
      complementaryProjection_apply_of_mem hx₁V]
  have hpolar0 := polarFactor_apply_eq_self_of_apply_eq_self hS0
  have hpolar1 := polarFactor_apply_eq_self_of_apply_eq_self hS1
  simpa [directRotation, map_add] using congrArg₂ (· + ·) hpolar0 hpolar1

/-- Polar-factor construction from the two projections.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from the experimental direct-rotation module through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_eq_polarFactor (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      polarFactor (projection V ∘ₗ projection U +
        complementaryProjection V ∘ₗ complementaryProjection U) := by
  rfl

/-- Trigonometric formula `W = cos Θ + J sin Θ`.

Lean proof route for a weaker agent:

1. Specialize the experimental polar-factor direct rotation, then use the finite two-projection functional calculus to identify the cosine, sine, and complex-structure factors.
2. This should follow after the experimental operator-angle foundation.
-/
theorem directRotation_eq_cos_add_J_sin (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      cosAngleOperator U V + angleComplexStructure U V ∘ₗ sinAngleOperator U V := by
  classical
  let D := FiniteTwoProjection.orthogonalDecomposition U V
  apply D.ext
  · intro x hx
    simp [directRotation_apply_eq_self_of_mem_common U V hacute hx,
      cosAngleOperator_apply_common, sinAngleOperator_apply_common]
  · intro j x hx
    obtain ⟨θ, hθ, e₀, e₁, he⟩ := D.principalPlane_data j hx
    have hθacute : θ < Real.pi / 2 := principalAngle_lt_pi_div_two_of_acute hacute hθ
    have hW :
        D.toPrincipalPlane j ((directRotation U V hacute) x) =
          ![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] *ᵥ
            D.toPrincipalPlane j x :=
      directRotation_principalPlane_matrix U V hacute j x
    have hC :
        D.toPrincipalPlane j (cosAngleOperator U V x) =
          Real.cos θ • D.toPrincipalPlane j x :=
      cosAngleOperator_principalPlane U V j x
    have hS :
        D.toPrincipalPlane j (sinAngleOperator U V x) =
          Real.sin θ • D.toPrincipalPlane j x :=
      sinAngleOperator_principalPlane U V j x
    have hJ :
        D.toPrincipalPlane j (angleComplexStructure U V x) =
          ![0, -1; 1, 0] *ᵥ D.toPrincipalPlane j x :=
      FiniteTwoProjection.angleComplexStructure_principalPlane U V j x
    apply D.toPrincipalPlane_injective j
    simpa [LinearMap.add_apply, LinearMap.comp_apply, hC, hS, hJ,
      Matrix.mulVec_add, Matrix.mulVec_smul] using hW

/-- Square of the direct rotation is the product of the two reflections.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from the experimental direct-rotation module through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_sq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ
        (directRotation U V hacute).toLinearMap =
      V.reflection.toLinearMap ∘ₗ U.reflection.toLinearMap := by
  classical
  rw [directRotation_eq_cos_add_J_sin U V hacute]
  let C := cosAngleOperator U V
  let S := sinAngleOperator U V
  let J := angleComplexStructure U V
  have hCS : C ∘ₗ S = S ∘ₗ C := cos_sin_angle_comm U V
  have hJC : J ∘ₗ C = C ∘ₗ J := angleComplexStructure_comm_cos U V
  have hJS : J ∘ₗ S = S ∘ₗ J := angleComplexStructure_comm_sin U V
  have hJ2 : J ∘ₗ J = -principalPlaneProjection U V :=
    angleComplexStructure_sq U V
  have hpyth : C ∘ₗ C + S ∘ₗ S = LinearMap.id :=
    cos_sq_add_sin_sq U V
  have hdouble :
      V.reflection.toLinearMap ∘ₗ U.reflection.toLinearMap =
        (C ∘ₗ C - S ∘ₗ S) + (2 : 𝕜) • (J ∘ₗ S ∘ₗ C) :=
    reflectionProduct_doubleAngle_formula U V
  calc
    (C + J ∘ₗ S) ∘ₗ (C + J ∘ₗ S)
        = (C ∘ₗ C - S ∘ₗ S) + (2 : 𝕜) • (J ∘ₗ S ∘ₗ C) := by
            ext x
            simp [LinearMap.add_apply, LinearMap.comp_apply, hCS, hJC, hJS,
              hJ2, hpyth]
            module
    _ = V.reflection.toLinearMap ∘ₗ U.reflection.toLinearMap := hdouble.symm

/-- The angle operator commutes with the direct rotation.

Lean proof route for a weaker agent:

1. Specialize the experimental polar-factor direct rotation, then use the finite two-projection functional calculus to identify the cosine, sine, and complex-structure factors.
2. This should follow after the experimental operator-angle foundation.
-/
theorem directRotation_comm_angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ angleOperator U V =
      angleOperator U V ∘ₗ (directRotation U V hacute).toLinearMap := by
  rw [directRotation_eq_cos_add_J_sin U V hacute]
  have hC := angleOperator_comm_cos U V
  have hS := angleOperator_comm_sin U V
  have hJ := angleOperator_comm_angleComplexStructure U V
  calc
    (cosAngleOperator U V + angleComplexStructure U V ∘ₗ sinAngleOperator U V) ∘ₗ
        angleOperator U V
        = cosAngleOperator U V ∘ₗ angleOperator U V +
            angleComplexStructure U V ∘ₗ
              (sinAngleOperator U V ∘ₗ angleOperator U V) := by
              ext x; simp [LinearMap.comp_apply, LinearMap.add_apply]
    _ = angleOperator U V ∘ₗ cosAngleOperator U V +
          (angleOperator U V ∘ₗ angleComplexStructure U V) ∘ₗ
            sinAngleOperator U V := by rw [hC, hS, hJ]; simp [LinearMap.comp_assoc]
    _ = angleOperator U V ∘ₗ
          (cosAngleOperator U V +
            angleComplexStructure U V ∘ₗ sinAngleOperator U V) := by
              ext x; simp [LinearMap.comp_apply, LinearMap.add_apply]

/-- Uniqueness among acute rotations with the correct intertwining and positive
real part.

Lean proof route for a weaker agent:

1. Use `hsq` to identify `W` and `directRotation U V hacute` as square roots of the same
   unitary product of reflections.
2. Use `hre` to select the positive-real-part square-root branch on each principal two-plane.
3. On the common and doubly orthogonal summands, use `hmap` and the branch condition to show
   both operators are the identity.
4. Finish by extensionality over the principal-plane orthogonal decomposition.

Signature audit: The reflection-square hypothesis removes the counterexamples obtained by
rotating the common complement while still mapping `U` onto `V`.
-/
theorem directRotation_unique (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V)
    (hsq : W.toLinearMap ∘ₗ W.toLinearMap =
      V.reflection.toLinearMap ∘ₗ U.reflection.toLinearMap)
    (hre : ∀ x, 0 ≤ RCLike.re ⟪W x, x⟫_𝕜) :
    W = directRotation U V hacute := by
  classical
  let D := FiniteTwoProjection.orthogonalDecomposition U V
  apply LinearIsometryEquiv.ext
  intro x
  obtain ⟨xtriv, hxtriv, xp, hxp, rfl⟩ := D.decompose x
  have htrivW : W xtriv = xtriv := by
    have hsq_triv : W (W xtriv) = xtriv := by
      simpa [LinearMap.comp_apply, reflection_apply_common hxtriv] using
        congrArg (fun T : E →ₗ[𝕜] E => T xtriv) hsq
    have hre_triv := hre (W xtriv - xtriv)
    have hnorm : ‖W xtriv - xtriv‖ ^ 2 = 0 := by
      rw [norm_sub_sq_eq, W.norm_map, hsq_triv]
      simpa [RCLike.re_add, RCLike.re_sub] using hre_triv
    exact sub_eq_zero.mp (norm_sq_eq_zero.mp hnorm)
  have htrivR := directRotation_apply_eq_self_of_mem_common U V hacute hxtriv
  have hp : W xp = directRotation U V hacute xp := by
    obtain ⟨j, θ, hθ, y, hy, rfl⟩ := D.mem_principalPlanes.mp hxp
    have hθacute : 0 ≤ θ ∧ θ < Real.pi / 2 :=
      principalAngle_range_of_acute hacute hθ
    have hWblock := congrArg
      (fun T : E →ₗ[𝕜] E => D.principalPlaneRestriction j T)
      hsq
    have hRblock := congrArg
      (fun T : E →ₗ[𝕜] E => D.principalPlaneRestriction j T)
      (directRotation_sq U V hacute)
    have hreblock : ∀ z, 0 ≤ RCLike.re
        ⟪D.principalPlaneRestriction j W.toLinearMap z, z⟫_𝕜 := by
      intro z
      simpa using hre (D.fromPrincipalPlane j z)
    have hroot : D.principalPlaneRestriction j W.toLinearMap =
        D.principalPlaneRestriction j (directRotation U V hacute).toLinearMap :=
      planar_unitary_squareRoot_unique hθacute
        (by simpa [hWblock, hRblock]) hreblock
    exact D.principalPlaneRestriction_apply_eq hroot y
  simpa [map_add, htrivW, htrivR, hp]

/-- Davis--Kahan Proposition 4.3: for every UI norm the direct rotation
minimizes the positive displacement square `(I-W⋆)(I-W)`.  This is the
unconditional all-UI extremal statement.

Lean proof route for a weaker agent:

1. Use the finite principal-plane decomposition and Davis--Kahan Section 4 scalar inequalities on each `2 × 2` block, then apply symmetric-gauge/Fan dominance.
2. The experimental operator-norm minimizer supplies geometry but not the arbitrary finite UI conclusion.
-/
theorem directRotation_minimizes_displacementSquare_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (directRotation U V hacute).symm.toLinearMap) ∘ₗ
        (LinearMap.id - (directRotation U V hacute).toLinearMap)) ≤
      N ((LinearMap.id - W.symm.toLinearMap) ∘ₗ
        (LinearMap.id - W.toLinearMap)) := by
  classical
  let A := (LinearMap.id - (directRotation U V hacute).symm.toLinearMap) ∘ₗ
    (LinearMap.id - (directRotation U V hacute).toLinearMap)
  let B := (LinearMap.id - W.symm.toLinearMap) ∘ₗ
    (LinearMap.id - W.toLinearMap)
  have hApos : A.IsPositive := displacementSquare_positive _
  have hBpos : B.IsPositive := displacementSquare_positive _
  have hKyFan : ∀ k, kyFanEigenvalueSum 𝕜 A k ≤ kyFanEigenvalueSum 𝕜 B k := by
    intro k
    let D := FiniteTwoProjection.orthogonalDecomposition U V
    refine D.kyFan_le_of_blockwise ?_ ?_
    · intro x hx
      simp [A, B, directRotation_apply_eq_self_of_mem_common U V hacute hx,
        displacementSquare_apply]
      exact norm_sq_nonneg _
    · intro j
      obtain ⟨θ, hθ⟩ := D.principalAngle_data j
      have htransport := D.unitaryTransport_block W hmap j
      exact planar_displacementSquare_eigenvalue_majorization θ htransport
  exact N.le_of_positive_kyFan_dominance hApos hBpos hKyFan

/-- Davis--Kahan Proposition 4.4: if the largest principal angle is at most
`π/3`, the direct rotation minimizes `N (I-W)` for every UI norm.  Without
this restriction the statement is false for some UI norms.

Lean proof route for a weaker agent:

1. Use the finite principal-plane decomposition and Davis--Kahan Section 4 scalar inequalities on each `2 × 2` block, then apply symmetric-gauge/Fan dominance.
2. The experimental operator-norm minimizer supplies geometry but not the arbitrary finite UI conclusion.
-/
theorem directRotation_minimizes_uiNorm_of_largestAngle_le_pi_div_three
    (N : UnitarilyInvariantNorm 𝕜 E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hangle : principalAngles U V 0 ≤ Real.pi / 3)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  classical
  have hall : ∀ i, principalAngles U V i ≤ Real.pi / 3 := by
    intro i
    exact (principalAngles_antitone U V i).trans hangle
  have hsing : ∀ k,
      kyFanSingularValueSum 𝕜
          (LinearMap.id - (directRotation U V hacute).toLinearMap) k ≤
        kyFanSingularValueSum 𝕜 (LinearMap.id - W.toLinearMap) k := by
    intro k
    let D := FiniteTwoProjection.orthogonalDecomposition U V
    refine D.kyFanSingular_le_of_blockwise ?_ ?_
    · intro x hx
      simp [directRotation_apply_eq_self_of_mem_common U V hacute hx]
    · intro j
      obtain ⟨θ, hθ⟩ := D.principalAngle_data j
      exact planar_displacement_singular_majorization_of_angle_le_pi_div_three
        (hall j) (D.unitaryTransport_block W hmap j)
  exact N.le_of_kyFan_singular_dominance hsing

/-- Pointwise maximum-displacement extremal property.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from the experimental direct-rotation module through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_minimizes_max_displacement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    ‖((directRotation U V hacute).toLinearMap - LinearMap.id).toContinuousLinearMap‖ ≤
      ‖(W.toLinearMap - LinearMap.id).toContinuousLinearMap‖ := by
  classical
  let D := FiniteTwoProjection.orthogonalDecomposition U V
  rw [ContinuousLinearMap.opNorm_eq_sSup_unit_sphere,
    ContinuousLinearMap.opNorm_eq_sSup_unit_sphere]
  refine csSup_le ?_ ?_
  · exact ⟨0, by simp⟩
  · rintro r ⟨x, hxunit, rfl⟩
    obtain ⟨xtriv, hxtriv, xp, hxp, rfl⟩ := D.decompose x
    have horth := D.trivial_orthogonal_principal hxtriv hxp
    have hRtriv := directRotation_apply_eq_self_of_mem_common U V hacute hxtriv
    have hplane := D.max_displacement_principalPlane_le W hmap hacute xp
    calc
      ‖directRotation U V hacute (xtriv + xp) - (xtriv + xp)‖
          = ‖directRotation U V hacute xp - xp‖ := by simp [map_add, hRtriv]
      _ ≤ ‖W (xtriv + xp) - (xtriv + xp)‖ := hplane
      _ ≤ ‖(W.toLinearMap - LinearMap.id).toContinuousLinearMap‖ := by
        simpa [sub_apply, hxunit] using
          (W.toLinearMap - LinearMap.id).toContinuousLinearMap.le_opNorm (xtriv + xp)

/-- Orthonormal-basis extremal property from Davis--Kahan Proposition 4.2.

Lean proof route for a weaker agent:

1. Use the finite principal-plane decomposition and Davis--Kahan Section 4 scalar inequalities on each `2 × 2` block, then apply symmetric-gauge/Fan dominance.
2. The experimental operator-norm minimizer supplies geometry but not the arbitrary finite UI conclusion.
-/
theorem directRotation_minimizes_sum_sq_basis_angles
    {n : ℕ} (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    ∑ i, ‖directRotation U V hacute (b i) - b i‖ ^ 2 ≤
      ∑ i, ‖W (b i) - b i‖ ^ 2 := by
  classical
  have htrace := directRotation_minimizes_displacementSquare_uiNorm
    (UnitarilyInvariantNorm.traceNorm 𝕜 E) U V hacute W hmap
  have hleft :
      (UnitarilyInvariantNorm.traceNorm 𝕜 E)
        ((LinearMap.id - (directRotation U V hacute).symm.toLinearMap) ∘ₗ
          (LinearMap.id - (directRotation U V hacute).toLinearMap)) =
        ∑ i, ‖directRotation U V hacute (b i) - b i‖ ^ 2 := by
    rw [traceNorm_positive_eq_trace]
    simpa [trace_eq_sum_orthonormalBasis, inner_sub_left, inner_sub_right,
      LinearIsometryEquiv.inner_map_map]
  have hright :
      (UnitarilyInvariantNorm.traceNorm 𝕜 E)
        ((LinearMap.id - W.symm.toLinearMap) ∘ₗ
          (LinearMap.id - W.toLinearMap)) =
        ∑ i, ‖W (b i) - b i‖ ^ 2 := by
    rw [traceNorm_positive_eq_trace]
    simpa [trace_eq_sum_orthonormalBasis, inner_sub_left, inner_sub_right,
      LinearIsometryEquiv.inner_map_map]
  simpa [hleft, hright] using htrace

end DavisKahanTheory
end ForMathlib
