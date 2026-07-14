/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTwoTheta
import ForMathlib.Analysis.InnerProductSpace.IntertwiningUnitary

/-!
# Direct rotation of two subspaces

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 4 and 12.
* Davis--Kahan (1970), Sections 3--4.
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, Section
  "Canonical matching of subspaces".

This is the basis-independent completion of the existing
`OrthoProjFamily.intertwiningUnitary`.  The direct rotation is the canonical
unitary carrying one subspace to the other.  Its extremal properties are stated
with the qualifications in Davis--Kahan Section 4: the positive displacement
square is minimized for every UI norm, whereas `‖I-W‖` itself needs an angle
restriction for arbitrary UI norms.
-/


/-! ## Remaining construction plan

Construct the finite direct rotation from the polar decomposition of
`P_V P_U + P_Vperp P_Uperp`.  Define `angleComplexStructure` on each nontrivial
principal two-plane by the quarter-turn matrix and zero on common summands.
Prove mapping, intertwining, and inverse symmetry from polar-factor uniqueness;
then identify the cosine/sine and exponential formulas by checking each
principal block.  The bounded experimental theorem should eventually supply
all geometry except finite matrix normalization.
-/


/-! ## Weak-agent execution plan: direct rotation

### A. Use the existing finite polar-decomposition API

Let

`S := projection V ∘ₗ projection U +
      complementaryProjection V ∘ₗ complementaryProjection U`.

Prove from `hacute` that `ker S = ⊥`; in finite dimension this gives
bijectivity and `IsUnit S`.  Then define `directRotation` with
`polarUnitaryEquiv hS`, not by choosing principal planes.  The repository
already provides `polarFactor`, `polarUnitaryEquiv`,
`polarUnitaryEquiv_coe`, and `polar_decomposition_unitary` in
`PolarDecomposition.lean`.  This immediately makes
`directRotation_eq_polarFactor` a short simp theorem.

Before constructing the bundled isometry, prove algebraically:

* `S ∘ₗ projection U = projection V ∘ₗ S`;
* `S.adjoint ∘ₗ S` commutes with `projection U`;
* therefore `abs S` and its inverse commute with `projection U`.

The last step should use the positive functional calculus already developed
for `abs`; avoid a basis calculation.  Combining these facts gives the
intertwining theorem, and range equality follows from it plus bijectivity.

### B. Derive symmetry and the square identity from polar uniqueness

Compute `S(V,U) = S(U,V).adjoint`.  Use uniqueness of the polar factor of an
invertible operator to obtain `directRotation_symm`.  For the square identity,
first prove it on the generic two-projection block or derive the algebraic
identity for the polar factors of `S` and `S.adjoint`; verify the reflection
order on the explicit planar model before generalizing.

### C. Defer `angleComplexStructure`

Do not block the basic direct rotation on a full operator-angle calculus.
First prove the polar construction, mapping, symmetry, common-part identity,
and square identity.  Define `angleComplexStructure` later from

`J := (W - W.adjoint) * (2 sinAngleOperator U V)⁻¹`

on the support of the sine operator, extended by zero on its kernel, or from
the principal-plane decomposition.  The trigonometric formula and commutation
with the angle operator are downstream of this definition.

### D. Extremality

For arbitrary UI norms, reduce to singular values on each principal plane.
Create a single finite majorization lemma comparing the displacement-square
singular values of the direct rotation with those of any competing unitary.
Use `UnitarilyInvariantNorm.apply_le_of_kyFanSum_le` afterward.  The
`π/3`-restricted unsquared displacement result should reuse a second scalar
block inequality; do not infer it from the unconditional squared theorem.

### E. Bundle/coercion traps

Keep `S` and polar calculations as `LinearMap`s.  Convert to
`LinearIsometryEquiv` once.  When using a bundled isometry in an equality,
state an intermediate equality of its `toLinearMap`; extensional equality of
the bundles can then use the appropriate ext theorem.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Two-block specialization of the canonical intertwining unitary -/

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
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  · intro x y
    change ⟪U.starProjection x, y⟫_𝕜 = ⟪x, U.starProjection y⟫_𝕜
    exact U.inner_starProjection_left_eq_right x y

/-- The complete orthogonal projection family for `E = U ⊕ Uᗮ`. -/
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
      simpa [twoBlockProjectionFamily, complementaryProjection, projection] using hx
    intro hVperp
    have hxV : x ∈ V := by
      have hxVV : x ∈ (Vᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hVperp
      simpa using hxVV
    have hU : U.starProjection x = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff U).mpr hxUperp
    exact hne (hacute.2 x hxV hU)

/-- The partial complex structure on the nontrivial two-subspace planes. -/
noncomputable def angleComplexStructure (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E := by
  sorry

/-- Canonical direct rotation from `U` to `V`. -/
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

/-- The direct rotation maps `U` onto `V`.
-/
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

/-- Intertwining identity `W P_U = P_V W`.
-/
theorem directRotation_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ projection U =
      projection V ∘ₗ (directRotation U V hacute).toLinearMap := by
  exact directRotation_comp_projection_aux U V hacute

/-- Reversing the pair gives the inverse rotation.

Lean proof route for a weaker agent:

1. Preferred route: specialize the corresponding bounded theorem from the experimental direct-rotation module through the finite continuous-linear-map/isometry equivalence bridge
2. prove only the bundle/coercion normalization locally.
-/
theorem directRotation_symm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotation V U hacute.symm = (directRotation U V hacute).symm := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end DavisKahanTheory
end ForMathlib
