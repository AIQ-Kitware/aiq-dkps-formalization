/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Sources.Davis1963.RotationEnergy
import DavisKahan.FiniteDimensional.Core.AngleGeometry
import DavisKahan.FiniteDimensional.Core.SpectralGap
import DavisKahan.FiniteDimensional.SinTheta.UnitarilyInvariant
import DavisKahan.Experimental.FiniteDimensional.Core.AngleOperators
import ForMathlib.Analysis.InnerProductSpace.TwoDimensionalSingularValues
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
# Sharpness and two-dimensional extremizers

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 13.
* Davis--Kahan (1970), Section 2 immediately after the four headline
  theorems, and the two-dimensional models used throughout Sections 6--8.
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, final sharp two-subspace
  section.

The constants in all four classic theorems are optimal.  Planar models must
respect the multiplicity convention of each angle operator: the one-sided
`sin (2Θ)` map has one nonzero singular value per principal plane, unlike the
symmetric off-diagonal perturbations used by the full-space tangent models.
-/


/-! ## Remaining construction plan

Use a single explicit planar model for every sharpness result.  Define the
reference and rotated one-dimensional subspaces in `EuclideanSpace R (Fin 2)`,
use a diagonal gapped operator, and form sine, tangent, and double-angle
perturbations by rotation/conjugation.  Prove the model projections and
singular values by extensional matrix calculation.  Each sharpness theorem
should then be a scalar trigonometric simplification, making failures at right
angles or quarter turns explicit rather than hidden in abstract geometry.
-/


/-! ## Weak-agent execution plan: explicit planar extremizers

Use the standard basis `e0`, `e1` of `EuclideanSpace 𝕜 (Fin 2)`.  Add local
abbreviations and simp lemmas before defining any operator:

* `uθ := cos θ • e0 + sin θ • e1`;
* `vθ := -sin θ • e0 + cos θ • e1`;
* orthonormality of `uθ,vθ`;
* `modelSubspace = 𝕜 ∙ e0` and
  `rotatedModelSubspace θ = 𝕜 ∙ uθ`.

Prefer `Submodule.span 𝕜 {e0}` and `Submodule.span 𝕜 {uθ}`.  Prove membership
and projection formulas once.  Then establish the `2 × 2` matrices of both
orthogonal projections by `LinearMap.ext` on `e0,e1`.

Define `modelGappedOperator a b` by
`e0 ↦ a • e0`, `e1 ↦ b • e1`.  For the `sin Θ` extremizer, use

`Rθ D Rθ⁻¹ - D`,

where `Rθ` sends `e0,e1` to `uθ,vθ`.  Its eigenvalues are
`±(b-a) sin θ`, so its operator norm is `(b-a) sin θ` on the stated angle
range.  Prove this by an explicit characteristic/eigenvector calculation or
by squaring the matrix to a scalar multiple of the identity.

Do not reuse that perturbation for the tangent and double-angle theorems.
For each remaining model, first write the exact equality conditions from the
corresponding block/Sylvester proof and solve the resulting scalar equations
for the four matrix entries.  Add a private theorem recording those entries,
then define the operator from the solved matrix.  This is safer than guessing a
rotation conjugate and discovering later that the zero-compression or
off-diagonal hypothesis fails.

For every model, prove in this order:

1. symmetry;
2. the required reducing and compression/off-diagonal hypotheses;
3. the exact internal or ordered gap;
4. the singular values of the perturbation;
5. the singular values of the angle operator;
6. the displayed UI-norm equality by unitary invariance and homogeneity.

For a `2 × 2` operator whose square is `r^2 • id`, use that identity to prove
both singular values are `|r|`; avoid expanding the general singular-value
definition repeatedly.  Keep trigonometric side conditions (`sin θ ≥ 0`,
`cos θ > 0`, `cos (2θ) > 0`) as named lemmas.

For direct sums, define the block operator by the decomposition
`Fin (2*m) ≃ Fin m × Fin 2` and transport `m` copies of the planar model.
Prove the singular-value multiset is repeated blockwise before invoking any UI
norm.  The scalar limit theorem should use existing `Real.tendsto_sin_div` and
`Real.tendsto_tan_div`-style lemmas if available; isolate it from the operator
sharpness development.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Plane (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)

/-- First standard basis vector of the planar model. -/
noncomputable def e0 : Plane 𝕜 := EuclideanSpace.single 0 1

/-- Second standard basis vector of the planar model. -/
noncomputable def e1 : Plane 𝕜 := EuclideanSpace.single 1 1

/-- Unit vector at angle `θ` from the coordinate line. -/
noncomputable def uθ (θ : ℝ) : Plane 𝕜 :=
  (Real.cos θ : 𝕜) • e0 + (Real.sin θ : 𝕜) • e1

/-- Coordinate line in the two-dimensional model. -/
noncomputable def modelSubspace : Submodule 𝕜 (Plane 𝕜) :=
  Submodule.span 𝕜 {e0}

/-- Line obtained by rotating the coordinate line by angle `θ`. -/
noncomputable def rotatedModelSubspace (θ : ℝ) : Submodule 𝕜 (Plane 𝕜) :=
  Submodule.span 𝕜 {uθ θ}

/-! Construct the following five operators as explicit `2 × 2` matrices in
the standard basis.  Start with `diag(a,b)`, conjugate by the planar rotation
for the `sin Θ` model, use the graph residual for `tan Θ`, and take the
reflection/off-diagonal parts for the double-angle models.  Matrix ext reduces
all later norm and equality claims to scalar trigonometric identities. -/

/-- Diagonal gapped operator used by the extremal examples. -/
noncomputable def modelGappedOperator (a b : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin (Matrix.diagonal ![(a : 𝕜), (b : 𝕜)])

/-- Planar rotation matrix by angle `θ` with real entries cast into `𝕜`. -/
noncomputable def planarRotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![(Real.cos θ : 𝕜), -(Real.sin θ : 𝕜);
     (Real.sin θ : 𝕜), (Real.cos θ : 𝕜)]

/-- Perturbation producing equality in the `sin Θ` model: the rotation
conjugate of the diagonal model minus the diagonal model,
`R(θ) diag(a,b) R(θ)ᵀ - diag(a,b)`.  Its entries are
`(b-a) sin²θ`, off-diagonal `(a-b) sinθ cosθ`, and `(a-b) sin²θ`, so its
square is `((b-a) sinθ)² • 1`. -/
noncomputable def modelSinThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  let d := b - a
  Matrix.toEuclideanLin
    !![((d * Real.sin θ ^ 2 : ℝ) : 𝕜),
       ((-d * Real.sin θ * Real.cos θ : ℝ) : 𝕜);
       ((-d * Real.sin θ * Real.cos θ : ℝ) : 𝕜),
       ((-d * Real.sin θ ^ 2 : ℝ) : 𝕜)]

/-- Perturbation/residual producing equality in the `tan Θ` model.

Construction route: use the graph residual of the rotated one-dimensional
subspace, with scaling chosen so the ordered Sylvester inequality is an
equality. -/
noncomputable def modelTanThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    ![![(0 : 𝕜), (((b-a) * Real.tan θ : ℝ) : 𝕜)],
      ![(((b-a) * Real.tan θ : ℝ) : 𝕜), (0 : 𝕜)]]

/-- Reflection-compatible perturbation producing equality in `sin (2 Θ)`:
the purely off-diagonal part of the rotated model, with entry
`(a-b) sinθ cosθ = ((a-b)/2) sin (2θ)` in both corners.  Being purely
off-diagonal it anticommutes with the reflection `diag(1,-1)` through the
model subspace. -/
noncomputable def modelSinTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![0, (((a - b) / 2 * Real.sin (2 * θ) : ℝ) : 𝕜);
       (((a - b) / 2 * Real.sin (2 * θ) : ℝ) : 𝕜), 0]

/-- Off-diagonal perturbation used by the `tan (2 Θ)` extremizer: the purely
off-diagonal symmetric perturbation with entry `((b-a)/2) tan (2θ)`, chosen so
the eigenvectors of `diag(a,b) + H` sit at angle `θ` from the coordinate axes
(the planar Riccati rotation law `tan (2θ) = 2h/(b-a)`). -/
noncomputable def modelTanTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    !![0, (((b - a) / 2 * Real.tan (2 * θ) : ℝ) : 𝕜);
       (((b - a) / 2 * Real.tan (2 * θ) : ℝ) : 𝕜), 0]


/-! ## Explicit planar geometry -/

@[simp] theorem norm_e0 : ‖e0 (𝕜 := 𝕜)‖ = 1 := by
  simp [e0]

@[simp] theorem norm_e1 : ‖e1 (𝕜 := 𝕜)‖ = 1 := by
  simp [e1]

@[simp] theorem inner_e0_e0 : ⟪e0 (𝕜 := 𝕜), e0⟫_𝕜 = 1 := by
  simp [e0, EuclideanSpace.inner_single_left]

@[simp] theorem inner_e1_e1 : ⟪e1 (𝕜 := 𝕜), e1⟫_𝕜 = 1 := by
  simp [e1, EuclideanSpace.inner_single_left]

@[simp] theorem inner_e0_e1 : ⟪e0 (𝕜 := 𝕜), e1⟫_𝕜 = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left]

@[simp] theorem inner_e1_e0 : ⟪e1 (𝕜 := 𝕜), e0⟫_𝕜 = 0 := by
  simp [e0, e1, EuclideanSpace.inner_single_left]

@[simp] theorem inner_uθ_e0 (θ : ℝ) :
    ⟪uθ (𝕜 := 𝕜) θ, e0⟫_𝕜 = (Real.cos θ : 𝕜) := by
  rw [uθ, inner_add_left, inner_smul_left, inner_smul_left,
    inner_e0_e0, inner_e1_e0, RCLike.conj_ofReal, RCLike.conj_ofReal]
  ring

@[simp] theorem inner_uθ_e1 (θ : ℝ) :
    ⟪uθ (𝕜 := 𝕜) θ, e1⟫_𝕜 = (Real.sin θ : 𝕜) := by
  rw [uθ, inner_add_left, inner_smul_left, inner_smul_left,
    inner_e0_e1, inner_e1_e1, RCLike.conj_ofReal, RCLike.conj_ofReal]
  ring

@[simp] theorem norm_uθ (θ : ℝ) : ‖uθ (𝕜 := 𝕜) θ‖ = 1 := by
  have hsq : ‖uθ (𝕜 := 𝕜) θ‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), uθ]
    simp only [inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, inner_e0_e0, inner_e1_e1, inner_e0_e1, inner_e1_e0,
      RCLike.conj_ofReal]
    -- the residual goal is `RCLike.re` of a real cast; `nlinarith` cannot see
    -- through the cast until it is pushed outwards
    simp only [mul_one, mul_zero, add_zero, zero_add, ← RCLike.ofReal_mul,
      ← RCLike.ofReal_add, RCLike.ofReal_re]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (uθ (𝕜 := 𝕜) θ)]

private theorem plane_eq_coord_smul_e0_add_coord_smul_e1 (x : Plane 𝕜) :
    x = x 0 • e0 (𝕜 := 𝕜) + x 1 • e1 (𝕜 := 𝕜) := by
  ext i
  fin_cases i <;> simp [e0, e1, PiLp.single_apply]

private theorem plane_linearMap_ext {F' : Type*} [AddCommMonoid F'] [Module 𝕜 F']
    {A B : Plane 𝕜 →ₗ[𝕜] F'}
    (h0 : A (e0 (𝕜 := 𝕜)) = B (e0 (𝕜 := 𝕜)))
    (h1 : A (e1 (𝕜 := 𝕜)) = B (e1 (𝕜 := 𝕜))) : A = B := by
  ext x
  rw [plane_eq_coord_smul_e0_add_coord_smul_e1 x]
  simp [h0, h1]

private theorem starProjection_span_singleton_apply_of_norm_one
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [FiniteDimensional 𝕜 E'] (v x : E') (hv : ‖v‖ = 1) :
    (Submodule.span 𝕜 {v}).starProjection x = ⟪v, x⟫_𝕜 • v := by
  classical
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span (by simp))
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        have hyv : y = v := by simpa using hy
        subst y
        simp [inner_sub_left, inner_smul_left,
          inner_self_eq_norm_sq, hv, inner_conj_symm]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

@[simp] theorem modelSubspace_starProjection_e0 :
    (modelSubspace (𝕜 := 𝕜)).starProjection (e0 (𝕜 := 𝕜)) = e0 := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (e0 (𝕜 := 𝕜)) (e0 (𝕜 := 𝕜)) norm_e0
  simpa [modelSubspace] using h

@[simp] theorem modelSubspace_starProjection_e1 :
    (modelSubspace (𝕜 := 𝕜)).starProjection (e1 (𝕜 := 𝕜)) = 0 := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (e0 (𝕜 := 𝕜)) (e1 (𝕜 := 𝕜)) norm_e0
  simpa [modelSubspace] using h

@[simp] theorem rotatedModelSubspace_starProjection_e0 (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (e0 (𝕜 := 𝕜)) =
      (Real.cos θ : 𝕜) • uθ θ := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (uθ (𝕜 := 𝕜) θ) (e0 (𝕜 := 𝕜)) (norm_uθ θ)
  simpa [rotatedModelSubspace] using h

@[simp] theorem rotatedModelSubspace_starProjection_e1 (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (e1 (𝕜 := 𝕜)) =
      (Real.sin θ : 𝕜) • uθ θ := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (uθ (𝕜 := 𝕜) θ) (e1 (𝕜 := 𝕜)) (norm_uθ θ)
  simpa [rotatedModelSubspace] using h

/-- The rotated line is invariant, so its projector fixes its own generator.
The double-angle operators nest the two projectors, so this is needed. -/
@[simp] theorem rotatedModelSubspace_starProjection_uθ (θ : ℝ) :
    (rotatedModelSubspace (𝕜 := 𝕜) θ).starProjection (uθ (𝕜 := 𝕜) θ) =
      uθ θ := by
  have h := starProjection_span_singleton_apply_of_norm_one (𝕜 := 𝕜)
    (uθ (𝕜 := 𝕜) θ) (uθ (𝕜 := 𝕜) θ) (norm_uθ θ)
  rw [rotatedModelSubspace, h, inner_self_eq_norm_sq_to_K, norm_uθ]
  simp

/-- Coordinate projection of the rotated generator, in the same nested
position. -/
@[simp] theorem modelSubspace_starProjection_uθ (θ : ℝ) :
    (modelSubspace (𝕜 := 𝕜)).starProjection (uθ (𝕜 := 𝕜) θ) =
      (Real.cos θ : 𝕜) • e0 := by
  rw [uθ, map_add, map_smul, map_smul, modelSubspace_starProjection_e0,
    modelSubspace_starProjection_e1]
  simp

private theorem projection_sub_model_eq_matrix (θ : ℝ) :
    projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        !![((Real.sin θ ^ 2 : ℝ) : 𝕜),
           ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜);
           ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜),
           ((-Real.sin θ ^ 2 : ℝ) : 𝕜)] := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  apply plane_linearMap_ext
  · -- reduce the projections *before* `e0`/`e1` are unfolded into coordinates
    simp only [LinearMap.sub_apply, projection, ContinuousLinearMap.coe_coe,
      modelSubspace_starProjection_e0, modelSubspace_starProjection_e1,
      rotatedModelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e1]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toEuclideanLin_apply, PiLp.single_apply] <;>
      (try push_cast) <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        smul_eq_mul, mul_one, RCLike.ofReal_mul, RCLike.ofReal_one]) <;>
      -- `ring` degrades to `ring_nf` and *succeeds*, so `first` would never
      -- reach the Pythagorean alternatives; `ring1` fails properly
      first
        | ring1
        | linear_combination (-1 : 𝕜) * hpy
        | linear_combination hpy
  · simp only [LinearMap.sub_apply, projection, ContinuousLinearMap.coe_coe,
      modelSubspace_starProjection_e0, modelSubspace_starProjection_e1,
      rotatedModelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e1]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toEuclideanLin_apply, PiLp.single_apply] <;>
      (try push_cast) <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        smul_eq_mul, mul_one, RCLike.ofReal_mul, RCLike.ofReal_one]) <;>
      -- `ring` degrades to `ring_nf` and *succeeds*, so `first` would never
      -- reach the Pythagorean alternatives; `ring1` fails properly
      first
        | ring1
        | linear_combination (-1 : 𝕜) * hpy
        | linear_combination hpy

private theorem sinThetaMap_model_eq_matrix (θ : ℝ) :
    sinThetaMap (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        !![((Real.sin θ ^ 2 : ℝ) : 𝕜), 0;
           ((-Real.sin θ * Real.cos θ : ℝ) : 𝕜), 0] := by
  have hpy : ((Real.sin θ : 𝕜)) ^ 2 + ((Real.cos θ : 𝕜)) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) (Real.sin_sq_add_cos_sq θ)
    push_cast at h
    exact h
  apply plane_linearMap_ext
  · -- reduce the projections *before* `e0`/`e1` are unfolded into coordinates
    simp only [sinThetaMap, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply, LinearMap.sub_apply,
      modelSubspace_starProjection_e0, modelSubspace_starProjection_e1,
      rotatedModelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e1, map_smul, map_add,
      modelSubspace_starProjection_uθ, rotatedModelSubspace_starProjection_uθ,
      Submodule.starProjection_orthogonal_val]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toEuclideanLin_apply, PiLp.single_apply] <;>
      (try push_cast) <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        smul_eq_mul, mul_one, RCLike.ofReal_mul, RCLike.ofReal_one]) <;>
      -- `ring` degrades to `ring_nf` and *succeeds*, so `first` would never
      -- reach the Pythagorean alternatives; `ring1` fails properly
      first
        | ring1
        | linear_combination (-1 : 𝕜) * hpy
        | linear_combination hpy
  · simp only [sinThetaMap, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.comp_apply, LinearMap.sub_apply,
      modelSubspace_starProjection_e0, modelSubspace_starProjection_e1,
      rotatedModelSubspace_starProjection_e0,
      rotatedModelSubspace_starProjection_e1, map_smul, map_add,
      modelSubspace_starProjection_uθ, rotatedModelSubspace_starProjection_uθ,
      Submodule.starProjection_orthogonal_val]
    ext i
    fin_cases i <;>
      simp [uθ, e0, e1, Matrix.toEuclideanLin_apply, PiLp.single_apply] <;>
      (try push_cast) <;>
      (try simp only [RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
        smul_eq_mul, mul_one, RCLike.ofReal_mul, RCLike.ofReal_one]) <;>
      -- `ring` degrades to `ring_nf` and *succeeds*, so `first` would never
      -- reach the Pythagorean alternatives; `ring1` fails properly
      first
        | ring1
        | linear_combination (-1 : 𝕜) * hpy
        | linear_combination hpy

private theorem sinTwoAngleOperator_model_eq_matrix (θ : ℝ) :
    sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        !![0, 0; ((Real.sin (2 * θ) : ℝ) : 𝕜), 0] := by
  apply plane_linearMap_ext
  · ext i
    fin_cases i <;>
      simp [sinTwoAngleOperator, complementaryProjection, projection, uθ,
        Matrix.toEuclideanLin_apply, e0, e1, PiLp.single_apply,
        Real.sin_two_mul] <;> push_cast <;> ring
  · ext i
    fin_cases i <;>
      simp [sinTwoAngleOperator, complementaryProjection, projection, uθ,
        Matrix.toEuclideanLin_apply, e0, e1, PiLp.single_apply,
        Real.sin_two_mul] <;> push_cast <;> ring

private theorem projection_sub_model_isSymmetric (θ : ℝ) :
    (projection (modelSubspace (𝕜 := 𝕜)) -
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ)).IsSymmetric :=
  (projection_isSymmetric _).sub (projection_isSymmetric _)

private theorem projection_sub_model_sq (θ : ℝ) :
    (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ)) ∘ₗ
      (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      ((((Real.sin θ) ^ 2 : ℝ) : 𝕜) • LinearMap.id) := by
  rw [projection_sub_model_eq_matrix]
  ext x i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin_apply, Fin.sum_univ_two] <;>
    push_cast <;> nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem modelSinThetaPerturbation_isSymmetric (a b θ : ℝ) :
    (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).IsSymmetric := by
  intro x y
  simp [modelSinThetaPerturbation, Matrix.toEuclideanLin_apply, Fin.sum_univ_two]
  ring

private theorem modelSinThetaPerturbation_sq (a b θ : ℝ) :
    modelSinThetaPerturbation (𝕜 := 𝕜) a b θ ∘ₗ
      modelSinThetaPerturbation (𝕜 := 𝕜) a b θ =
      (((((b - a) * Real.sin θ) ^ 2 : ℝ) : 𝕜) • LinearMap.id) := by
  ext x i
  fin_cases i <;>
    simp [modelSinThetaPerturbation, Matrix.toEuclideanLin_apply,
      Fin.sum_univ_two] <;>
    push_cast <;> nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem singularValues_sinThetaMap_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (sinThetaMap (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin θ) 0 := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  rw [sinThetaMap_model_eq_matrix]
  apply singularValues_eq_pair_of_gram_eq finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin 2) 𝕜) _ hsin (by norm_num) hsin
  refine (EuclideanSpace.basisFun (Fin 2) 𝕜).toBasis.ext fun i => ?_
  rw [OrthonormalBasis.coe_toBasis]
  fin_cases i <;>
    ext j <;> fin_cases j <;>
    simp [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      Matrix.toEuclideanLin_apply, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, diagOp_apply_basis] <;>
    push_cast <;> nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem singularValues_projection_sub_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (projection (modelSubspace (𝕜 := 𝕜)) -
      projection (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin θ) (Real.sin θ) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  simpa [abs_of_nonneg hsin] using
    singularValues_eq_abs_pair_of_isSymmetric_sq finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜)
      (projection (modelSubspace (𝕜 := 𝕜)) -
        projection (rotatedModelSubspace (𝕜 := 𝕜) θ))
      (Real.sin θ) (projection_sub_model_isSymmetric θ)
      (projection_sub_model_sq θ)

private theorem singularValues_modelSinThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues ((b - a) * Real.sin θ)
        ((b - a) * Real.sin θ) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hprod : 0 ≤ (b - a) * Real.sin θ :=
    mul_nonneg (sub_nonneg.mpr hab.le) hsin
  simpa [abs_of_nonneg hprod] using
    singularValues_eq_abs_pair_of_isSymmetric_sq finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜)
      (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ)
      ((b - a) * Real.sin θ)
      (modelSinThetaPerturbation_isSymmetric a b θ)
      (modelSinThetaPerturbation_sq a b θ)

private theorem singularValues_sinAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin θ) (Real.sin θ) := by
  rw [← singularValues_projection_sub_projection]
  exact singularValues_projection_sub_model hθ0 hθ1

private theorem sinAngleOperator_model_eq_smul_id
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    sinAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      (((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) := by
  let A := projection (modelSubspace (𝕜 := 𝕜)) -
    projection (rotatedModelSubspace (𝕜 := 𝕜) θ)
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hpos : ((((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) :
      Plane 𝕜 →ₗ[𝕜] Plane 𝕜).IsPositive := by
    constructor
    · intro x y
      simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
        inner_smul_right, RCLike.conj_ofReal]
      rw [inner_conj_symm]
    · intro x
      rw [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
        RCLike.conj_ofReal, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]
      exact mul_nonneg hsin (sq_nonneg _)
  have hsquare :
      ((((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) : Plane 𝕜 →ₗ[𝕜] Plane 𝕜) ∘ₗ
          (((Real.sin θ : ℝ) : 𝕜) • LinearMap.id) = A.adjoint ∘ₗ A := by
    rw [show A.adjoint = A from (projection_sub_model_isSymmetric θ).adjoint_eq]
    simpa [A, smul_smul, ← RCLike.ofReal_mul, pow_two] using
      (projection_sub_model_sq (𝕜 := 𝕜) θ).symm
  change ForMathlib.abs A = _
  exact (LinearMap.IsPositive.sqrt_unique A.isPositive_adjoint_comp_self hpos hsquare).symm

private theorem singularValues_tanAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.tan θ) (Real.tan θ) := by
  have hθle : θ ≤ Real.pi / 2 := hθ1.le
  have hsinEq := sinAngleOperator_model_eq_smul_id (𝕜 := 𝕜) hθ0 hθle
  have harcsin : Real.arcsin (Real.sin θ) = θ :=
    Real.arcsin_sin (by linarith [Real.pi_pos]) hθle
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have htan : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθle
  rw [tanAngleOperator, hsinEq]
  have hfc := FiniteDimensional.selfAdjointFunctionalCalculus_real_smul_id
    (𝕜 := 𝕜) (E := Plane 𝕜) (Real.sin θ) Real.arcsin
  rw [hfc, harcsin,
    FiniteDimensional.selfAdjointFunctionalCalculus_real_smul_id]
  simp [safeTan, hcos]
  simpa [abs_of_nonneg htan] using
    singularValues_diagOp_fin_two (𝕜 := 𝕜) finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜) htan htan le_rfl

private theorem singularValues_sinTwoAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.sin (2 * θ)) 0 := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [sinTwoAngleOperator_model_eq_matrix]
  simpa [abs_of_nonneg hsin] using
    singularValues_lowerLeft_two_by_two (𝕜 := 𝕜) (Real.sin (2 * θ))

private theorem singularValues_tanTwoAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      pairSingularValues (Real.tan (2 * θ)) (Real.tan (2 * θ)) := by
  have hθle : θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsinEq := sinAngleOperator_model_eq_smul_id (𝕜 := 𝕜) hθ0 hθle
  have harcsin : Real.arcsin (Real.sin θ) = θ :=
    Real.arcsin_sin (by linarith [Real.pi_pos]) hθle
  have hcos : Real.cos (2 * θ) ≠ 0 := by
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  have htan : 0 ≤ Real.tan (2 * θ) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  rw [tanTwoAngleOperator, hsinEq]
  have hfc := FiniteDimensional.selfAdjointFunctionalCalculus_real_smul_id
    (𝕜 := 𝕜) (E := Plane 𝕜) (Real.sin θ) Real.arcsin
  rw [hfc, harcsin,
    FiniteDimensional.selfAdjointFunctionalCalculus_real_smul_id]
  simp [safeTanTwo, hcos]
  simpa [abs_of_nonneg htan] using
    singularValues_diagOp_fin_two (𝕜 := 𝕜) finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin 2) 𝕜) htan htan le_rfl

private theorem singularValues_modelSinTwoThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues (((b - a) / 2) * Real.sin (2 * θ))
        (((b - a) / 2) * Real.sin (2 * θ)) := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hprod : 0 ≤ ((b-a)/2) * Real.sin (2*θ) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num)) hsin
  simpa [modelSinTwoThetaPerturbation, abs_of_nonneg hprod, abs_neg,
    neg_sub] using
    singularValues_offDiagonal_two_by_two (𝕜 := 𝕜)
      (((a-b)/2) * Real.sin (2*θ))

private theorem singularValues_modelTanTwoThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (htan : 0 ≤ Real.tan (2 * θ)) :
    (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues (((b - a) / 2) * Real.tan (2 * θ))
        (((b - a) / 2) * Real.tan (2 * θ)) := by
  have hprod : 0 ≤ ((b-a)/2) * Real.tan (2*θ) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num)) htan
  simpa [modelTanTwoThetaPerturbation, abs_of_nonneg hprod] using
    singularValues_offDiagonal_two_by_two (𝕜 := 𝕜)
      (((b-a)/2) * Real.tan (2*θ))

private theorem singularValues_modelTanThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (htan : 0 ≤ Real.tan θ) :
    (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      pairSingularValues ((b-a) * Real.tan θ) ((b-a) * Real.tan θ) := by
  have hprod : 0 ≤ (b-a) * Real.tan θ :=
    mul_nonneg (sub_nonneg.mpr hab.le) htan
  simpa [modelTanThetaPerturbation, abs_of_nonneg hprod] using
    singularValues_offDiagonal_two_by_two (𝕜 := 𝕜) ((b-a) * Real.tan θ)

/-- The model subspaces have exactly the prescribed principal angle.

Lean proof route for a weaker agent:

1. Write the two normalized spanning vectors explicitly, compute the single overlap singular value `|cos θ|`, and use the angle-range hypotheses to simplify `arccos`.
2. Prove the overlap scalar is nonnegative on `[0,π/2]`, so the absolute value disappears.
3. Rewrite the first principal angle with `Real.arccos_cos` and the supplied range bounds.
-/
theorem principalAngles_model (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    principalAngles (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ) 0 = θ := by
  rw [principalAngles]
  change Real.arcsin
      ((sinThetaMap (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues 0) = θ
  rw [singularValues_sinThetaMap_model hθ0 hθ1]
  simp only [pairSingularValues_zero]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) hθ1

/-- Equality case for the `sin Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.

Signature audit: The theorem now uses a dedicated `sin Θ` perturbation model; do not reuse it
for the tangent or double-angle families.
-/
/-- The scalar gap is a positive real, so its field norm is itself.  The
singular-value comparisons need this to discharge the `‖b - a‖` that
`singularValues_smul` introduces. -/
private theorem norm_ofReal_sub_of_lt {a b : ℝ} (hab : a < b) :
    ‖((b : 𝕜) - (a : 𝕜))‖ = b - a := by
  rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, abs_of_pos (sub_pos.mpr hab)]

theorem sinTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have hsing :
      (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
        ((b-a : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues := by
    rw [singularValues_modelSinThetaPerturbation hab hθ0 (le_of_lt hθ1),
      RectangularUnitarilyInvariantNorm.singularValues_smul,
      singularValues_sinAngle_model hθ0 (le_of_lt hθ1)]
    ext i
    simp [pairSingularValues, abs_of_pos (sub_pos.mpr hab),
      norm_ofReal_sub_of_lt hab,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    (b-a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ))
        = N ((b-a : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
            (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
          rw [N.smul_eq]; simp [abs_of_pos (sub_pos.mpr hab)]
    _ = N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing.symm

/-- Equality case for the `tan Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.

Signature audit: The dedicated tangent model must include the zero-compression/Galerkin
hypothesis required by the theorem it saturates.
-/
theorem tanTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan θ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 hθ1.le
  have hsing :
      (((b - a : ℝ) : 𝕜) • tanAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
        (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues := by
    rw [RectangularUnitarilyInvariantNorm.singularValues_smul,
      singularValues_tanAngle_model hθ0 hθ1,
      singularValues_modelTanThetaPerturbation hab htan]
    ext i
    simp [pairSingularValues, abs_of_pos (sub_pos.mpr hab),
      norm_ofReal_sub_of_lt hab,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (((b - a : ℝ) : 𝕜) • tanAngleOperator
          (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
      rw [N.smul_eq]
      simp [abs_of_pos (sub_pos.mpr hab)]
    _ = N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing

/-- Equality case for the `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.

Signature audit: The dedicated double-angle model is reflection-compatible and is independent
of the single-angle extremizer.
-/
theorem sinTwoTheta_model_operatorNorm_equality
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ =
      2 * ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ := by
  rw [opNorm_eq_singularValues_zero _ finrank_euclideanSpace_fin (by norm_num),
    opNorm_eq_singularValues_zero _ finrank_euclideanSpace_fin (by norm_num),
    singularValues_sinTwoAngle_model hθ0 hθ1,
    singularValues_modelSinTwoThetaPerturbation hab hθ0 hθ1]
  simp only [pairSingularValues_zero]
  ring

/-- Equality case for the `tan 2Θ` theorem.

Lean proof route for a weaker agent:

1. First separate the correct planar model for this theorem family.
2. Then compute the two-by-two matrices, their singular values, the gap, and the relevant angle function explicitly; equality should reduce to a scalar trigonometric identity.
-/
theorem tanTwoTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan (2 * θ) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  have hsing :
      (((b - a : ℝ) : 𝕜) • tanTwoAngleOperator
        (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
        (((2 : ℝ) : 𝕜) • modelTanTwoThetaPerturbation
          (𝕜 := 𝕜) a b θ).singularValues := by
    rw [RectangularUnitarilyInvariantNorm.singularValues_smul,
      RectangularUnitarilyInvariantNorm.singularValues_smul,
      singularValues_tanTwoAngle_model hθ0 hθ1,
      singularValues_modelTanTwoThetaPerturbation hab htan]
    ext i
    simp [pairSingularValues, abs_of_pos (sub_pos.mpr hab),
      norm_ofReal_sub_of_lt hab,
      mul_assoc, mul_left_comm, mul_comm]
    ring
  calc
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
        N (((b - a : ℝ) : 𝕜) • tanTwoAngleOperator
          (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
      rw [N.smul_eq]
      simp [abs_of_pos (sub_pos.mpr hab)]
    _ = N (((2 : ℝ) : 𝕜) • modelTanTwoThetaPerturbation
          (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing
    _ = 2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
      rw [N.smul_eq]
      norm_num

/-- The constant one in the single-angle theorems cannot be decreased.

Lean proof route for a weaker agent:

1. Instantiate the corrected planar equality model at any nonzero admissible angle and use `c < 1` or `c < 2` to obtain the strict counterexample to a smaller universal constant.
2. Choose explicit `a<b` and `0<θ<π/2`, then invoke `sinTheta_model_equality` for the operator norm.
3. Multiply the strict inequality `c<1` by the positive perturbation norm.
-/
theorem sinTheta_constant_optimal :
    ∀ c : ℝ, c < 1 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 6, by norm_num, by positivity, ?_⟩
  have heq := sinTheta_model_equality
    (UnitarilyInvariantNorm.opNorm 𝕜 (Plane 𝕜))
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi/6)
    (by norm_num) (by positivity) (by linarith [Real.pi_pos])
  have hpos : 0 < ‖(modelSinThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi/6)).toContinuousLinearMap‖ := by
    rw [norm_pos_iff]
    intro hzero
    have := congrArg (fun T => T (e0 (𝕜 := 𝕜))) hzero
    simpa [modelSinThetaPerturbation, e0] using this
  simpa using (mul_lt_of_lt_one_left hpos hc)

/-- The factor two in the double-angle theorems cannot be decreased.

Lean proof route for a weaker agent:

1. Instantiate the corrected planar equality model at any nonzero admissible angle and use `c < 1` or `c < 2` to obtain the strict counterexample to a smaller universal constant.
2. Choose an angle with nonzero double-angle map and invoke `sinTwoTheta_model_operatorNorm_equality`.
3. Multiply `c<2` by the positive perturbation norm and rewrite the equality.
-/
theorem sinTwoTheta_constant_optimal :
    ∀ c : ℝ, c < 2 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 8, by norm_num, by positivity, ?_⟩
  have heq := sinTwoTheta_model_operatorNorm_equality
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi/8)
    (by norm_num) (by positivity) (by linarith [Real.pi_pos])
  have hpos : 0 < ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi/8)).toContinuousLinearMap‖ := by
    rw [norm_pos_iff]
    intro hzero
    have := congrArg (fun T => T (e0 (𝕜 := 𝕜))) hzero
    simpa [modelSinTwoThetaPerturbation, e0] using this
  nlinarith

/-!
The former `directSum_models_simultaneous_equality` declaration was false: the
one-sided `sinTwoAngleOperator` contributes one nonzero singular value per
principal plane, whereas the symmetric off-diagonal perturbation contributes
two.  A future simultaneous-gauge theorem must use rank-matched one-sided
residual models.  The operator-norm sharpness result above is the correct
endpoint for the present symmetric planar perturbation.
-/


/-- To first order in a linear perturbation parameter, all four theorem
conclusions agree.

Signature audit: The theorem has been renamed to match its scalar content.  The operator-level
first-order comparison should be a separate corollary of the four planar equality theorems.
-/
theorem single_double_sine_tangent_ratios_tendsto_one :
    Tendsto (fun θ : ℝ => Real.sin θ / Real.tan θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto (fun θ : ℝ => Real.sin (2 * θ) / Real.tan (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have base : Tendsto (fun θ : ℝ => Real.sin θ / Real.tan θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hcos : Tendsto (fun θ : ℝ => Real.cos θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.cos 0)) :=
        (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds Real.pi_div_two_pos)
    refine hcos.congr' ?_
    filter_upwards [hmem] with θ hθ
    have hsin : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2]))
    rw [Real.tan_eq_sin_div_cos, div_div_eq_mul_div,
      mul_comm (Real.sin θ) (Real.cos θ), mul_div_assoc, div_self hsin, mul_one]
  refine ⟨base, ?_⟩
  have h2 : Tendsto (fun θ : ℝ => 2 * θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun θ : ℝ => 2 * θ) := continuous_const.mul continuous_id
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ (hθ : (0 : ℝ) < θ)
      exact mul_pos two_pos hθ
  exact base.comp h2

end DavisKahanTheory
end ForMathlib
