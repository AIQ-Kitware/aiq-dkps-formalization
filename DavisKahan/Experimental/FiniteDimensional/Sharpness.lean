/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Sources.Davis1963.RotationEnergy
import DavisKahan.FiniteDimensional.Core.AngleGeometry
import DavisKahan.FiniteDimensional.Core.SpectralGap
import DavisKahan.Experimental.FiniteDimensional.Core.AngleOperators

/-!
# Sharpness and planar extremizers

The four Davis--Kahan constants are realized by explicit two-dimensional
matrices.  The models are deliberately distinct because the equality
conditions in the sine, tangent, double-sine, and double-tangent proofs are
different.  Direct sums repeat the singular-value lists, so the same equality
holds for every symmetric gauge and therefore every unitarily invariant norm.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Plane (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)

private noncomputable def e0 : Plane 𝕜 :=
  EuclideanSpace.single (0 : Fin 2) (1 : 𝕜)
private noncomputable def e1 : Plane 𝕜 :=
  EuclideanSpace.single (1 : Fin 2) (1 : 𝕜)
private noncomputable def uθ (θ : ℝ) : Plane 𝕜 :=
  (Real.cos θ : 𝕜) • e0 + (Real.sin θ : 𝕜) • e1
private noncomputable def vθ (θ : ℝ) : Plane 𝕜 :=
  -(Real.sin θ : 𝕜) • e0 + (Real.cos θ : 𝕜) • e1

private theorem orthonormal_uθ_vθ (θ : ℝ) :
    Orthonormal 𝕜 (![uθ (𝕜 := 𝕜) θ, vθ (𝕜 := 𝕜) θ] : Fin 2 → Plane 𝕜) := by
  simp [uθ, vθ, e0, e1, Real.sin_sq_add_cos_sq]

/-- Coordinate line in the planar model. -/
noncomputable def modelSubspace : Submodule 𝕜 (Plane 𝕜) :=
  Submodule.span 𝕜 {e0 (𝕜 := 𝕜)}

/-- Line rotated counterclockwise by `θ`. -/
noncomputable def rotatedModelSubspace (θ : ℝ) : Submodule 𝕜 (Plane 𝕜) :=
  Submodule.span 𝕜 {uθ (𝕜 := 𝕜) θ}

/-- Diagonal operator with spectral values `a<b`. -/
noncomputable def modelGappedOperator (a b : ℝ) : Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin (Matrix.diagonal ![(a : 𝕜), (b : 𝕜)])

/-- Equality perturbation for the single-angle sine theorem.  It is the
rotation conjugate of `diag(a,b)` minus `diag(a,b)`. -/
noncomputable def modelSinThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    ![![((b-a) * Real.sin θ ^ 2 : ℝ) : 𝕜,
        (-((b-a) * Real.sin θ * Real.cos θ) : ℝ) : 𝕜],
      ![(-((b-a) * Real.sin θ * Real.cos θ) : ℝ) : 𝕜,
        (-((b-a) * Real.sin θ ^ 2) : ℝ) : 𝕜]]

/-- Equality residual for the single-angle tangent theorem. -/
noncomputable def modelTanThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  Matrix.toEuclideanLin
    ![![(0 : 𝕜), (((b-a) * Real.tan θ : ℝ) : 𝕜)],
      ![(((b-a) * Real.tan θ : ℝ) : 𝕜), (0 : 𝕜)]]

/-- Equality perturbation for `sin (2Θ)`.  With
`d=(b-a)/2`, the perturbed operator has eigenvectors `uθ,vθ` and centered
eigenvalues `±d cos(2θ)`. -/
noncomputable def modelSinTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  let d := (b-a) / 2
  let s := Real.sin (2*θ)
  let c := Real.cos (2*θ)
  Matrix.toEuclideanLin
    ![![((d*s^2 : ℝ) : 𝕜), ((-d*s*c : ℝ) : 𝕜)],
      ![((-d*s*c : ℝ) : 𝕜), ((-d*s^2 : ℝ) : 𝕜)]]

/-- Equality perturbation for `tan (2Θ)`.  The perturbed operator has centered
eigenvalues `±d/cos(2θ)`, so its diagonal part is unchanged and its off-diagonal
entry is `d tan(2θ)`. -/
noncomputable def modelTanTwoThetaPerturbation (a b θ : ℝ) :
    Plane 𝕜 →ₗ[𝕜] Plane 𝕜 :=
  let d := (b-a) / 2
  Matrix.toEuclideanLin
    ![![(0 : 𝕜), ((-d * Real.tan (2*θ) : ℝ) : 𝕜)],
      ![((-d * Real.tan (2*θ) : ℝ) : 𝕜), (0 : 𝕜)]]

private theorem modelProjection_matrix (θ : ℝ) :
    projection (rotatedModelSubspace (𝕜 := 𝕜) θ) =
      Matrix.toEuclideanLin
        ![![((Real.cos θ)^2 : ℝ), (Real.sin θ * Real.cos θ : ℝ)],
          ![(Real.sin θ * Real.cos θ : ℝ), ((Real.sin θ)^2 : ℝ)]] := by
  ext x
  rw [projection_span_unit (orthonormal_uθ_vθ (𝕜 := 𝕜) θ).1]
  simp [uθ, e0, e1, inner_add_left, inner_smul_left, Matrix.toEuclideanLin_apply]

/-- The two model lines have principal angle `θ` on `[0,π/2]`. -/
theorem principalAngles_model (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    principalAngles (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ) 0 = θ := by
  classical
  have hoverlap :
      (principalCosines (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)) 0 = Real.cos θ := by
    rw [principalCosines_rankOne]
    simp [modelSubspace, rotatedModelSubspace, uθ, e0, e1,
      Real.cos_nonneg_of_mem_Icc ⟨hθ0, hθ1⟩]
  rw [principalAngles, hoverlap]
  exact Real.arccos_cos hθ0 hθ1

private theorem singularValues_sinAngle_model
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      fun i => if i < 2 then Real.sin θ else 0 := by
  funext i
  rw [sinAngleOperator_singularValues, principalAngles_model θ hθ0 hθ1]
  simp [Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (hθ1.trans (by linarith [Real.pi_pos]))]

private theorem singularValues_modelSinThetaPerturbation
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
      fun i => if i < 2 then (b-a) * Real.sin θ else 0 := by
  have hsquare :
      modelSinThetaPerturbation (𝕜 := 𝕜) a b θ ∘ₗ
        modelSinThetaPerturbation (𝕜 := 𝕜) a b θ =
      (((b-a) * Real.sin θ)^2 : 𝕜) • LinearMap.id := by
    ext i <;> fin_cases i <;>
      simp [modelSinThetaPerturbation, Matrix.toEuclideanLin_apply,
        Real.sin_sq_add_cos_sq] <;> ring
  exact singularValues_eq_constant_of_selfAdjoint_sq_scalar hsquare
    (mul_nonneg (sub_nonneg.mpr (le_of_lt hab))
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [hθ1, Real.pi_pos])))

/-- Equality case for the `sin Θ` theorem. -/
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
      LinearMap.singularValues_smul,
      singularValues_sinAngle_model hθ0 (le_of_lt hθ1)]
    funext i; split <;> simp [abs_of_pos (sub_pos.mpr hab)]
  calc
    (b-a) * N (sinAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ))
        = N ((b-a : 𝕜) • sinAngleOperator (modelSubspace (𝕜 := 𝕜))
            (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
          rw [N.smul]; simp [abs_of_pos (sub_pos.mpr hab)]
    _ = N (modelSinThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsing.symm

/-- Equality case for the `tan Θ` theorem. -/
theorem tanTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N (tanAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      N (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan θ := Real.tan_nonneg_of_nonneg_of_lt_pi_div_two hθ0 hθ1
  have hsingT := singularValues_tanAngle_model (𝕜 := 𝕜) hθ0 hθ1
  have hsingH :
      (modelTanThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues =
        fun i => if i < 2 then (b-a) * Real.tan θ else 0 := by
    exact singularValues_offDiagonal_two_by_two
      (mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) htan)
  apply N.eq_of_same_singularValues
  rw [LinearMap.singularValues_smul, hsingT, hsingH]
  funext i; split <;> simp [abs_of_pos (sub_pos.mpr hab)]

/-- Equality case for the `sin 2Θ` theorem. -/
theorem sinTwoTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    (b - a) * N (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have hsingS := singularValues_sinTwoAngle_model (𝕜 := 𝕜) hθ0 hθ1
  have hsingH := singularValues_modelSinTwoThetaPerturbation
    (𝕜 := 𝕜) hab hθ0 hθ1
  have hsame :
      ((b-a : 𝕜) • sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
        (rotatedModelSubspace (𝕜 := 𝕜) θ)).singularValues =
      ((2 : 𝕜) • modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).singularValues := by
    rw [LinearMap.singularValues_smul, LinearMap.singularValues_smul,
      hsingS, hsingH]
    funext i; split <;> simp [abs_of_pos (sub_pos.mpr hab), abs_of_nonneg]
  calc
    (b-a) * N (sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ))
        = N ((b-a : 𝕜) • sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
            (rotatedModelSubspace (𝕜 := 𝕜) θ)) := by
          rw [N.smul]; simp [abs_of_pos (sub_pos.mpr hab)]
    _ = N ((2 : 𝕜) • modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) :=
      N.eq_of_same_singularValues hsame
    _ = 2 * N (modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
      rw [N.smul]; norm_num

/-- Equality case for the `tan 2Θ` theorem. -/
theorem tanTwoTheta_model_equality
    (N : UnitarilyInvariantNorm 𝕜 (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 4) :
    (b - a) * N (tanTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
      (rotatedModelSubspace (𝕜 := 𝕜) θ)) =
      2 * N (modelTanTwoThetaPerturbation (𝕜 := 𝕜) a b θ) := by
  have htan : 0 ≤ Real.tan (2*θ) := by
    apply Real.tan_nonneg_of_nonneg_of_lt_pi_div_two
    · linarith
    · linarith
  have hsingT := singularValues_tanTwoAngle_model (𝕜 := 𝕜) hθ0 hθ1
  have hsingH := singularValues_modelTanTwoThetaPerturbation
    (𝕜 := 𝕜) hab htan
  apply N.eq_of_same_singularValues
  rw [LinearMap.singularValues_smul, LinearMap.singularValues_smul,
    hsingT, hsingH]
  funext i; split <;> simp [abs_of_pos (sub_pos.mpr hab)]

/-- The constant one in the single-angle theorem cannot be reduced. -/
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
  simpa using (mul_lt_mul_of_lt_one_left hpos hc)

/-- The factor two in the double-angle theorem cannot be reduced. -/
theorem sinTwoTheta_constant_optimal :
    ∀ c : ℝ, c < 2 → ∃ (a b θ : ℝ), a < b ∧ 0 < θ ∧
      c * ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) a b θ).toContinuousLinearMap‖ <
        (b - a) * ‖(sinTwoAngleOperator (modelSubspace (𝕜 := 𝕜))
          (rotatedModelSubspace (𝕜 := 𝕜) θ)).toContinuousLinearMap‖ := by
  intro c hc
  refine ⟨0, 1, Real.pi / 8, by norm_num, by positivity, ?_⟩
  have heq := sinTwoTheta_model_equality
    (UnitarilyInvariantNorm.opNorm 𝕜 (Plane 𝕜))
    (𝕜 := 𝕜) (a := 0) (b := 1) (θ := Real.pi/8)
    (by norm_num) (by positivity) (by linarith [Real.pi_pos])
  have hpos : 0 < ‖(modelSinTwoThetaPerturbation (𝕜 := 𝕜) 0 1
      (Real.pi/8)).toContinuousLinearMap‖ := by
    rw [norm_pos_iff]
    intro hzero
    have := congrArg (fun T => T (e0 (𝕜 := 𝕜))) hzero
    simpa [modelSinTwoThetaPerturbation, e0] using this
  nlinarith

/-- Orthogonal direct sums repeat the planar equality singular values, hence
attain equality for every UI norm simultaneously. -/
theorem directSum_models_simultaneous_equality (m : ℕ) :
    ∃ (A H : EuclideanSpace 𝕜 (Fin (2 * m)) →ₗ[𝕜]
        EuclideanSpace 𝕜 (Fin (2 * m)))
      (U V : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin (2 * m))))
      (δ : ℝ),
      A.IsSymmetric ∧ H.IsSymmetric ∧ 0 < δ ∧
      Reduces A U ∧ Reduces (A + H) V ∧ InternalGap A U δ ∧
      ∀ N : UnitarilyInvariantNorm 𝕜 (EuclideanSpace 𝕜 (Fin (2 * m))),
        δ * N (sinTwoAngleOperator U V) = 2 * N H := by
  classical
  let θ := Real.pi / 8
  let e : Fin (2*m) ≃ Fin m × Fin 2 := finTwoBlockEquiv m
  let A := blockDiagonalAlong e (fun _ => modelGappedOperator (𝕜 := 𝕜) 0 1)
  let H := blockDiagonalAlong e
    (fun _ => modelSinTwoThetaPerturbation (𝕜 := 𝕜) 0 1 θ)
  let U := blockSubspaceAlong e (fun _ => modelSubspace (𝕜 := 𝕜))
  let V := blockSubspaceAlong e
    (fun _ => rotatedModelSubspace (𝕜 := 𝕜) θ)
  refine ⟨A, H, U, V, 1, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact blockDiagonal_isSymmetric fun _ => modelGappedOperator_isSymmetric 0 1
  · exact blockDiagonal_isSymmetric fun _ => modelSinTwoThetaPerturbation_isSymmetric 0 1 θ
  · exact blockSubspace_reduces_blockDiagonal _ _
  · intro j
    exact modelSinTwoTheta_perturbed_reduces_rotated
      (𝕜 := 𝕜) (a := 0) (b := 1) (θ := θ)
  · exact internalGap_blockDiagonal (by norm_num)
  · intro N
    have hsing := singularValues_blockDiagonal_repeat e
      (sinTwoTheta_model_equality
        (UnitarilyInvariantNorm.opNorm 𝕜 (Plane 𝕜))
        (𝕜 := 𝕜) (a := 0) (b := 1) (θ := θ)
        (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
    exact N.eq_of_same_singularValues hsing

/-- The single- and double-angle sine/tangent ratios agree to first order. -/
theorem single_double_sine_tangent_ratios_tendsto_one :
    Tendsto (fun θ : ℝ => Real.sin θ / Real.tan θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto (fun θ : ℝ => Real.sin (2 * θ) / Real.tan (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hbase : Tendsto (fun x : ℝ => Real.sin x / Real.tan x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hcos : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      simpa using (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with x hx
    rw [Real.tan_eq_sin_div_cos]
    field_simp [Real.sin_ne_zero_of_mem_Ioo hx]
  refine ⟨hbase, ?_⟩
  have htwo : Tendsto (fun x : ℝ => 2*x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    exact tendsto_nhdsWithin_mono_right
      (by simpa using (continuous_const.mul continuous_id).tendsto 0)
      (by intro x hx; positivity)
  exact hbase.comp htwo

end DavisKahanTheory
end ForMathlib
