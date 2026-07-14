/-
Rigid-coordinate invariance for the Quench OLS bridge.

Classical multidimensional scaling identifies a centered configuration only up
to a common orthogonal transformation.  Ordinary least squares with an
intercept is insensitive to this ambiguity: rotating every feature vector and
rotating the slope by the same linear isometry leaves every fitted prediction
and every least-squares objective value unchanged.
-/
import DkpsQuench2026.Paper.OLSQueryEfficiency

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
  RealInnerProductSpace InnerProductSpace
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

universe u v

namespace DkpsQuench2026.Paper.OLS

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {d n : ℕ}

/-- Rotate the slope of an affine predictor by a linear isometry, leaving its
intercept unchanged. -/
def rotateCoefficients
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (θ : AffineCoefficients d) :
    AffineCoefficients d where
  intercept := θ.intercept
  slope := W θ.slope

@[simp] theorem rotateCoefficients_intercept
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (θ : AffineCoefficients d) :
    (rotateCoefficients W θ).intercept = θ.intercept := rfl

@[simp] theorem rotateCoefficients_slope
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (θ : AffineCoefficients d) :
    (rotateCoefficients W θ).slope = W θ.slope := rfl

/-- Rotating both the coordinate and the slope leaves an affine prediction
unchanged. -/
theorem affinePredict_rotate
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (θ : AffineCoefficients d) (x : Vec d) :
    affinePredict (rotateCoefficients W θ) (W x) = affinePredict θ x := by
  unfold affinePredict rotateCoefficients
  rw [LinearIsometryEquiv.inner_map_map]

@[simp] theorem rotateCoefficients_symm_apply
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (θ : AffineCoefficients d) :
    rotateCoefficients W.symm (rotateCoefficients W θ) = θ := by
  cases θ
  simp [rotateCoefficients]

@[simp] theorem rotateCoefficients_apply_symm
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (θ : AffineCoefficients d) :
    rotateCoefficients W (rotateCoefficients W.symm θ) = θ := by
  cases θ
  simp [rotateCoefficients]

/-- The finite least-squares objective is exactly invariant under a common
orthogonal transformation of all feature vectors. -/
theorem empiricalSquaredError_rotate
    (W : Vec d ≃ₗᵢ[ℝ] Vec d)
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) :
    empiricalSquaredError (fun i => W (x i)) target
        (rotateCoefficients W θ) =
      empiricalSquaredError x target θ := by
  unfold empiricalSquaredError
  apply Finset.sum_congr rfl
  intro i _hi
  rw [affinePredict_rotate]

/-- Re-expressing arbitrary transformed coefficients in the original
coordinate system preserves their objective value. -/
theorem empiricalSquaredError_rotate_symm
    (W : Vec d ≃ₗᵢ[ℝ] Vec d)
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) :
    empiricalSquaredError x target (rotateCoefficients W.symm θ) =
      empiricalSquaredError (fun i => W (x i)) target θ := by
  simpa using
    (empiricalSquaredError_rotate
      (W := W.symm) (x := fun i => W (x i)) (target := target) (θ := θ))

/-- Transport an exact OLS minimizer through the rotational ambiguity of a
centered CMDS configuration. -/
def OLSFit.rotate
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target) (W : Vec d ≃ₗᵢ[ℝ] Vec d) :
    OLSFit (fun i => W (x i)) target where
  coeff := rotateCoefficients W fit.coeff
  optimal := by
    intro θ'
    calc
      empiricalSquaredError (fun i => W (x i)) target
          (rotateCoefficients W fit.coeff) =
          empiricalSquaredError x target fit.coeff :=
        empiricalSquaredError_rotate W x target fit.coeff
      _ ≤ empiricalSquaredError x target
          (rotateCoefficients W.symm θ') := fit.optimal _
      _ = empiricalSquaredError (fun i => W (x i)) target θ' :=
        empiricalSquaredError_rotate_symm W x target θ'

/-- The affine model itself is invariant after the matching coefficient
reparameterization. -/
theorem affineModel_rotate
    (W : Vec d ≃ₗᵢ[ℝ] Vec d)
    (ψ : Model Q X → Vec d) (θ : AffineCoefficients d) :
    affineModel (rotateCoefficients W θ) (fun f => W (ψ f)) =
      affineModel θ ψ := by
  funext f
  exact affinePredict_rotate W θ (ψ f)

/-- Consequently, the population MSE of an affine witness is independent of
the arbitrary orthogonal orientation selected by CMDS. -/
theorem mse_affineModel_rotate
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (W : Vec d ≃ₗᵢ[ℝ] Vec d)
    (ψ : Model Q X → Vec d) (θ : AffineCoefficients d) :
    MSE Pf truth (affineModel (rotateCoefficients W θ) (fun f => W (ψ f))) =
      MSE Pf truth (affineModel θ ψ) := by
  rw [affineModel_rotate]


/-! ## Translation and full rigid-motion invariance -/

/-- Reparameterize an affine predictor after translating every feature by the
same vector.  The slope is unchanged and the intercept absorbs the translation. -/
def translateCoefficients
    (c : Vec d) (θ : AffineCoefficients d) : AffineCoefficients d where
  intercept := θ.intercept - ⟪θ.slope, c⟫_ℝ
  slope := θ.slope

@[simp] theorem translateCoefficients_intercept
    (c : Vec d) (θ : AffineCoefficients d) :
    (translateCoefficients c θ).intercept = θ.intercept - ⟪θ.slope, c⟫_ℝ := rfl

@[simp] theorem translateCoefficients_slope
    (c : Vec d) (θ : AffineCoefficients d) :
    (translateCoefficients c θ).slope = θ.slope := rfl

/-- Translating every coordinate and compensating in the intercept leaves every
prediction unchanged. -/
theorem affinePredict_translate
    (c : Vec d) (θ : AffineCoefficients d) (x : Vec d) :
    affinePredict (translateCoefficients c θ) (x + c) = affinePredict θ x := by
  unfold affinePredict translateCoefficients
  rw [inner_add_right]
  ring

@[simp] theorem translateCoefficients_neg_apply
    (c : Vec d) (θ : AffineCoefficients d) :
    translateCoefficients (-c) (translateCoefficients c θ) = θ := by
  cases θ
  simp [translateCoefficients]

@[simp] theorem translateCoefficients_apply_neg
    (c : Vec d) (θ : AffineCoefficients d) :
    translateCoefficients c (translateCoefficients (-c) θ) = θ := by
  cases θ
  simp [translateCoefficients]

/-- The finite least-squares objective is exactly invariant under a common
translation of all features when an intercept is present. -/
theorem empiricalSquaredError_translate
    (c : Vec d) (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) :
    empiricalSquaredError (fun i => x i + c) target
        (translateCoefficients c θ) =
      empiricalSquaredError x target θ := by
  unfold empiricalSquaredError
  apply Finset.sum_congr rfl
  intro i _hi
  rw [affinePredict_translate]

/-- Re-expressing arbitrary translated-coordinate coefficients in the original
coordinate system preserves their objective value. -/
theorem empiricalSquaredError_translate_neg
    (c : Vec d) (x : Fin n → Vec d) (target : Fin n → ℝ)
    (θ : AffineCoefficients d) :
    empiricalSquaredError x target (translateCoefficients (-c) θ) =
      empiricalSquaredError (fun i => x i + c) target θ := by
  have h := empiricalSquaredError_translate
    c x target (translateCoefficients (-c) θ)
  simpa using h.symm

/-- Transport an exact OLS minimizer through a common feature translation. -/
def OLSFit.translate
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target) (c : Vec d) :
    OLSFit (fun i => x i + c) target where
  coeff := translateCoefficients c fit.coeff
  optimal := by
    intro θ'
    calc
      empiricalSquaredError (fun i => x i + c) target
          (translateCoefficients c fit.coeff) =
          empiricalSquaredError x target fit.coeff :=
        empiricalSquaredError_translate c x target fit.coeff
      _ ≤ empiricalSquaredError x target
          (translateCoefficients (-c) θ') := fit.optimal _
      _ = empiricalSquaredError (fun i => x i + c) target θ' :=
        empiricalSquaredError_translate_neg c x target θ'

/-- Reparameterize affine coefficients under the full rigid coordinate change
`x ↦ W x + c`. -/
def rigidCoefficients
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (c : Vec d)
    (θ : AffineCoefficients d) : AffineCoefficients d :=
  translateCoefficients c (rotateCoefficients W θ)

/-- Affine predictions are invariant under a matching orthogonal transformation
and translation of all DKPS coordinates. -/
theorem affinePredict_rigid
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (c : Vec d)
    (θ : AffineCoefficients d) (x : Vec d) :
    affinePredict (rigidCoefficients W c θ) (W x + c) =
      affinePredict θ x := by
  rw [rigidCoefficients, affinePredict_translate, affinePredict_rotate]

/-- Transport an OLS minimizer through a full rigid coordinate change. -/
def OLSFit.rigid
    (x : Fin n → Vec d) (target : Fin n → ℝ)
    (fit : OLSFit x target)
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (c : Vec d) :
    OLSFit (fun i => W (x i) + c) target :=
  OLSFit.translate (fun i => W (x i)) target
    (OLSFit.rotate x target fit W) c

/-- The affine model is invariant under a common rigid transformation of the
perspective coordinates. -/
theorem affineModel_rigid
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (c : Vec d)
    (ψ : Model Q X → Vec d) (θ : AffineCoefficients d) :
    affineModel (rigidCoefficients W c θ) (fun f => W (ψ f) + c) =
      affineModel θ ψ := by
  funext f
  exact affinePredict_rigid W c θ (ψ f)

/-- Population affine risk is independent of the arbitrary rigid representative
used for the DKPS coordinates. -/
theorem mse_affineModel_rigid
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (truth : Model Q X → ℝ)
    (W : Vec d ≃ₗᵢ[ℝ] Vec d) (c : Vec d)
    (ψ : Model Q X → Vec d) (θ : AffineCoefficients d) :
    MSE Pf truth
        (affineModel (rigidCoefficients W c θ) (fun f => W (ψ f) + c)) =
      MSE Pf truth (affineModel θ ψ) := by
  rw [affineModel_rigid]

end DkpsQuench2026.Paper.OLS
