/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.SpectralTheory.FormMethod.BeamSection9
import DavisKahan.TanTheta.Theorem63Unbounded
import DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds

/-!
# Section 9, equations (9.5)--(9.7): the tangent refinement, on the genuine operator

`BeamSection9` proved the two Rayleigh--Ritz inputs for the free-beam example —
the compression form bound `beamRitz_form_le`, the residual norm
`norm_beamRitzResidual_le`, and the perturbed spectral gap
`beamPerturbed_specProjection_Ioo_eq_zero`.  This module bundles them into the
`UnboundedTrialBlock` the unbounded Theorem 6.3 consumes and reads off the
paper's tangent envelope.

The endpoint is `beamTanTheta_le`:

    ‖tan Θ₀‖ ≤ tangentThetaExactBound ε

for the genuine perturbed beam `A + ε t`, its exact low spectral subspace, and the
affine trial subspace — no certificate record, no hypothesis beyond `0 < ε < 100`.
Feeding it to `DavisKahan1970.Section9.equation_9_6` produces the printed decimal.

## The residual is the recentered one

The trial block's residual is `(1 - P_Z) ∘ (A + ε t)|_Z`, whose Gram matrix is the
*recentered* `orthogonalResidualGram ε = (ε²/30)[[1,-1],[-1,1]]` rather than the
initial `residualGram ε`.  That is the whole content of the Rayleigh--Ritz
refinement: the initial residual's top singular value is `|ε|√((11+√76)/30)`, the
recentered one is `|ε|√15/15`, which is smaller by a factor of about 3.9.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Model

open DavisKahan1970.Section9
open TauCeti.DavisKahan.Experimental.TanTheta
open TauCeti.DavisKahan.Experimental.ExactTanTheta
open TauCeti.DavisKahan.Experimental.ExactSinTheta

noncomputable section

/-! ## The Ritz compression as a bounded self-adjoint block -/

/-- The Rayleigh--Ritz compression of the perturbation to the trial subspace. -/
def beamRitzCompression (ε : ℝ) : beamTrial →L[ℂ] beamTrial :=
  beamTrial.orthogonalProjectionOnto ∘L beamResidual ε

theorem beamRitzCompression_coe (ε : ℝ) (x : beamTrial) :
    ((beamRitzCompression ε x : beamTrial) : BeamL2)
      = beamTrial.starProjection (beamResidual ε x) := rfl

/-- The compression of a self-adjoint operator to a subspace is self-adjoint. -/
theorem beamRitzCompression_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint (beamRitzCompression ε) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hproj : ∀ u : BeamL2, ∀ z : beamTrial,
      ⟪beamTrial.starProjection u, (z : BeamL2)⟫_ℂ = ⟪u, (z : BeamL2)⟫_ℂ := by
    intro u z
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 z.2]
  have hx : ⟪(beamRitzCompression ε x : beamTrial), y⟫_ℂ
      = ⟪beamResidual ε x, (y : BeamL2)⟫_ℂ := by
    rw [Submodule.coe_inner, beamRitzCompression_coe, hproj]
  have hy : ⟪x, (beamRitzCompression ε y : beamTrial)⟫_ℂ
      = ⟪(x : BeamL2), beamResidual ε y⟫_ℂ := by
    rw [Submodule.coe_inner, beamRitzCompression_coe, ← inner_conj_symm, hproj,
      inner_conj_symm]
  show ⟪(beamRitzCompression ε x : beamTrial), y⟫_ℂ
      = ⟪x, (beamRitzCompression ε y : beamTrial)⟫_ℂ
  rw [hx, hy]
  exact beamPerturbation_isSelfAdjoint ε (x : BeamL2) (y : BeamL2)

/-! ## The trial block -/

/-- **The Rayleigh--Ritz trial block of the Section 9 example.**  The trial subspace
is the affine plane, the compression is `beamRitzCompression`, and the residual is
the part of `(A + ε t)|_Z` orthogonal to `Z`. -/
def beamTrialBlock (ε : ℝ) : UnboundedTrialBlock (beamPerturbed ε) beamTrial where
  domain_le := fun _ hy => beamTrial_le_domain hy
  operator := beamRitzCompression ε
  operator_selfAdjoint := beamRitzCompression_isSelfAdjoint ε
  operator_apply x := by
    rw [beamRitzCompression_coe]
    congr 1
    have hker : beamOperator.toLinearMap ⟨(x : BeamL2), beamTrial_le_domain x.2⟩ = 0 :=
      beamOperator_apply_trial x.2 _
    show beamResidual ε x = _
    rw [show (beamPerturbed ε).toLinearMap ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
        = beamOperator.toLinearMap ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
          + beamPerturbation ε (x : BeamL2) from rfl, hker, zero_add]
    rfl
  residual := beamResidual ε - beamTrialIncl ∘L beamRitzCompression ε
  residual_apply x := by
    have hker : beamOperator.toLinearMap ⟨(x : BeamL2), beamTrial_le_domain x.2⟩ = 0 :=
      beamOperator_apply_trial x.2 _
    rw [show (beamPerturbed ε).toLinearMap ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
        = beamOperator.toLinearMap ⟨(x : BeamL2), beamTrial_le_domain x.2⟩
          + beamPerturbation ε (x : BeamL2) from rfl, hker, zero_add]
    rfl

theorem beamTrialBlock_residual_apply (ε : ℝ) (x : beamTrial) :
    (beamTrialBlock ε).residual x
      = beamResidual ε x - beamTrial.starProjection (beamResidual ε x) := rfl

/-- **The recentered residual norm.**  `norm_beamRitzResidual_le` in operator form. -/
theorem norm_beamTrialBlock_residual_le (ε : ℝ) :
    ‖(beamTrialBlock ε).residual‖ ≤ orthogonalResidualSingularValue ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · unfold orthogonalResidualSingularValue
    positivity
  · intro x
    rw [beamTrialBlock_residual_apply]
    exact norm_beamRitzResidual_le ε x

/-- The compression form bound, in the shape the trial block's consumer takes. -/
theorem beamTrialBlock_compression_form_le (ε : ℝ) (hε : 0 ≤ ε) (z : beamTrial) :
    RCLike.re ⟪(beamTrialBlock ε).operator z, z⟫_ℂ ≤ ritzHigh ε * ‖z‖ ^ 2 := by
  have hz : ⟪(beamTrialBlock ε).operator z, z⟫_ℂ = ⟪beamResidual ε z, (z : BeamL2)⟫_ℂ := by
    rw [Submodule.coe_inner]
    show ⟪beamTrial.starProjection (beamResidual ε z), (z : BeamL2)⟫_ℂ = _
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 z.2]
  rw [hz]
  exact beamRitz_form_le ε hε z
end

/-! ## Equation (9.6): the tangent envelope for the genuine operator -/

/-- **The largest tangent** of the angles between the affine trial subspace and the
exact low spectral subspace of `A + ε t` -- everything at or below the upper Ritz
value. -/
noncomputable def beamTanTheta (ε : ℝ) : ℝ :=
  ‖theorem63DirectedTangent beamTrial
    (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic)‖

/-- The upper Ritz value stays below `500` on the paper's parameter range. -/
theorem ritzHigh_lt_five_hundred {ε : ℝ} (hε100 : ε < 100) :
    ritzHigh ε < 500 := by
  have hc : ritzHighCoefficient ≤ 1 := by
    unfold ritzHighCoefficient
    have h3 : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 from by
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hcpos : 0 < ritzHighCoefficient := by
    unfold ritzHighCoefficient
    positivity
  unfold ritzHigh
  nlinarith

/-- **Davis--Kahan 1970, equation (9.6), for the genuine free-beam operator.**

The largest tangent of the angles between the affine trial subspace and the exact
low spectral subspace of `A + ε t` is at most the exact Rayleigh--Ritz envelope
`tangentThetaExactBound ε`.

Everything in the hypothesis list is the paper's: `0 < ε < 100`.  The gap is the
proved `beamPerturbed_specProjection_Ioo_eq_zero`, the compression bound is the
proved `beamRitz_form_le`, and the residual norm is the proved
`norm_beamRitzResidual_le`.  No certificate field appears in the statement. -/
theorem beamTanTheta_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε ≤ tangentThetaExactBound ε := by
  have hritz : ritzHigh ε < 500 := ritzHigh_lt_five_hundred hε100
  have hδ : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  have hgap : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Ioo (ritzHigh ε) (ritzHigh ε + (500 - ritzHigh ε))) measurableSet_Ioo = 0 := by
    rw [show ritzHigh ε + (500 - ritzHigh ε) = 500 from by ring]
    exact beamPerturbed_specProjection_Ioo_eq_zero ε hε.le
  have hmain := theorem6_3_unbounded_ideal_directedTangent
    (operatorNormKyFanDominantIdealFamily.{0, 0} ℂ)
    (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) (beamTrialBlock ε) hδ hgap
    (beamTrialBlock_compression_form_le ε hε.le)
    (mem_operatorNormKyFanDominantIdealFamily _)
  have hgauge := hmain.2
  rw [gauge_operatorNormKyFanDominantIdealFamily,
    gauge_operatorNormKyFanDominantIdealFamily] at hgauge
  have hchain : (500 - ritzHigh ε) * beamTanTheta ε
      ≤ orthogonalResidualSingularValue ε :=
    le_trans hgauge (norm_beamTrialBlock_residual_le ε)
  have hden : (1 : ℝ) - ritzHighCoefficient / 500 * ε ≠ 0 := by
    have h : ritzHigh ε = ε * ritzHighCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : tangentThetaExactBound ε
      = orthogonalResidualSingularValue ε / (500 - ritzHigh ε) := by
    unfold tangentThetaExactBound orthogonalResidualSingularValue
    rw [abs_of_pos hε, show ritzHigh ε = ε * ritzHighCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hδ
        exact ne_of_gt hδ)]
    ring
  rw [hbound, le_div_iff₀ hδ]
  linarith [hchain]

/-- **Equation (9.6) as printed.**  The exact envelope, relaxed to the paper's
decimal. -/
theorem beamTanTheta_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε
      < ((1291 : ℝ) / 2500000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  equation_9_6 ε (beamTanTheta ε) hε hε100 (beamTanTheta_le ε hε hε100)

end Model
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
