/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.SpectralTheory.FormMethod.BeamSection9
import DavisKahan.TanTheta.Theorem63Unbounded
import DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound

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
  -- the operator norm, read as the first Ky Fan gauge
  have hmain := theorem6_3_unbounded_ideal_directedTangent
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 1 one_pos)
    (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) (beamTrialBlock ε) hδ hgap
    (beamTrialBlock_compression_form_le ε hε.le)
    (KyFanDominantIdealFamily.kyFan_mem 1 one_pos _)
  have hgauge := hmain.2
  rw [KyFanDominantIdealFamily.kyFan_gauge, KyFanDominantIdealFamily.kyFan_gauge,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hgauge
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

/-! ## The low spectral subspace is exactly two-dimensional

Equations (9.9)--(9.11) reduce the eigenproblem to a two-by-two Schur complement.
That reduction describes the *actual* eigenvectors only if the perturbed operator
really has exactly two spectral dimensions below `500`, and that is a
Rayleigh--Ritz dimension count: coercivity off the trial subspace caps it at
`dim beamTrial`, the Ritz bound attains the cap.

The one hypothesis the general theorem cannot supply is that the low spectral
range lies inside the domain -- `Set.Iic 500` is unbounded below.  Here it does,
because the perturbed beam is positive: the free beam's form is its bending
energy and the perturbation's symbol is `ε t ≥ 0`. -/

/-- **The perturbed beam is positive.** -/
theorem beamPerturbed_form_nonneg (ε : ℝ) (hε : 0 ≤ ε)
    (x : (beamPerturbed ε).toLinearPMap.domain) :
    0 ≤ (⟪(beamPerturbed ε).toLinearPMap x, (x : BeamL2)⟫_ℂ).re := by
  have hxdom : (x : BeamL2) ∈ beamOperator.domain := x.2
  have hsplit : (beamPerturbed ε).toLinearPMap x
      = beamOperator.toLinearMap ⟨(x : BeamL2), hxdom⟩ + beamPerturbation ε (x : BeamL2) :=
    rfl
  rw [hsplit, inner_add_left, Complex.add_re]
  have h1 : 0 ≤ (⟪beamOperator.toLinearMap ⟨(x : BeamL2), hxdom⟩, (x : BeamL2)⟫_ℂ).re :=
    beamShiftedFormData.beam_nonnegative ⟨(x : BeamL2), hxdom⟩
  have h2 := re_inner_beamPerturbation_nonneg ε hε (x : BeamL2)
  linarith

/-- Every negative real is a resolvent point of the perturbed beam. -/
theorem beamPerturbed_mem_resolventSet_of_neg (ε : ℝ) (hε : 0 ≤ ε)
    {lam : ℝ} (hlam : lam < 0) :
    (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet (beamPerturbed ε).toLinearPMap := by
  refine TauCeti.LinearPMap.mem_resolventSet_of_lower_bound
    (beamPerturbed_isSelfAdjoint ε) (by simp) (c := -lam) (by linarith) ?_
  intro x
  rcases eq_or_lt_of_le (norm_nonneg ((x : BeamL2))) with hx0 | hxpos
  · rw [← hx0, mul_zero]
    exact norm_nonneg _
  · have hform := beamPerturbed_form_nonneg ε hε x
    have hCS : (⟪(beamPerturbed ε).toLinearPMap x - (lam : ℂ) • (x : BeamL2),
        (x : BeamL2)⟫_ℂ).re
        ≤ ‖(beamPerturbed ε).toLinearPMap x - (lam : ℂ) • (x : BeamL2)‖ * ‖(x : BeamL2)‖ := by
      exact re_inner_le_norm (𝕜 := ℂ)
        ((beamPerturbed ε).toLinearPMap x - (lam : ℂ) • (x : BeamL2)) ((x : BeamL2))
    have hval : (⟪(beamPerturbed ε).toLinearPMap x - (lam : ℂ) • (x : BeamL2),
        (x : BeamL2)⟫_ℂ).re
        = (⟪(beamPerturbed ε).toLinearPMap x, (x : BeamL2)⟫_ℂ).re
          - lam * ‖(x : BeamL2)‖ ^ 2 := by
      have hself : ⟪(x : BeamL2), (x : BeamL2)⟫_ℂ = ((‖(x : BeamL2)‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
      rw [inner_sub_left, Complex.sub_re, inner_smul_left, Complex.conj_ofReal, hself,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hval] at hCS
    have hsq : -lam * ‖(x : BeamL2)‖ ^ 2
        ≤ ‖(beamPerturbed ε).toLinearPMap x - (lam : ℂ) • (x : BeamL2)‖ * ‖(x : BeamL2)‖ := by
      nlinarith [hform, hCS]
    refine le_of_mul_le_mul_right ?_ hxpos
    nlinarith [hsq]

/-- The perturbed beam has no spectral mass below zero. -/
theorem beamPerturbed_specProjection_Iio_zero (ε : ℝ) (hε : 0 ≤ ε) :
    TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iio 0) measurableSet_Iio = 0 :=
  TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet
    (beamPerturbed_isSelfAdjoint ε) _ _
    (fun _ hlam => beamPerturbed_mem_resolventSet_of_neg ε hε hlam)

/-- Hence the low spectral range lies inside the domain: it is the spectral range
of the *bounded* set `[0, 500]`. -/
theorem beamPerturbed_specRange_le_domain (ε : ℝ) (hε : 0 ≤ ε)
    {y : BeamL2}
    (hy : y ∈ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic) :
    y ∈ (beamPerturbed ε).toLinearPMap.domain := by
  have hfix : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic y = y :=
    (TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).1 hy
  have hsplit : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic
      = TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
          (Set.Iio 0) measurableSet_Iio
        + TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
          (Set.Icc 0 500) measurableSet_Icc := by
    have hunion := (TauCeti.LinearPMap.spectralPVM (beamPerturbed_isSelfAdjoint ε)).proj_union
      (B₁ := Set.Iio (0 : ℝ)) (B₂ := Set.Icc (0 : ℝ) 500)
      measurableSet_Iio measurableSet_Icc
      (by
        rw [Set.disjoint_left]
        rintro t ht htc
        rw [Set.mem_Iio] at ht
        rw [Set.mem_Icc] at htc
        linarith [htc.1])
    have hset : Set.Iio (0 : ℝ) ∪ Set.Icc 0 500 = Set.Iic 500 := by
      ext t
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro (h | ⟨-, h⟩)
        · linarith
        · exact h
      · intro h
        rcases lt_or_ge t 0 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨h0, h⟩
    simp only [TauCeti.LinearPMap.specProjection_def]
    rw [← (TauCeti.LinearPMap.spectralPVM (beamPerturbed_isSelfAdjoint ε)).proj_congr hset
      (measurableSet_Iio.union measurableSet_Icc) measurableSet_Iic, hunion]
  have hy' : TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
      (Set.Icc 0 500) measurableSet_Icc y = y := by
    have h := congrArg (fun T : BeamL2 →L[ℂ] BeamL2 => T y) hsplit
    simp only [add_apply] at h
    rw [beamPerturbed_specProjection_Iio_zero ε hε] at h
    simp only [zero_apply, zero_add] at h
    rw [← h]
    exact hfix
  refine TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded
    (beamPerturbed_isSelfAdjoint ε) _ _ (M := 500) ?_
    ((TauCeti.LinearPMap.mem_specRange_iff _ _ _ _).2 hy')
  intro t ht
  rw [Set.mem_Icc] at ht
  rw [abs_of_nonneg ht.1]
  exact ht.2

/-- **The Rayleigh--Ritz dimension cap for the free beam.**  No finite-dimensional
subspace of the perturbed beam's spectral range below `500` has more dimensions
than the affine trial subspace. -/
theorem beamPerturbed_finrank_le (ε : ℝ) (hε : 0 ≤ ε)
    {W : Submodule ℂ BeamL2} [FiniteDimensional ℂ W]
    (hW : W ≤ TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic 500) measurableSet_Iic) :
    Module.finrank ℂ W ≤ Module.finrank ℂ beamTrial :=
  TauCeti.LinearPMap.finrank_le_of_le_specRange_Iic (beamPerturbed_isSelfAdjoint ε)
    (β := 1001 / 2) (c := 500) (by norm_num)
    (fun y hy => beamPerturbed_form_ge_of_mem_orthogonal ε hε y hy)
    (fun _ hy => beamPerturbed_specRange_le_domain ε hε hy) hW

/-- **The cap is attained.**  The trial subspace injects into the spectral range
below the upper Ritz value, hence into the one below `500`. -/
theorem beamTrial_finrank_le (ε : ℝ) (hε : 0 ≤ ε)
    {W : Submodule ℂ BeamL2} [FiniteDimensional ℂ W]
    (hW : TauCeti.LinearPMap.specRange (beamPerturbed_isSelfAdjoint ε)
      (Set.Iic (ritzHigh ε)) measurableSet_Iic ≤ W) :
    Module.finrank ℂ beamTrial ≤ Module.finrank ℂ W :=
  TauCeti.LinearPMap.finrank_le_finrank_of_le_specRange_Iic
    (beamPerturbed_isSelfAdjoint ε) (α := ritzHigh ε)
    (fun _ hy => beamTrial_le_domain hy)
    (fun y hy => beamPerturbed_form_le_of_mem_beamTrial ε hε y hy) hW

/-- The affine trial subspace is two-dimensional: the two Ritz vectors are an
orthonormal basis of it. -/
theorem finrank_beamTrial : Module.finrank ℂ beamTrial = 2 := by
  classical
  obtain ⟨h1, h2, h12⟩ := beamTrialVec_orthonormal
  have h21 : ⟪beamTrialVecTwo, beamTrialVecOne⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) beamTrialVecTwo beamTrialVecOne, h12, map_zero]
  obtain ⟨n1, n2, -⟩ := beamTrial_orthonormal
  have hb1 : (beamTrialVecOne : BeamL2) = centeredAffineLp trialOne := rfl
  have hb2 : (beamTrialVecTwo : BeamL2) = centeredAffineLp trialTwo := rfl
  have hn1 : ‖(beamTrialVecOne : BeamL2)‖ = 1 := by
    rw [hb1]
    nlinarith [n1, norm_nonneg (centeredAffineLp trialOne)]
  have hn2 : ‖(beamTrialVecTwo : BeamL2)‖ = 1 := by
    rw [hb2]
    nlinarith [n2, norm_nonneg (centeredAffineLp trialTwo)]
  have horth : Orthonormal ℂ (![beamTrialVecOne, beamTrialVecTwo] : Fin 2 → beamTrial) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h12, h21, hn1, hn2]
  have hrange : Set.range (![beamTrialVecOne, beamTrialVecTwo] : Fin 2 → beamTrial)
      = {beamTrialVecOne, beamTrialVecTwo} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : ⊤ ≤ Submodule.span ℂ
      (Set.range (![beamTrialVecOne, beamTrialVecTwo] : Fin 2 → beamTrial)) := by
    rw [hrange, beamTrialVec_span_eq_top]
  have hbasis : Module.Basis (Fin 2) ℂ beamTrial :=
    Module.Basis.mk horth.linearIndependent hspan
  rw [Module.finrank_eq_card_basis hbasis]
  simp

end Model
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
