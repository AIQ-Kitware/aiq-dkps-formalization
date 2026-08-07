/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.SpectralTheory.FormMethod.BeamSpectrum
import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.SinTheta.BoundedPerturbation
import DavisKahan.Sources.DavisKahan1970.Section9.ExactData
import DavisKahan.Sources.DavisKahan1970.Section9.TrialSubspace
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport
import ForTauCeti.MeasureTheory.MulLpAlgebra

/-!
# The Davis--Kahan Section 9 free-beam example, on the genuine operator

`BeamSpectrum` produced the self-adjoint fourth-derivative realization
`beamOperator`, identified its kernel as the affine plane, and proved the spectral
gap `realSpectrum ⊆ {0} ∪ (500, ∞)`.  This file assembles the remaining *finite*
data of the paper's numerical example around that operator:

* `beamTrial`, the two-dimensional affine trial subspace, is exactly the kernel;
* `beamPerturbation ε`, multiplication by `ε t`, is the paper's bounded perturbation,
  self-adjoint with norm at most `ε`;
* the exact `L²` moments of affine functions against `1`, `t` and `t²` — this is the
  "moments to integrals" identification that the Section 9 finite layer
  (`TrialSubspace.lean`) was written against;
* the residual norm bound `‖(ε t)|_trial‖ ≤ residualTopSingularValue ε`, whose
  constant is the square root of the top eigenvalue of the residual Gram matrix.

## Main results

* `TauCeti.…FreeBeam.Model.beamTrial_eq_ker`: the trial space is the kernel.
* `TauCeti.…FreeBeam.Model.norm_beamPerturbation_comp_trialIncl_le`: the residual bound.
-/

open MeasureTheory
open TauCeti.DavisKahan.Experimental
open TauCeti.DavisKahan.Experimental.ExactSinTheta
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Model

noncomputable section

/-! ## Complex integrals on the unit interval -/

/-- The ambient measure integrates complex integrands as interval integrals. -/
theorem integral_unitIocMeasure_complex (f : ℝ → ℂ) :
    ∫ t, f t ∂unitIocMeasure = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure_def]

/-- Exact monomial moments of the unit interval. -/
theorem integral_unitIocMeasure_pow (n : ℕ) :
    ∫ t, ((t : ℂ)) ^ n ∂unitIocMeasure = 1 / (n + 1) := by
  have hre : ∀ t : ℝ, ((t : ℂ)) ^ n = (((t ^ n : ℝ)) : ℂ) := by
    intro t
    push_cast
    ring
  simp only [hre]
  rw [integral_complex_ofReal, integral_unitIocMeasure_eq_intervalIntegral]
  rw [integral_pow]
  push_cast
  ring

/-! ## The affine trial subspace -/

/-- The two-dimensional affine trial subspace of the paper's numerical example. -/
def beamTrial : Submodule ℂ BeamL2 := Submodule.span ℂ {beamOneLp, beamIdLp}

theorem mem_beamTrial_iff {x : BeamL2} :
    x ∈ beamTrial ↔ ∃ a b : ℂ, x = affineLp a b := by
  rw [beamTrial, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, rfl⟩

theorem affineLp_mem_beamTrial (a b : ℂ) : affineLp a b ∈ beamTrial :=
  mem_beamTrial_iff.2 ⟨a, b, rfl⟩

instance : FiniteDimensional ℂ beamTrial := by
  rw [beamTrial]
  exact FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

instance : CompleteSpace beamTrial := FiniteDimensional.complete ℂ _

/-- The trial subspace lies in the operator's domain: it is the affine kernel
identified in `BeamSpectrum`. -/
theorem beamTrial_le_domain {x : BeamL2} (hx : x ∈ beamTrial) :
    x ∈ beamOperator.domain := by
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hx
  exact (beamOperator_affine_mem_and_zero a b).choose

/-- The beam operator annihilates the trial subspace. -/
theorem beamOperator_apply_trial {x : BeamL2} (hx : x ∈ beamTrial)
    (h : x ∈ beamOperator.domain) :
    beamOperator.toLinearMap ⟨x, h⟩ = 0 := by
  obtain ⟨a, b, rfl⟩ := mem_beamTrial_iff.1 hx
  exact (beamOperator_affine_mem_and_zero a b).choose_spec

/-- The isometric inclusion of the trial subspace. -/
def beamTrialIncl : beamTrial →L[ℂ] BeamL2 := beamTrial.subtypeL

@[simp] theorem beamTrialIncl_apply (x : beamTrial) :
    beamTrialIncl x = (x : BeamL2) := rfl

/-! ## The multiplication perturbation `ε t` -/

/-- The unit-interval coordinate, clamped so that the symbol is globally bounded. -/
def beamClamp (t : ℝ) : ℝ := max 0 (min t 1)

theorem measurable_beamClamp : Measurable beamClamp :=
  measurable_const.max (measurable_id.min measurable_const)

theorem beamClamp_nonneg (t : ℝ) : 0 ≤ beamClamp t := le_max_left _ _

theorem beamClamp_le_one (t : ℝ) : beamClamp t ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem beamClamp_eq_self {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : beamClamp t = t := by
  rw [beamClamp, min_eq_left ht.2, max_eq_right ht.1.le]

/-- The symbol of the paper's perturbation: `ε` times the clamped coordinate. -/
def beamSymbol (ε : ℝ) (t : ℝ) : ℂ := ((ε * beamClamp t : ℝ) : ℂ)

theorem measurable_beamSymbol (ε : ℝ) : Measurable (beamSymbol ε) :=
  Complex.measurable_ofReal.comp (measurable_const.mul measurable_beamClamp)

theorem norm_beamSymbol_le (ε : ℝ) (t : ℝ) : ‖beamSymbol ε t‖ ≤ |ε| := by
  rw [beamSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (beamClamp_nonneg t)]
  calc |ε| * beamClamp t ≤ |ε| * 1 :=
        mul_le_mul_of_nonneg_left (beamClamp_le_one t) (abs_nonneg ε)
    _ = |ε| := mul_one _

/-- **The Section 9 perturbation**: multiplication by `ε t` on `L²(0,1]`. -/
def beamPerturbation (ε : ℝ) : BeamL2 →L[ℂ] BeamL2 :=
  mulLp unitIocMeasure (measurable_beamSymbol ε) (norm_beamSymbol_le ε)

theorem coeFn_beamPerturbation (ε : ℝ) (x : BeamL2) :
    (beamPerturbation ε x : ℝ → ℂ) =ᵐ[unitIocMeasure]
      fun t => ((ε * t : ℝ) : ℂ) * (x : ℝ → ℂ) t := by
  filter_upwards [coeFn_mulLp unitIocMeasure (measurable_beamSymbol ε)
    (norm_beamSymbol_le ε) x, ae_mem_unitIocMeasure] with t ht hmem
  rw [show (beamPerturbation ε x : ℝ → ℂ) t
    = (mulLp unitIocMeasure (measurable_beamSymbol ε) (norm_beamSymbol_le ε) x :
        ℝ → ℂ) t from rfl, ht, beamSymbol, beamClamp_eq_self hmem]

theorem norm_beamPerturbation_le (ε : ℝ) : ‖beamPerturbation ε‖ ≤ |ε| := by
  have := norm_mulLp_le unitIocMeasure (measurable_beamSymbol ε) (norm_beamSymbol_le ε)
  simpa [beamPerturbation, abs_abs] using this

/-! ## Inner products of continuous representatives -/

/-- The `L²` inner product of two continuous representatives is the integral of the
pointwise product. -/
theorem inner_contToLp (g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h) :
    ⟪contToLp g hg, contToLp h hh⟫_ℂ
      = ∫ t, (starRingEnd ℂ) (g t) * h t ∂unitIocMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_contToLp g hg, coeFn_contToLp h hh] with t htg hth
  rw [htg, hth, RCLike.inner_apply]
  ring

/-- Read off the squared `L²` norm of a continuous representative from an explicit
value of its self-pairing integral. -/
theorem norm_sq_contToLp (g : ℝ → ℂ) (hg : Continuous g) {r : ℝ}
    (h : ∫ t, (starRingEnd ℂ) (g t) * g t ∂unitIocMeasure = (r : ℂ)) :
    ‖contToLp g hg‖ ^ 2 = r := by
  have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (contToLp g hg)
  rw [inner_contToLp g g hg hg, h] at hself
  have hcast : (((‖contToLp g hg‖ ^ 2 : ℝ)) : ℂ) = ((r : ℝ) : ℂ) := by
    push_cast
    exact hself.symm
  exact_mod_cast hcast

/-! ## Affine elements as continuous representatives -/

/-- Affine elements of the trial space are the continuous affine functions. -/
theorem affineLp_eq_contToLp (a b : ℂ) :
    affineLp a b = contToLp (fun t => a + b * t) (by fun_prop) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
    coeFn_beamIdLp, coeFn_contToLp (fun t => a + b * t) (by fun_prop)] with
    t hadd hsa hsb h1 hT hc
  rw [show (affineLp a b : ℝ → ℂ) t
    = ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℂ) t from rfl, hadd, hc]
  simp only [Pi.add_apply, hsa, hsb, Pi.smul_apply, smul_eq_mul, h1, hT]
  ring

/-- The perturbation of an affine element is the continuous function `ε t (a + b t)`. -/
theorem beamPerturbation_affineLp (ε : ℝ) (a b : ℂ) :
    beamPerturbation ε (affineLp a b)
      = contToLp (fun t => ((ε : ℂ) * t) * (a + b * t)) (by fun_prop) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_beamPerturbation ε (affineLp a b),
    coeFn_contToLp (fun t => ((ε : ℂ) * t) * (a + b * t)) (by fun_prop),
    coeFn_contToLp (fun t => a + b * t) (by fun_prop)] with t hp hc ha
  rw [hp, hc, affineLp_eq_contToLp, ha]
  push_cast
  ring

/-! ## The exact affine moments -/

/-- Continuous functions are integrable against the finite unit-interval measure. -/
theorem integrable_contFn (g : ℝ → ℂ) (hg : Continuous g) :
    Integrable g unitIocMeasure :=
  (integrable_coeFn (contToLp g hg)).congr (coeFn_contToLp g hg)

/-- Exact monomial moments, in the normalized form the polynomial lemmas consume. -/
theorem integral_unitIocMeasure_coe : ∫ t : ℝ, (t : ℂ) ∂unitIocMeasure = 1 / 2 := by
  have h := integral_unitIocMeasure_pow 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h]
  norm_num

theorem integral_unitIocMeasure_coe_sq :
    ∫ t : ℝ, (t : ℂ) ^ 2 ∂unitIocMeasure = 1 / 3 := by
  have h := integral_unitIocMeasure_pow 2
  rw [h]
  norm_num

theorem integral_unitIocMeasure_coe_cube :
    ∫ t : ℝ, (t : ℂ) ^ 3 ∂unitIocMeasure = 1 / 4 := by
  have h := integral_unitIocMeasure_pow 3
  rw [h]
  norm_num

theorem integral_unitIocMeasure_coe_four :
    ∫ t : ℝ, (t : ℂ) ^ 4 ∂unitIocMeasure = 1 / 5 := by
  have h := integral_unitIocMeasure_pow 4
  rw [h]
  norm_num

/-- Exact integral of a quadratic with complex coefficients. -/
theorem integral_unitIocMeasure_quadratic (c0 c1 c2 : ℂ) :
    ∫ t, (c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2) ∂unitIocMeasure
      = c0 + c1 / 2 + c2 / 3 := by
  have hi01 : Integrable (fun t : ℝ => c0 + c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi0 : Integrable (fun _ : ℝ => c0) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi1 : Integrable (fun t : ℝ => c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi2 : Integrable (fun t : ℝ => c2 * (t : ℂ) ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  rw [integral_add hi01 hi2, integral_add hi0 hi1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_unitIocMeasure_coe, integral_unitIocMeasure_coe_sq,
    MeasureTheory.integral_const]
  have huniv : unitIocMeasure.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, measure_univ]
    simp
  rw [huniv, one_smul]
  ring

/-- Exact integral of a quartic with complex coefficients. -/
theorem integral_unitIocMeasure_quartic (c0 c1 c2 c3 c4 : ℂ) :
    ∫ t, (c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2 + c3 * (t : ℂ) ^ 3
        + c4 * (t : ℂ) ^ 4) ∂unitIocMeasure
      = c0 + c1 / 2 + c2 / 3 + c3 / 4 + c4 / 5 := by
  have hi0 : Integrable (fun _ : ℝ => c0) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi1 : Integrable (fun t : ℝ => c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi2 : Integrable (fun t : ℝ => c2 * (t : ℂ) ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi3 : Integrable (fun t : ℝ => c3 * (t : ℂ) ^ 3) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi4 : Integrable (fun t : ℝ => c4 * (t : ℂ) ^ 4) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi01 : Integrable (fun t : ℝ => c0 + c1 * (t : ℂ)) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi012 : Integrable
      (fun t : ℝ => c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2) unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  have hi0123 : Integrable
      (fun t : ℝ => c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2 + c3 * (t : ℂ) ^ 3)
      unitIocMeasure :=
    integrable_contFn _ (by fun_prop)
  rw [integral_add hi0123 hi4, integral_add hi012 hi3, integral_add hi01 hi2,
    integral_add hi0 hi1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_unitIocMeasure_coe, integral_unitIocMeasure_coe_sq,
    integral_unitIocMeasure_coe_cube, integral_unitIocMeasure_coe_four,
    MeasureTheory.integral_const]
  have huniv : unitIocMeasure.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, measure_univ]
    simp
  rw [huniv, one_smul]
  ring

/-! ## The exact affine norms -/

/-- The `L²` norm of an affine element, in the real coordinates
`‖a‖²`, `2 Re(conj a · b)`, `‖b‖²` of its coefficient pair.  This is the
`moments to integrals` identification: the value is
`CenteredAffine.inner` of the pair with itself. -/
theorem norm_affineLp_sq (a b : ℂ) :
    ‖affineLp a b‖ ^ 2
      = ‖a‖ ^ 2 + (2 * ((starRingEnd ℂ) a * b).re) / 2 + ‖b‖ ^ 2 / 3 := by
  rw [affineLp_eq_contToLp]
  refine norm_sq_contToLp _ _ ?_
  have hpt : ∀ t : ℝ, (starRingEnd ℂ) (a + b * (t : ℂ)) * (a + b * (t : ℂ))
      = ((starRingEnd ℂ) a * a)
        + ((starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a) * (t : ℂ)
        + ((starRingEnd ℂ) b * b) * (t : ℂ) ^ 2 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quadratic]
  have ha : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hb : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcross : (starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a
      = ((2 * ((starRingEnd ℂ) a * b).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj ((starRingEnd ℂ) a * b)]
    congr 1
    simp [mul_comm]
  rw [ha, hb, hcross]
  push_cast
  ring

/-- The `L²` norm of the perturbed affine element: the `t²`-weighted moments. -/
theorem norm_beamPerturbation_affineLp_sq (ε : ℝ) (a b : ℂ) :
    ‖beamPerturbation ε (affineLp a b)‖ ^ 2
      = ε ^ 2 * (‖a‖ ^ 2 / 3 + (2 * ((starRingEnd ℂ) a * b).re) / 4
        + ‖b‖ ^ 2 / 5) := by
  rw [beamPerturbation_affineLp]
  refine norm_sq_contToLp _ _ ?_
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (((ε : ℂ) * (t : ℂ)) * (a + b * (t : ℂ)))
          * (((ε : ℂ) * (t : ℂ)) * (a + b * (t : ℂ)))
      = 0 + 0 * (t : ℂ)
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * a)) * (t : ℂ) ^ 2
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a))
            * (t : ℂ) ^ 3
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) b * b)) * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  have ha : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hb : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hcross : (starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a
      = ((2 * ((starRingEnd ℂ) a * b).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj ((starRingEnd ℂ) a * b)]
    congr 1
    simp [mul_comm]
  rw [ha, hb, hcross]
  push_cast
  ring

/-! ## The residual bound -/

/-- The exact Rayleigh quotient inequality behind the residual singular value: the
`t²` moment form is dominated by `(11 + √76)/30` times the `L²` form.  The constant
is sharp — it is the top eigenvalue of the residual Gram matrix — so the
discriminant of the difference vanishes identically. -/
theorem residual_quadratic_bound {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : B ^ 2 ≤ 4 * A * C) :
    A / 3 + B / 4 + C / 5 ≤ (11 + Real.sqrt 76) / 30 * (A + B / 2 + C / 3) := by
  have hs : Real.sqrt 76 ^ 2 = 76 := Real.sq_sqrt (by norm_num)
  have hsnn : 0 ≤ Real.sqrt 76 := Real.sqrt_nonneg _
  have hs8 : 8 < Real.sqrt 76 := by nlinarith
  set s := Real.sqrt 76 with hsdef
  -- the claim is `0 ≤ u A + v B + w C` with `u = 6 + 6 s`, `v = 3 s - 12`,
  -- `w = 2 s - 14`, all positive, and `u w = v ^ 2`
  have hkey : 0 ≤ (6 + 6 * s) * A + (3 * s - 12) * B + (2 * s - 14) * C := by
    rcases le_or_gt 0 B with hBpos | hBneg
    · have h1 : 0 ≤ (6 + 6 * s) * A := by positivity
      have h2 : 0 ≤ (3 * s - 12) * B := mul_nonneg (by linarith) hBpos
      have h3 : 0 ≤ (2 * s - 14) * C := mul_nonneg (by linarith) hC
      linarith
    · -- `(u A + w C)² ≥ 4 u w A C = 4 v² A C ≥ v² B²`, and both sides are nonnegative
      have huw : (6 + 6 * s) * (2 * s - 14) = (3 * s - 12) ^ 2 := by nlinarith
      have hsum : 0 ≤ (6 + 6 * s) * A + (2 * s - 14) * C := by
        have h1 : 0 ≤ (6 + 6 * s) * A := by positivity
        have h3 : 0 ≤ (2 * s - 14) * C := mul_nonneg (by linarith) hC
        linarith
      have hsq : ((3 * s - 12) * B) ^ 2
          ≤ ((6 + 6 * s) * A + (2 * s - 14) * C) ^ 2 := by
        have hAC : (3 * s - 12) ^ 2 * B ^ 2 ≤ (3 * s - 12) ^ 2 * (4 * A * C) :=
          mul_le_mul_of_nonneg_left hB (sq_nonneg _)
        nlinarith [sq_nonneg ((6 + 6 * s) * A - (2 * s - 14) * C)]
      nlinarith [hsq, hsum]
  linarith

/-- Every affine element is compressed by the perturbation with the residual's top
singular value.  This is the exact operator-norm content of the Section 9 residual
Gram matrix. -/
theorem norm_beamPerturbation_affineLp_le (ε : ℝ) (a b : ℂ) :
    ‖beamPerturbation ε (affineLp a b)‖
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε * ‖affineLp a b‖ := by
  set A : ℝ := ‖a‖ ^ 2 with hAdef
  set C : ℝ := ‖b‖ ^ 2 with hCdef
  set B : ℝ := 2 * ((starRingEnd ℂ) a * b).re with hBdef
  have hA : 0 ≤ A := by positivity
  have hC : 0 ≤ C := by positivity
  have hBsq : B ^ 2 ≤ 4 * A * C := by
    have hre : |((starRingEnd ℂ) a * b).re| ≤ ‖(starRingEnd ℂ) a * b‖ :=
      Complex.abs_re_le_norm _
    have hnorm : ‖(starRingEnd ℂ) a * b‖ = ‖a‖ * ‖b‖ := by
      rw [norm_mul, RCLike.norm_conj]
    rw [hnorm] at hre
    have := sq_le_sq' (neg_abs_le _) (le_abs_self ((((starRingEnd ℂ) a * b)).re))
    nlinarith [abs_nonneg ((((starRingEnd ℂ) a * b)).re), norm_nonneg a, norm_nonneg b]
  -- both sides are nonnegative, so compare squares
  have hlhs := norm_beamPerturbation_affineLp_sq ε a b
  have hrhs := norm_affineLp_sq a b
  have hsq : ‖beamPerturbation ε (affineLp a b)‖ ^ 2
      ≤ (DavisKahan1970.Section9.residualTopSingularValue ε * ‖affineLp a b‖) ^ 2 := by
    rw [mul_pow, DavisKahan1970.Section9.residualTopSingularValue_sq, hlhs, hrhs]
    rw [DavisKahan1970.Section9.residualGramEigenvalueHigh]
    have hq := residual_quadratic_bound hA hC hBsq
    nlinarith [sq_nonneg ε, hq]
  have hnn : 0 ≤ DavisKahan1970.Section9.residualTopSingularValue ε * ‖affineLp a b‖ := by
    refine mul_nonneg ?_ (norm_nonneg _)
    rw [DavisKahan1970.Section9.residualTopSingularValue]
    positivity
  nlinarith [norm_nonneg (beamPerturbation ε (affineLp a b)), hsq, hnn]

/-- **The Section 9 residual bound.**  Restricted to the affine trial subspace, the
perturbation `ε t` has operator norm at most `residualTopSingularValue ε`. -/
theorem norm_beamPerturbation_comp_trialIncl_le (ε : ℝ) :
    ‖beamPerturbation ε ∘L beamTrialIncl‖
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · rw [DavisKahan1970.Section9.residualTopSingularValue]
    positivity
  · intro x
    obtain ⟨a, b, hab⟩ := mem_beamTrial_iff.1 x.2
    have hx : (x : BeamL2) = affineLp a b := hab
    have hnorm : ‖x‖ = ‖affineLp a b‖ := by rw [← hx]; rfl
    rw [ContinuousLinearMap.comp_apply, beamTrialIncl_apply, hx, hnorm]
    exact norm_beamPerturbation_affineLp_le ε a b

/-! ## The perturbed operator and its high spectral subspace -/

/-- The perturbation is self-adjoint: its symbol is real. -/
theorem beamPerturbation_isSelfAdjoint (ε : ℝ) :
    DavisKahan.IsSelfAdjointOperator (beamPerturbation ε) := by
  intro x y
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_beamPerturbation ε x, coeFn_beamPerturbation ε y] with t hx hy
  simp only [RCLike.inner_apply, ContinuousLinearMap.coe_coe, hx, hy, map_mul,
    Complex.conj_ofReal]
  ring

/-- **The exact operator of the Section 9 example**: the free beam perturbed by
multiplication by `ε t`. -/
def beamPerturbed (ε : ℝ) : DKClosedOperator (H := BeamL2) :=
  beamOperator.addBounded (beamPerturbation ε)

theorem beamPerturbed_isSelfAdjoint (ε : ℝ) : (beamPerturbed ε).IsSelfAdjoint :=
  addBounded_isSelfAdjoint beamOperator beamOperator_isSelfAdjoint _
    (beamPerturbation_isSelfAdjoint ε)

/-- The spectral set that isolates everything above the free-beam gap. -/
def beamHighSet : Set ℝ := Set.Ici 500

theorem measurableSet_beamHighSet : MeasurableSet beamHighSet := measurableSet_Ici

/-- The zero operator on the trial subspace: the compression of the free beam to its
own kernel, which is the trial subspace itself. -/
def beamTrialZero : DKClosedOperator (H := beamTrial) :=
  DavisKahanExt.ClosedOperator.ofBounded 0

theorem beamTrialZero_isSelfAdjoint : beamTrialZero.IsSelfAdjoint :=
  DavisKahanExt.ClosedOperator.ofBounded_isSelfAdjoint 0 (fun _ _ => by simp)

/-- **The largest sine of the angle** between the affine trial subspace and the exact
low spectral subspace of the perturbed beam: the operator norm of the cross projection
onto the exact spectral subspace above the gap. -/
def beamSinTheta (ε : ℝ) : ℝ :=
  ‖ContinuousLinearMap.adjoint beamTrialIncl ∘L
      selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖

theorem beamSinTheta_nonneg (ε : ℝ) : 0 ≤ beamSinTheta ε :=
  norm_nonneg (ContinuousLinearMap.adjoint beamTrialIncl ∘L
    selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)

/-- **Davis--Kahan 1970, equation (9.1), for the genuine free-beam operator.**  The
sine of the angle between the affine trial subspace and the exact low spectral
subspace of `A + ε t` is bounded by the residual's top singular value over the
spectral gap `500`.  Nothing here is assumed: the gap comes from
`realSpectrum_beamOperator_subset_gap`, the trial space is the proved kernel, and the
residual norm is the proved `t²`-moment bound. -/
theorem beamSinTheta_le (ε : ℝ) :
    beamSinTheta ε ≤ DavisKahan1970.Section9.residualTopSingularValue ε / 500 := by
  classical
  have hXdom : ∀ x : beamTrialZero.domain,
      beamTrialIncl (x : beamTrial) ∈ beamOperator.domain := fun x =>
    beamTrial_le_domain (x : beamTrial).2
  have hXint : ∀ x : beamTrialZero.domain,
      beamOperator.toLinearMap ⟨beamTrialIncl (x : beamTrial), hXdom x⟩
        = beamTrialIncl (beamTrialZero.toLinearMap x) := by
    intro x
    have hz : beamTrialZero.toLinearMap x = 0 := rfl
    rw [hz, map_zero]
    exact beamOperator_apply_trial (x : beamTrial).2 _
  have hlow : SemiboundedBelow beamTrialZero 0 := by
    intro x
    have hz : beamTrialZero.toLinearPMap x = 0 := rfl
    rw [hz, inner_zero_left]
    simp
  have hhigh : SemiboundedAbove beamTrialZero 0 := by
    intro x
    have hz : beamTrialZero.toLinearPMap x = 0 := rfl
    rw [hz, inner_zero_left]
    simp
  have hspec := selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε) beamHighSet
      measurableSet_beamHighSet (a := (0 : ℝ) - 500) (b := (0 : ℝ) + 500) (by
        refine Set.eq_empty_iff_forall_notMem.2 ?_
        rintro lam ⟨hlam, -, h2⟩
        have hge : (500 : ℝ) ≤ lam := hlam
        have hlt : lam < (0 : ℝ) + 500 := h2
        linarith)
  have hmain := sinTheta_unbounded_opNorm_of_spectrum_gap
    (boundedPerturbationSinThetaData beamOperator (beamPerturbation ε) beamTrialZero
      (selfAdjointSpectralRestriction (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamHighSet measurableSet_beamHighSet)
      beamTrialIncl
      (selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      hXdom hXint
      (selfAdjointSpectralRestriction_inclusion_mem_domain (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
      (selfAdjointSpectralRestriction_inclusion_intertwines (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet))
    (beamPerturbed_isSelfAdjoint ε) beamTrialZero_isSelfAdjoint
    (selfAdjointSpectralRestriction_isSelfAdjoint (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
    (β := 0) (α := 0) (δ := 500) le_rfl (by norm_num) hlow hhigh hspec
  have hF₁norm : ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
      (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ ≤ 1 :=
    opNorm_le_one_of_isometry
      (selfAdjointSpectralSubspaceInclusion_isometric (beamPerturbed ε)
        (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet)
  have hres : ‖ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
        selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
          (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε := by
    calc ‖ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl) ∘L
            selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖
        ≤ ‖ContinuousLinearMap.adjoint (beamPerturbation ε ∘L beamTrialIncl)‖ *
            ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖beamPerturbation ε ∘L beamTrialIncl‖ *
            ‖selfAdjointSpectralSubspaceInclusion (beamPerturbed ε)
              (beamPerturbed_isSelfAdjoint ε) beamHighSet measurableSet_beamHighSet‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ ‖beamPerturbation ε ∘L beamTrialIncl‖ * 1 :=
          mul_le_mul_of_nonneg_left hF₁norm
            (norm_nonneg (beamPerturbation ε ∘L beamTrialIncl))
      _ = ‖beamPerturbation ε ∘L beamTrialIncl‖ := mul_one _
      _ ≤ DavisKahan1970.Section9.residualTopSingularValue ε :=
          norm_beamPerturbation_comp_trialIncl_le ε
  have hchain : 500 * beamSinTheta ε
      ≤ DavisKahan1970.Section9.residualTopSingularValue ε := le_trans hmain hres
  linarith

/-! ## The spectral subspace below the gap -/

/-- The spectral set below the free-beam gap.  The threshold `1001/2 = 500.5` is chosen
below `4.73⁴ = 500.546…` and above the paper's rounded `500`, so it separates the zero
modes from the whole positive spectrum with room to spare. -/
def beamLowSet : Set ℝ := Set.Iic (1001 / 2)

theorem measurableSet_beamLowSet : MeasurableSet beamLowSet := measurableSet_Iic

/-- **The free-beam gap, sharpened past the paper's rounding.**  The positive spectrum
clears `500.5`, not merely `500`: the characteristic roots exceed `4.73` and
`4.73⁴ = 500.5466…`. -/
theorem realSpectrum_beamOperator_subset_sharp :
    beamOperator.realSpectrum ⊆ ({0} : Set ℝ) ∪ Set.Ioi (1001 / 2) := by
  intro lam hlam
  rcases realSpectrum_beamOperator_subset hlam with h0 | ⟨beta, hbeta, hchar, hlameq⟩
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Set.mem_Ioi, hlameq]
    have h473 := Classical.four_seventy_three_lt_of_characteristic_eq_zero hbeta hchar
    have hpow : ((473 : ℝ) / 100) ^ 4 < beta ^ 4 :=
      pow_lt_pow_left₀ h473 (by norm_num) (by norm_num)
    have hnum : (1001 : ℝ) / 2 < ((473 : ℝ) / 100) ^ 4 := by norm_num
    linarith

/-- Every nonzero point below the gap is a resolvent point of the free beam. -/
theorem beamOperator_mem_resolventSet_of_mem_lowSet_diff {lam : ℝ}
    (hlam : lam ∈ beamLowSet \ ({0} : Set ℝ)) :
    (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet beamOperator.toLinearPMap := by
  by_contra hcon
  have hmem : lam ∈ beamOperator.realSpectrum := fun hr => hcon hr
  rcases realSpectrum_beamOperator_subset_sharp hmem with h0 | hgt
  · exact hlam.2 h0
  · have hle : lam ≤ (1001 : ℝ) / 2 := hlam.1
    exact absurd hgt (by simp only [Set.mem_Ioi, not_lt]; exact hle)

/-- The spectral measure of the punctured region below the gap vanishes. -/
theorem beamSpecProjection_lowSet_diff_eq_zero :
    TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint
        (beamLowSet \ ({0} : Set ℝ))
        (measurableSet_beamLowSet.diff (measurableSet_singleton 0)) = 0 :=
  TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet
    beamOperator_isSelfAdjoint _ _
    (fun _ hlam => beamOperator_mem_resolventSet_of_mem_lowSet_diff hlam)

/-- **Everything below the gap is a zero mode**: the spectral projection of the whole
region below `500.5` is the projection onto the kernel eigenvalue `{0}`. -/
theorem beamSpecProjection_lowSet_eq_singleton :
    TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint beamLowSet
        measurableSet_beamLowSet
      = TauCeti.LinearPMap.specProjection beamOperator_isSelfAdjoint
        ({0} : Set ℝ) (measurableSet_singleton 0) := by
  have hsplit : ({0} : Set ℝ) ∪ (beamLowSet \ ({0} : Set ℝ)) = beamLowSet := by
    refine Set.union_sdiff_cancel ?_
    intro lam hlam
    rw [Set.mem_singleton_iff] at hlam
    rw [hlam]
    exact Set.mem_Iic.2 (by norm_num)
  have hdisj : Disjoint ({0} : Set ℝ) (beamLowSet \ ({0} : Set ℝ)) :=
    Set.disjoint_sdiff_right
  have hunion := (TauCeti.LinearPMap.spectralPVM beamOperator_isSelfAdjoint).proj_union
    (measurableSet_singleton 0)
    (measurableSet_beamLowSet.diff (measurableSet_singleton 0)) hdisj
  rw [TauCeti.LinearPMap.specProjection_def, TauCeti.LinearPMap.specProjection_def]
  rw [← (TauCeti.LinearPMap.spectralPVM beamOperator_isSelfAdjoint).proj_congr hsplit
    ((measurableSet_singleton 0).union
      (measurableSet_beamLowSet.diff (measurableSet_singleton 0)))
    measurableSet_beamLowSet, hunion]
  have hzero := beamSpecProjection_lowSet_diff_eq_zero
  rw [TauCeti.LinearPMap.specProjection_def] at hzero
  rw [hzero, add_zero]

/-- A vector selected below the gap is selected by the kernel eigenvalue. -/
theorem mem_specRange_singleton_of_mem_lowSet {y : BeamL2}
    (hy : y ∈ TauCeti.LinearPMap.specRange beamOperator_isSelfAdjoint beamLowSet
      measurableSet_beamLowSet) :
    y ∈ TauCeti.LinearPMap.specRange beamOperator_isSelfAdjoint ({0} : Set ℝ)
      (measurableSet_singleton 0) := by
  rw [TauCeti.LinearPMap.mem_specRange_iff] at hy ⊢
  rw [← beamSpecProjection_lowSet_eq_singleton]
  exact hy

/-- The compression of the free beam to the spectral subspace below the gap is zero:
both form bounds are `0`. -/
theorem beamLow_semiboundedBelow :
    SemiboundedBelow (selfAdjointSpectralRestriction beamOperator
      beamOperator_isSelfAdjoint beamLowSet measurableSet_beamLowSet) 0 := by
  intro x
  exact (TauCeti.LinearPMap.re_inner_apply_bounds_of_subset_Icc
    beamOperator_isSelfAdjoint ({0} : Set ℝ) (measurableSet_singleton 0)
    (β := 0) (α := 0) (by simp) (mem_specRange_singleton_of_mem_lowSet x.1.2) x.2).1

theorem beamLow_semiboundedAbove :
    SemiboundedAbove (selfAdjointSpectralRestriction beamOperator
      beamOperator_isSelfAdjoint beamLowSet measurableSet_beamLowSet) 0 := by
  intro x
  exact (TauCeti.LinearPMap.re_inner_apply_bounds_of_subset_Icc
    beamOperator_isSelfAdjoint ({0} : Set ℝ) (measurableSet_singleton 0)
    (β := 0) (α := 0) (by simp) (mem_specRange_singleton_of_mem_lowSet x.1.2) x.2).2

/-! ## Equation (9.2): the double-angle bound -/

/-- **The largest sine of twice the angle** between the free beam's zero-mode spectral
subspace and the low spectral subspace of the perturbed operator. -/
def beamSinTwoTheta (ε : ℝ) : ℝ :=
  ‖DavisKahanExt.sinTwoAngleOperatorC
      (selfAdjointSpectralSubspace beamOperator beamOperator_isSelfAdjoint beamLowSet
        measurableSet_beamLowSet)
      (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamLowSet measurableSet_beamLowSet)‖

theorem beamSinTwoTheta_nonneg (ε : ℝ) : 0 ≤ beamSinTwoTheta ε :=
  norm_nonneg (DavisKahanExt.sinTwoAngleOperatorC
      (selfAdjointSpectralSubspace beamOperator beamOperator_isSelfAdjoint beamLowSet
        measurableSet_beamLowSet)
      (selfAdjointSpectralSubspace (beamPerturbed ε) (beamPerturbed_isSelfAdjoint ε)
        beamLowSet measurableSet_beamLowSet))

/-- The complement of the low set avoids the gap interval, so the free beam's
complementary block has no spectrum there. -/
theorem beamHigh_spectrum_avoids :
    ∀ lam ∈ Set.Ioo ((0 : ℝ) - 1001 / 2) ((0 : ℝ) + 1001 / 2),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction beamOperator beamOperator_isSelfAdjoint
          beamLowSetᶜ measurableSet_beamLowSet.compl).toLinearPMap :=
  selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
    beamOperator beamOperator_isSelfAdjoint beamLowSetᶜ measurableSet_beamLowSet.compl
    (by
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro lam ⟨hlam, -, h2⟩
      have hgt : (1001 : ℝ) / 2 < lam := by
        simpa only [beamLowSet, Set.mem_compl_iff, Set.mem_Iic, not_le] using hlam
      have hlt : lam < (0 : ℝ) + 1001 / 2 := h2
      linarith)

/-- **Davis--Kahan 1970, equation (9.2), for the genuine free-beam operator.**  The
double-angle sine between the zero-mode subspace and the perturbed low subspace is
below `2 ε / 500`.  The `sin 2Θ` theorem contributes the factor two and the perturbation
norm; the gap `500.5` comes from `realSpectrum_beamOperator_subset_sharp`, which is why
the strict inequality of the printed bound survives. -/
theorem beamSinTwoTheta_lt (ε : ℝ) (hε : 0 < ε) :
    beamSinTwoTheta ε < 2 * ε / 500 := by
  have hmain := sinTwoTheta_addBounded_of_spectrum_gap beamOperator
    beamOperator_isSelfAdjoint (beamPerturbation ε) (beamPerturbation_isSelfAdjoint ε)
    beamLowSet beamLowSet measurableSet_beamLowSet measurableSet_beamLowSet
    (β := 0) (α := 0) (δ := 1001 / 2) le_rfl (by norm_num)
    beamLow_semiboundedBelow beamLow_semiboundedAbove beamHigh_spectrum_avoids
  have hnorm : ‖beamPerturbation ε‖ ≤ ε := by
    have := norm_beamPerturbation_le ε
    rwa [abs_of_pos hε] at this
  have hchain : (1001 / 2 : ℝ) * beamSinTwoTheta ε ≤ 2 * ε := by
    refine le_trans hmain ?_
    linarith
  nlinarith [beamSinTwoTheta_nonneg ε, hchain]

/-! ## Moments to integrals: the finite layer is about the operator

`Section9/TrialSubspace.lean` builds the Ritz and residual matrices out of three
bilinear forms on `CenteredAffine`, declared there as exact finite data with the note
that "a later integration lemma may identify these forms with actual Lebesgue integrals
on the unit interval".  These are those lemmas. -/

/-- The `L²` inner product of two affine elements. -/
theorem inner_affineLp (a b c d : ℂ) :
    ⟪affineLp a b, affineLp c d⟫_ℂ
      = (starRingEnd ℂ) a * c
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) / 2
        + (starRingEnd ℂ) b * d / 3 := by
  rw [affineLp_eq_contToLp, affineLp_eq_contToLp, inner_contToLp]
  have hpt : ∀ t : ℝ, (starRingEnd ℂ) (a + b * (t : ℂ)) * (c + d * (t : ℂ))
      = (starRingEnd ℂ) a * c
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) * (t : ℂ)
        + ((starRingEnd ℂ) b * d) * (t : ℂ) ^ 2 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quadratic]

/-- The `t`-weighted inner product of two affine elements. -/
theorem inner_affineLp_beamPerturbation (ε : ℝ) (a b c d : ℂ) :
    ⟪affineLp a b, beamPerturbation ε (affineLp c d)⟫_ℂ
      = (ε : ℂ) * ((starRingEnd ℂ) a * c / 2
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) / 3
        + (starRingEnd ℂ) b * d / 4) := by
  rw [affineLp_eq_contToLp, beamPerturbation_affineLp, ← affineLp_eq_contToLp,
    affineLp_eq_contToLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (a + b * (t : ℂ)) * (((ε : ℂ) * (t : ℂ)) * (c + d * (t : ℂ)))
      = 0 + ((ε : ℂ) * ((starRingEnd ℂ) a * c)) * (t : ℂ)
        + ((ε : ℂ) * ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c)) * (t : ℂ) ^ 2
        + ((ε : ℂ) * ((starRingEnd ℂ) b * d)) * (t : ℂ) ^ 3
        + 0 * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- The `t²`-weighted inner product of two affine elements. -/
theorem inner_beamPerturbation_affineLp (ε : ℝ) (a b c d : ℂ) :
    ⟪beamPerturbation ε (affineLp a b), beamPerturbation ε (affineLp c d)⟫_ℂ
      = (ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * c / 3
        + ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c) / 4
        + (starRingEnd ℂ) b * d / 5) := by
  rw [beamPerturbation_affineLp, beamPerturbation_affineLp, inner_contToLp]
  have hpt : ∀ t : ℝ,
      (starRingEnd ℂ) (((ε : ℂ) * (t : ℂ)) * (a + b * (t : ℂ)))
          * (((ε : ℂ) * (t : ℂ)) * (c + d * (t : ℂ)))
      = 0 + 0 * (t : ℂ)
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * c)) * (t : ℂ) ^ 2
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) a * d + (starRingEnd ℂ) b * c)) * (t : ℂ) ^ 3
        + ((ε : ℂ) ^ 2 * ((starRingEnd ℂ) b * d)) * (t : ℂ) ^ 4 := by
    intro t
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  simp only [hpt]
  rw [integral_unitIocMeasure_quartic]
  ring

/-- The `L²` realization of a centered-affine trial function `c + d (2t - 1)`. -/
def centeredAffineLp (p : DavisKahan1970.Section9.CenteredAffine) : BeamL2 :=
  affineLp ((p.constant - p.centered : ℝ) : ℂ) ((2 * p.centered : ℝ) : ℂ)

theorem centeredAffineLp_mem_beamTrial (p : DavisKahan1970.Section9.CenteredAffine) :
    centeredAffineLp p ∈ beamTrial :=
  affineLp_mem_beamTrial _ _

/-- **The affine inner product is the `L²` inner product.** -/
theorem inner_centeredAffineLp (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪centeredAffineLp p, centeredAffineLp q⟫_ℂ
      = ((DavisKahan1970.Section9.CenteredAffine.inner p q : ℝ) : ℂ) := by
  rw [centeredAffineLp, centeredAffineLp, inner_affineLp,
    DavisKahan1970.Section9.CenteredAffine.inner]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- **The `t`-weighted affine form is the `L²` pairing against multiplication by `t`.** -/
theorem inner_centeredAffineLp_mul (ε : ℝ)
    (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪centeredAffineLp p, beamPerturbation ε (centeredAffineLp q)⟫_ℂ
      = ((ε * DavisKahan1970.Section9.CenteredAffine.tInner p q : ℝ) : ℂ) := by
  rw [centeredAffineLp, centeredAffineLp, inner_affineLp_beamPerturbation,
    DavisKahan1970.Section9.CenteredAffine.tInner]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- **The `t²`-weighted affine form is the `L²` norm of the multiplied pair.** -/
theorem inner_mul_centeredAffineLp_mul (ε : ℝ)
    (p q : DavisKahan1970.Section9.CenteredAffine) :
    ⟪beamPerturbation ε (centeredAffineLp p), beamPerturbation ε (centeredAffineLp q)⟫_ℂ
      = ((ε ^ 2 * DavisKahan1970.Section9.CenteredAffine.tSqInner p q : ℝ) : ℂ) := by
  rw [centeredAffineLp, centeredAffineLp, inner_beamPerturbation_affineLp,
    DavisKahan1970.Section9.CenteredAffine.tSqInner]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-! ## The Ritz and residual matrices of the genuine operator -/

open DavisKahan1970.Section9 in
/-- The two trial functions are an orthonormal pair of zero modes. -/
theorem beamTrial_orthonormal :
    ‖centeredAffineLp trialOne‖ ^ 2 = 1 ∧ ‖centeredAffineLp trialTwo‖ ^ 2 = 1 ∧
      ⟪centeredAffineLp trialOne, centeredAffineLp trialTwo⟫_ℂ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := inner_centeredAffineLp trialOne trialOne
    rw [trialOne_norm_sq] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    refine Complex.ofReal_inj.mp ?_
    push_cast
    exact h
  · have h := inner_centeredAffineLp trialTwo trialTwo
    rw [trialTwo_norm_sq] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    refine Complex.ofReal_inj.mp ?_
    push_cast
    exact h
  · rw [inner_centeredAffineLp, trialOne_inner_trialTwo]
    norm_num

open DavisKahan1970.Section9 in
/-- **The Ritz compression of `ε t` to the trial basis is the diagonal matrix of
equation (9.5)** — no longer as a finite-moment reconstruction, but as the genuine
`L²` compression of the genuine perturbation to the genuine kernel. -/
theorem beamRitz_matrix (ε : ℝ) :
    ⟪centeredAffineLp trialOne, beamPerturbation ε (centeredAffineLp trialOne)⟫_ℂ
        = ((ritzLow ε : ℝ) : ℂ) ∧
      ⟪centeredAffineLp trialOne, beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ = 0 ∧
      ⟪centeredAffineLp trialTwo, beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ
        = ((ritzHigh ε : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_centeredAffineLp_mul, trialOne_tInner_trialOne]
    rfl
  · rw [inner_centeredAffineLp_mul, trialOne_tInner_trialTwo]
    norm_num
  · rw [inner_centeredAffineLp_mul, trialTwo_tInner_trialTwo]
    rfl

open DavisKahan1970.Section9 in
/-- **The residual Gram matrix of equation (9.1) is the genuine Gram matrix** of the
residual `ε t` restricted to the trial subspace. -/
theorem beamResidualGram_matrix (ε : ℝ) :
    ⟪beamPerturbation ε (centeredAffineLp trialOne),
        beamPerturbation ε (centeredAffineLp trialOne)⟫_ℂ
        = (((residualGram ε).a₀₀ : ℝ) : ℂ) ∧
      ⟪beamPerturbation ε (centeredAffineLp trialOne),
        beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ
        = (((residualGram ε).a₀₁ : ℝ) : ℂ) ∧
      ⟪beamPerturbation ε (centeredAffineLp trialTwo),
        beamPerturbation ε (centeredAffineLp trialTwo)⟫_ℂ
        = (((residualGram ε).a₁₁ : ℝ) : ℂ) := by
  have hgram := initial_residual_gram_from_affine_moments ε
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_mul_centeredAffineLp_mul]
    congr 1
    exact congrArg SymmetricTwoByTwo.a₀₀ hgram
  · rw [inner_mul_centeredAffineLp_mul]
    congr 1
    exact congrArg SymmetricTwoByTwo.a₀₁ hgram
  · rw [inner_mul_centeredAffineLp_mul]
    congr 1
    exact congrArg SymmetricTwoByTwo.a₁₁ hgram

/-! ## The finite-data certificate, constructed -/

open DavisKahan1970.Section9 in
/-- **The Section 9 finite-data certificate, constructed from the genuine operator.**

Every field is now discharged rather than postulated: the two Gram matrices and the two
Ritz values are the compressions computed in `beamRitz_matrix` and
`beamResidualGram_matrix`, and the third eigenvalue is an actual nonzero point of
`beamOperator.realSpectrum`, whose lower bound `500` is
`realSpectrum_beamOperator_subset_sharp`. -/
def beamFiniteDataCertificate (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {alpha : ℝ} (halpha : alpha ∈ beamOperator.realSpectrum) (halpha0 : alpha ≠ 0) :
    FreeBeamFiniteDataCertificate ε where
  epsilon_pos := hε
  epsilon_lt_hundred := hε100
  third_eigenvalue := alpha
  third_eigenvalue_gt_five_hundred := by
    rcases realSpectrum_beamOperator_subset_sharp halpha with h0 | hgt
    · exact absurd h0 halpha0
    · have : (1001 : ℝ) / 2 < alpha := hgt
      linarith
  initial_residual_gram := residualGram ε
  initial_residual_gram_eq := rfl
  ritz_low := ritzLow ε
  ritz_high := ritzHigh ε
  ritz_low_eq := rfl
  ritz_high_eq := rfl
  recentered_residual_gram := orthogonalResidualGram ε
  recentered_residual_gram_eq := rfl

end

end Model
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
