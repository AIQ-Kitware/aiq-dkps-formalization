/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import DavisKahan.SpectralTheory.FormMethod.BeamFormSpace
import DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamModeUniqueness
import DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamRootLocalization
import Mathlib.Tactic

/-!
# Kernel and eigenfunctions of the free-beam operator

With the operator in hand (`BeamFormSpace`), this file starts its spectral analysis:

* the **variational eigen-identity**: an eigenpair of `beamOperator` pairs the bending slot
  of its form representative against every test pair;
* the **kernel is the affine plane**: `beamOperator u = 0` exactly when `u` is a complex
  combination of `1` and `t`.

The eigenfunction bootstrap and the full spectrum characterization build on these.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Model

noncomputable section

/-! ## Plumbing for the shifted realization -/

/-- The domain of the beam operator is the domain of its shifted realization. -/
theorem beamOperator_domain_eq :
    beamOperator.domain = beamShiftedFormData.shiftedOperator.domain := rfl

/-- The shifted operator acts as the beam operator plus the identity. -/
theorem shifted_apply_of_beam {x : beamOperator.domain} :
    beamShiftedFormData.shiftedOperator.toLinearMap x
      = beamOperator.toLinearMap x + (x : BeamL2) := by
  have h : beamOperator.toLinearMap x
      = beamShiftedFormData.shiftedOperator.toLinearMap x - (x : BeamL2) :=
    beamShiftedFormData.beamOperator_apply x
  rw [h]
  abel

/-- The inner product of the form space decomposes along the two slots. -/
theorem beamV_inner_decompose (p v : BeamV) :
    ⟪p, v⟫_ℂ = ⟪beamEmbed p, beamEmbed v⟫_ℂ + ⟪beamSnd p, beamSnd v⟫_ℂ := by
  have hcoe : ⟪p, v⟫_ℂ = ⟪(p : BeamPairSpace), (v : BeamPairSpace)⟫_ℂ := rfl
  rw [hcoe, WithLp.prod_inner_apply]
  rfl

/-- **The variational eigen-identity.**  If `x` is an eigenvector of the beam operator with
real eigenvalue `lam`, there is a form-space representative `p` with first slot `x` whose
bending slot pairs against every test pair by `lam` times the ambient pairing. -/
theorem exists_form_representative_of_eigen {lam : ℝ} {x : beamOperator.domain}
    (heig : beamOperator.toLinearMap x = (lam : ℂ) • (x : BeamL2)) :
    ∃ p : BeamV, beamEmbed p = (x : BeamL2) ∧
      ∀ v : BeamV, ⟪beamSnd p, beamSnd v⟫_ℂ
        = (lam : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ := by
  set p : BeamV := beamShiftedFormData.formRepresentative x with hpdef
  have hembed : beamEmbed p = (x : BeamL2) := by
    have := beamShiftedFormData.embed_formRepresentative x
    exact this
  refine ⟨p, hembed, ?_⟩
  intro v
  -- the variational identity for the forcing `(shifted) x = (1 + lam) x`
  have hvar := beamCoerciveFormData.variational_identity
    (beamShiftedFormData.shiftedOperator.toLinearMap x) v
  have hform : beamCoerciveFormData.formOperator
      (beamCoerciveFormData.solutionOperator
        (beamShiftedFormData.shiftedOperator.toLinearMap x))
      = p := by
    rw [show beamCoerciveFormData.formOperator = 1 from rfl]
    rfl
  rw [hform] at hvar
  -- identify the forcing
  have hforce : beamShiftedFormData.shiftedOperator.toLinearMap x
      = ((1 + lam : ℝ) : ℂ) • (x : BeamL2) := by
    rw [shifted_apply_of_beam, heig]
    push_cast
    rw [add_smul, one_smul]
    abel
  rw [hforce] at hvar
  -- expand both sides
  have hlhs : ⟪p, v⟫_ℂ = ⟪(x : BeamL2), beamEmbed v⟫_ℂ + ⟪beamSnd p, beamSnd v⟫_ℂ := by
    rw [beamV_inner_decompose, hembed]
  have hrhs : ⟪((1 + lam : ℝ) : ℂ) • (x : BeamL2),
      beamCoerciveFormData.embed v⟫_ℂ
      = ((1 + lam : ℝ) : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ := by
    rw [inner_smul_left]
    rw [show beamCoerciveFormData.embed = beamEmbed from rfl]
    congr 1
    rw [Complex.conj_ofReal]
  rw [hlhs, hrhs] at hvar
  have : ⟪beamSnd p, beamSnd v⟫_ℂ
      = ((1 + lam : ℝ) : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ
        - ⟪(x : BeamL2), beamEmbed v⟫_ℂ := by
    linear_combination hvar
  rw [this]
  push_cast
  ring

/-! ## The affine kernel -/

/-- Both bump moments against the ambient measure vanish. -/
theorem integral_bumpD2C_eq_zero (k : ℕ) :
    ∫ t, bumpD2C k t ∂unitIocMeasure = 0 := by
  have : ∫ t, bumpD2C k t ∂unitIocMeasure
      = ((∫ t, intervalBumpD2 k t ∂unitIocMeasure : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    rfl
  rw [this, integral_unitIocMeasure_eq_intervalIntegral, integral_intervalBumpD2]
  norm_num

/-- The first moment of the second bump derivative vanishes as well. -/
theorem integral_id_mul_bumpD2C_eq_zero (k : ℕ) :
    ∫ t, ((t : ℝ) : ℂ) * bumpD2C k t ∂unitIocMeasure = 0 := by
  have hpt : ∀ t : ℝ, ((t : ℝ) : ℂ) * bumpD2C k t
      = ((t * intervalBumpD2 k t : ℝ) : ℂ) := by
    intro t
    rw [bumpD2C]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal,
    integral_unitIocMeasure_eq_intervalIntegral, integral_id_mul_intervalBumpD2]
  norm_num

/-- The affine pair `(a·1 + b·t, 0)` lies in the form subspace. -/
theorem affinePair_mem (a b : ℂ) :
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
        (a • beamOneLp + b • beamIdLp, 0)) ∈ beamFormSubmodule := by
  rw [mem_beamFormSubmodule_iff]
  intro k
  have hfst : pairFst ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) = a • beamOneLp + b • beamIdLp := by
    rw [pairFst_apply]
    simp
  have hsnd : pairSnd ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
      (a • beamOneLp + b • beamIdLp, 0)) = 0 := by
    rw [pairSnd_apply]
    simp
  rw [hfst, hsnd]
  have hrhs : ∫ t, ((0 : BeamL2) : ℝ → ℂ) t * bumpC k t ∂unitIocMeasure = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [Lp.coeFn_zero ℂ 2 unitIocMeasure] with t ht
      rw [ht]
      simp
  rw [hrhs]
  have hlhs : ∫ t, ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℂ) t * bumpD2C k t
      ∂unitIocMeasure
      = a * (∫ t, bumpD2C k t ∂unitIocMeasure)
        + b * ∫ t, ((t : ℝ) : ℂ) * bumpD2C k t ∂unitIocMeasure := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← integral_add (((integrable_unitIocMeasure_of_continuous
          (continuous_bumpD2C k)).const_mul a))
        ((integrable_mul_of_continuous (integrable_unitIocMeasure_of_continuous
          (by fun_prop)) (continuous_bumpD2C k)).const_mul b)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
      Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
      coeFn_beamIdLp] with t hadd hsa hsb h1 hT
    rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, h1, hT,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hlhs, integral_bumpD2C_eq_zero, integral_id_mul_bumpD2C_eq_zero]
  ring

/-- The affine element of the ambient space attached to a coefficient pair. -/
def affineLp (a b : ℂ) : BeamL2 := a • beamOneLp + b • beamIdLp

/-- The form representative of an affine element. -/
def affineV (a b : ℂ) : BeamV :=
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm (affineLp a b, 0),
    affinePair_mem a b⟩

@[simp] theorem beamEmbed_affineV (a b : ℂ) : beamEmbed (affineV a b) = affineLp a b := by
  rw [show beamEmbed (affineV a b) = pairFst ((affineV a b : BeamV) : BeamPairSpace)
    from rfl]
  rw [show ((affineV a b : BeamV) : BeamPairSpace)
    = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm (affineLp a b, 0)
    from rfl]
  rw [pairFst_apply]
  simp

@[simp] theorem beamSnd_affineV (a b : ℂ) : beamSnd (affineV a b) = 0 := by
  rw [show beamSnd (affineV a b) = pairSnd ((affineV a b : BeamV) : BeamPairSpace)
    from rfl]
  rw [show ((affineV a b : BeamV) : BeamPairSpace)
    = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm (affineLp a b, 0)
    from rfl]
  rw [pairSnd_apply]
  simp

/-- The adjoint of the embedding sends an affine element to its form representative. -/
theorem adjoint_beamEmbed_affine (a b : ℂ) :
    ContinuousLinearMap.adjoint beamEmbed (affineLp a b) = affineV a b := by
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, beamV_inner_decompose,
    beamEmbed_affineV, beamSnd_affineV, inner_zero_left, add_zero]

/-- Affine elements lie in the beam operator's domain and are annihilated by it. -/
theorem beamOperator_affine_mem_and_zero (a b : ℂ) :
    ∃ h : affineLp a b ∈ beamOperator.domain,
      beamOperator.toLinearMap ⟨affineLp a b, h⟩ = 0 := by
  -- the resolvent fixes affine elements
  have hres : beamCoerciveFormData.resolvent (affineLp a b) = affineLp a b := by
    rw [show beamCoerciveFormData.resolvent
        = beamCoerciveFormData.embed ∘L beamCoerciveFormData.solutionOperator from rfl]
    have hsol : beamCoerciveFormData.solutionOperator (affineLp a b) = affineV a b := by
      rw [show beamCoerciveFormData.solutionOperator
          = beamCoerciveFormData.formInverse ∘L
            (ContinuousLinearMap.adjoint beamCoerciveFormData.embed) from rfl]
      have hinv : beamCoerciveFormData.formInverse = 1 := by
        rw [show beamCoerciveFormData.formInverse
            = Ring.inverse beamCoerciveFormData.formOperator from rfl]
        rw [show beamCoerciveFormData.formOperator = 1 from rfl]
        exact Ring.inverse_one _
      rw [ContinuousLinearMap.comp_apply, hinv]
      rw [show (ContinuousLinearMap.adjoint beamCoerciveFormData.embed)
          (affineLp a b) = affineV a b from adjoint_beamEmbed_affine a b]
      rfl
    rw [ContinuousLinearMap.comp_apply, hsol]
    exact beamEmbed_affineV a b
  have hmem : affineLp a b ∈ beamOperator.domain := by
    rw [show beamOperator.domain
        = LinearMap.range (beamCoerciveFormData.resolvent :
            BeamL2 →ₗ[ℂ] BeamL2) from rfl]
    exact ⟨affineLp a b, hres⟩
  refine ⟨hmem, ?_⟩
  -- the shifted operator fixes affine elements, so the beam operator kills them
  have hshift : beamShiftedFormData.shiftedOperator.toLinearMap ⟨affineLp a b, hmem⟩
      = affineLp a b := by
    have := Abstract.inverseClosedOperator_apply_R beamCoerciveFormData.resolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective (affineLp a b)
    have hsub : (⟨beamCoerciveFormData.resolvent (affineLp a b),
        LinearMap.mem_range_self _ (affineLp a b)⟩ :
          beamShiftedFormData.shiftedOperator.domain)
        = ⟨affineLp a b, hmem⟩ := Subtype.ext hres
    rw [← hsub]
    exact this
  have happly : beamOperator.toLinearMap ⟨affineLp a b, hmem⟩
      = beamShiftedFormData.shiftedOperator.toLinearMap ⟨affineLp a b, hmem⟩
        - affineLp a b :=
    beamShiftedFormData.beamOperator_apply _
  rw [happly, hshift, sub_self]

/-- Conversely, an element of the kernel is affine. -/
theorem exists_affine_of_beamOperator_eq_zero {x : beamOperator.domain}
    (hx : beamOperator.toLinearMap x = 0) :
    ∃ a b : ℂ, (x : BeamL2) = affineLp a b := by
  -- the quadratic form vanishes, hence so does the bending slot
  have hquad : RCLike.re ⟪beamOperator.toLinearMap x, (x : BeamL2)⟫_ℂ
      = beamShiftedFormData.bendingEnergy (beamShiftedFormData.formRepresentative x) :=
    beamShiftedFormData.beam_quadratic_eq_bendingEnergy x
  rw [hx, inner_zero_left] at hquad
  have hbend0 : beamShiftedFormData.bendingEnergy
      (beamShiftedFormData.formRepresentative x) = 0 := by
    rw [← hquad]
    simp
  have hbend : ‖beamSnd (beamShiftedFormData.formRepresentative x)‖ ^ 2 = 0 := hbend0
  have hsnd0 : beamSnd (beamShiftedFormData.formRepresentative x) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hbend
    exact norm_eq_zero.mp this
  -- the representation theorem with vanishing density
  obtain ⟨a, b, hab⟩ := beamV_repr (beamShiftedFormData.formRepresentative x)
  have hembed := beamShiftedFormData.embed_formRepresentative x
  refine ⟨a, b, ?_⟩
  have hK0 : secondPrimitive ((beamSnd (beamShiftedFormData.formRepresentative x)
      : ℝ → ℂ)) = secondPrimitive (fun _ => 0) := by
    apply secondPrimitive_congr_ae
    rw [hsnd0]
    exact Lp.coeFn_zero ℂ 2 unitIocMeasure
  have hKzero : ∀ t : ℝ, secondPrimitive (fun _ : ℝ => (0 : ℂ)) t = 0 := by
    intro t
    rw [secondPrimitive_def]
    simp
  refine Lp.ext ?_
  have hxcoe : ((x : BeamL2) : ℝ → ℂ)
      =ᵐ[unitIocMeasure] (beamEmbed (beamShiftedFormData.formRepresentative x)
        : ℝ → ℂ) := by
    rw [show beamEmbed (beamShiftedFormData.formRepresentative x) = (x : BeamL2)
      from hembed]
  filter_upwards [hxcoe, hab, Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
    coeFn_beamIdLp] with t hx1 hx2 hadd hsa hsb h1 hT
  rw [hx1, hx2, hK0, hKzero, add_zero]
  rw [show (affineLp a b : ℝ → ℂ) t = ((a • beamOneLp + b • beamIdLp : BeamL2) : ℝ → ℂ) t
    from rfl]
  rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, h1, hT,
    smul_eq_mul, smul_eq_mul]
  ring

/-! ## The eigen-pairing against smooth test functions -/

/-- Test the variational eigen-identity against the pair of a real `C²` function and its
second derivative, and conjugate away: the bending slot integrates against `f''` as `lam`
times the eigenvector against `f`. -/
theorem eigen_pairing_integral {lam : ℝ} {x : beamOperator.domain} {p : BeamV}
    (hpair : ∀ v : BeamV, ⟪beamSnd p, beamSnd v⟫_ℂ
      = (lam : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ)
    {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ t, HasDerivAt f (f1 t) t) (hd1 : ∀ t, HasDerivAt f1 (f2 t) t) :
    ∫ t, (beamSnd p : ℝ → ℂ) t * (f2 t : ℂ) ∂unitIocMeasure
      = (lam : ℂ) * ∫ t, ((x : BeamL2) : ℝ → ℂ) t * (f t : ℂ) ∂unitIocMeasure := by
  set v : BeamV := ⟨(WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
    (contToLp (fun t => (f t : ℂ)) (by fun_prop),
      contToLp (fun t => (f2 t : ℂ)) (by fun_prop)),
    contPair_mem hf hf1 hf2 hd hd1⟩ with hvdef
  have hvfst : beamEmbed v = contToLp (fun t => (f t : ℂ)) (by fun_prop) := by
    rw [show beamEmbed v = pairFst ((v : BeamV) : BeamPairSpace) from rfl, hvdef,
      pairFst_apply]
    simp
  have hvsnd : beamSnd v = contToLp (fun t => (f2 t : ℂ)) (by fun_prop) := by
    rw [show beamSnd v = pairSnd ((v : BeamV) : BeamPairSpace) from rfl, hvdef,
      pairSnd_apply]
    simp
  have hid := hpair v
  rw [hvfst, hvsnd] at hid
  -- expand the two inner products as integrals
  have hL : ⟪beamSnd p, contToLp (fun t => (f2 t : ℂ)) (by fun_prop)⟫_ℂ
      = ∫ t, (starRingEnd ℂ) ((beamSnd p : ℝ → ℂ) t) * (f2 t : ℂ) ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp (fun t => (f2 t : ℂ)) (by fun_prop)] with t ht
    rw [RCLike.inner_apply, ht]
    ring
  have hR : ⟪(x : BeamL2), contToLp (fun t => (f t : ℂ)) (by fun_prop)⟫_ℂ
      = ∫ t, (starRingEnd ℂ) (((x : BeamL2) : ℝ → ℂ) t) * (f t : ℂ) ∂unitIocMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp (fun t => (f t : ℂ)) (by fun_prop)] with t ht
    rw [RCLike.inner_apply, ht]
    ring
  rw [hL, hR] at hid
  -- conjugate the identity
  have hconj := congrArg (starRingEnd ℂ) hid
  rw [map_mul, Complex.conj_ofReal, ← integral_conj, ← integral_conj] at hconj
  have h1 : (fun t => (starRingEnd ℂ)
        ((starRingEnd ℂ) ((beamSnd p : ℝ → ℂ) t) * (f2 t : ℂ)))
      = fun t => (beamSnd p : ℝ → ℂ) t * (f2 t : ℂ) := by
    funext t
    rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  have h2 : (fun t => (starRingEnd ℂ)
        ((starRingEnd ℂ) (((x : BeamL2) : ℝ → ℂ) t) * (f t : ℂ)))
      = fun t => ((x : BeamL2) : ℝ → ℂ) t * (f t : ℂ) := by
    funext t
    rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [h1, h2] at hconj
  exact hconj

/-! ## Cubic test functions -/

/-- Cubic polynomial test function. -/
def cubic (c0 c1 c2 c3 t : ℝ) : ℝ := c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3

/-- First derivative of the cubic. -/
def cubicD1 (_c0 c1 c2 c3 t : ℝ) : ℝ := c1 + 2 * c2 * t + 3 * c3 * t ^ 2

/-- Second derivative of the cubic. -/
def cubicD2 (_c0 _c1 c2 c3 t : ℝ) : ℝ := 2 * c2 + 6 * c3 * t

theorem continuous_cubic (c0 c1 c2 c3 : ℝ) : Continuous (cubic c0 c1 c2 c3) := by
  unfold cubic
  fun_prop

theorem continuous_cubicD1 (c0 c1 c2 c3 : ℝ) : Continuous (cubicD1 c0 c1 c2 c3) := by
  unfold cubicD1
  fun_prop

theorem continuous_cubicD2 (c0 c1 c2 c3 : ℝ) : Continuous (cubicD2 c0 c1 c2 c3) := by
  unfold cubicD2
  fun_prop

theorem hasDerivAt_cubic (c0 c1 c2 c3 t : ℝ) :
    HasDerivAt (cubic c0 c1 c2 c3) (cubicD1 c0 c1 c2 c3 t) t := by
  have h := (((hasDerivAt_const t c0).add ((hasDerivAt_id t).const_mul c1)).add
    (((hasDerivAt_pow 2 t)).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)
  refine h.congr_deriv ?_
  unfold cubicD1
  push_cast
  ring

theorem hasDerivAt_cubicD1 (c0 c1 c2 c3 t : ℝ) :
    HasDerivAt (cubicD1 c0 c1 c2 c3) (cubicD2 c0 c1 c2 c3 t) t := by
  have h := ((hasDerivAt_const t c1).add
    (((hasDerivAt_id t).const_mul (2 * c2)))).add
    (((hasDerivAt_pow 2 t)).const_mul (3 * c3))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold cubicD2
    push_cast
    ring
  · refine Filter.Eventually.of_forall fun s => ?_
    unfold cubicD1
    simp only [Pi.add_apply, id_eq]

/-! ## The boundary form of an eigenfunction vanishes -/

/-- The classical boundary form of an eigenfunction's continuous representatives against any
cubic test function vanishes: two integrations by parts against the distributional
eigen-identity. -/
theorem boundary_form_eq_zero {lam : ℝ} {x : beamOperator.domain} {p : BeamV}
    (hpair : ∀ v : BeamV, ⟪beamSnd p, beamSnd v⟫_ℂ
      = (lam : ℂ) * ⟪(x : BeamL2), beamEmbed v⟫_ℂ)
    {ubar wbar u3 : ℝ → ℂ}
    (hxu : ((x : BeamL2) : ℝ → ℂ) =ᵐ[unitIocMeasure] ubar)
    (hwu : (beamSnd p : ℝ → ℂ) =ᵐ[unitIocMeasure] wbar)
    (hucont : Continuous ubar) (hwcont : Continuous wbar)
    (hw' : ∀ t, HasDerivAt wbar (u3 t) t)
    (hu3cont : ContinuousOn u3 (Set.Icc 0 1))
    (hu3' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt u3 ((lam : ℂ) * ubar t) (Set.Icc 0 1) t)
    (q q1 q2 : ℝ → ℝ)
    (hq : Continuous q) (hq1 : Continuous q1) (hq2 : Continuous q2)
    (hdq : ∀ t, HasDerivAt q (q1 t) t) (hdq1 : ∀ t, HasDerivAt q1 (q2 t) t) :
    wbar 1 * (q1 1 : ℂ) - wbar 0 * (q1 0 : ℂ)
      - (u3 1 * (q 1 : ℂ) - u3 0 * (q 0 : ℂ)) = 0 := by
  have hbridgeC : ∀ f : ℝ → ℂ, ∫ t, f t ∂unitIocMeasure = ∫ t in (0 : ℝ)..1, f t := by
    intro f
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure_def]
  -- the distributional identity for the continuous representatives
  have hInt := eigen_pairing_integral hpair hq hq1 hq2 hdq hdq1
  have hIntBar : ∫ t in (0 : ℝ)..1, wbar t * (q2 t : ℂ)
      = (lam : ℂ) * ∫ t in (0 : ℝ)..1, ubar t * (q t : ℂ) := by
    rw [← hbridgeC, ← hbridgeC]
    rw [show ∫ t, wbar t * (q2 t : ℂ) ∂unitIocMeasure
        = ∫ t, (beamSnd p : ℝ → ℂ) t * (q2 t : ℂ) ∂unitIocMeasure from
      integral_congr_ae (by
        filter_upwards [hwu] with t ht
        rw [ht])]
    rw [show ∫ t, ubar t * (q t : ℂ) ∂unitIocMeasure
        = ∫ t, ((x : BeamL2) : ℝ → ℂ) t * (q t : ℂ) ∂unitIocMeasure from
      integral_congr_ae (by
        filter_upwards [hxu] with t ht
        rw [ht])]
    exact hInt
  -- first integration by parts: differentiate the cubic side down
  have hIBP1 : ∫ t in (0 : ℝ)..1, wbar t * (q2 t : ℂ)
      = wbar 1 * (q1 1 : ℂ) - wbar 0 * (q1 0 : ℂ)
        - ∫ t in (0 : ℝ)..1, u3 t * (q1 t : ℂ) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hwcont.continuousOn (by fun_prop : Continuous fun t : ℝ => (q1 t : ℂ)).continuousOn
      (fun t _ => hw' t) (fun t _ => (hdq1 t).ofReal_comp)
      ?_ ((by fun_prop : Continuous fun t : ℝ => (q2 t : ℂ)).intervalIntegrable 0 1)
    have : ContinuousOn u3 (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hu3cont
    exact this.intervalIntegrable
  -- second integration by parts: interior two-sided derivatives of the third slot
  have hIBP2 : ∫ t in (0 : ℝ)..1, u3 t * (q1 t : ℂ)
      = u3 1 * (q 1 : ℂ) - u3 0 * (q 0 : ℂ)
        - ∫ t in (0 : ℝ)..1, ((lam : ℂ) * ubar t) * (q t : ℂ) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      ?_ (by fun_prop : Continuous fun t : ℝ => (q t : ℂ)).continuousOn
      ?_ (fun t _ => (hdq t).ofReal_comp)
      ((hucont.const_smul ((lam : ℂ))).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ => (q1 t : ℂ)).intervalIntegrable 0 1)
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hu3cont
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
      exact (hu3' t (Set.Ioo_subset_Icc_self ht')).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)
  -- combine
  have hlin : ∫ t in (0 : ℝ)..1, ((lam : ℂ) * ubar t) * (q t : ℂ)
      = (lam : ℂ) * ∫ t in (0 : ℝ)..1, ubar t * (q t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with t
    ring
  rw [hIBP2, hlin] at hIBP1
  rw [hIntBar] at hIBP1
  linear_combination -hIBP1

end

end Model
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti
