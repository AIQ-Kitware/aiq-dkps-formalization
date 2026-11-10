/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
Adapted in part from Spectra/OneParameterUnitaryGroup/Basic.lean at
  8dbaaf6728d1342ae16acf79fd7eef7c59b37e63, copyright (c) 2026
  Spectra Formalization Project, author Adam Bornemann, Apache 2.0.
-/
module

public import TauCeti.Analysis.Semigroups.Group.Unitary

/-!
# Complex operators of a native unitary group

The native group stores real continuous linear maps. Inner-product preservation
supplies complex linearity, so the same operator can be used in complex operator
composition and adjoint identities. The normalized difference quotient below
connects two-sided orbit derivatives to the native Stone generator; it creates
no second generator or generator domain.

The adjoint identity adapts the inverse/unitarity argument from the former
DKPS `OneParameterUnitaryGroup/Basic.lean` (Kitware, Jon Crall and Claude Opus 5,
Apache 2.0), itself adapted from Spectra at the commit credited above. The
remaining proofs reduce to native Tau Ceti group and generator APIs. No
separability or nonzero-space hypothesis is used; the quotient is zero at time
zero. This bridge supports the Yosida limit and Hilbert–Schmidt Sylvester flow
without defining an alternative group carrier or generator.
-/

public section

noncomputable section

open Complex Filter Topology
open scoped InnerProductSpace

namespace TauCeti.Semigroups.StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : TauCeti.Semigroups.StronglyContinuousGroup H) (hU : U.IsUnitary)

/-- The complex-linear operator underlying a native unitary group element. -/
@[expose]
def complexOperator (t : ℝ) : H →L[ℂ] H where
  toFun := U t
  map_add' := (U t).map_add
  map_smul' := hU.map_smul t
  cont := (U t).continuous

@[simp]
theorem complexOperator_apply (t : ℝ) (x : H) : U.complexOperator hU t x = U t x := rfl

@[simp]
theorem complexOperator_zero : U.complexOperator hU 0 = ContinuousLinearMap.id ℂ H := by
  ext x
  exact U.map_zero_apply x

/-- Composition law in the complex continuous-linear-map representation. -/
theorem complexOperator_add (s t : ℝ) :
    U.complexOperator hU (s + t) = (U.complexOperator hU s).comp (U.complexOperator hU t) := by
  ext x
  exact U.map_add_apply s t x

variable [CompleteSpace H]

/-- Time reversal is the complex adjoint. -/
theorem complexOperator_neg_eq_adjoint (t : ℝ) :
    U.complexOperator hU (-t) = (U.complexOperator hU t).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [complexOperator_apply]
  rw [← hU.inner_map_map t (U (-t) x) y, U.map_apply_map_neg_apply]

omit [CompleteSpace H] in
/-- Difference quotient in the self-adjoint Stone normalization. -/
def stoneDiffQuot (x : H) (t : ℝ) : H :=
  (-I) • ((1 / t) • (U t x - x))

omit [CompleteSpace H] in
/-- The Stone quotient is division by `i t`, including at time zero. -/
@[simp]
theorem stoneDiffQuot_apply (x : H) (t : ℝ) :
    U.stoneDiffQuot x t = (I * (t : ℂ))⁻¹ • (U t x - x) := by
  rw [stoneDiffQuot, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  simp [one_div, mul_inv_rev, mul_comm]

/-- The normalized two-sided difference quotient converges to the native Stone generator.
The native orbit derivative supplies the real quotient; scalar multiplication
by `-i` supplies precisely the self-adjoint normalization. -/
theorem tendsto_stoneDiffQuot (x : (U.stoneGenerator hU).domain) :
    Tendsto (U.stoneDiffQuot (x : H)) (𝓝[≠] (0 : ℝ)) (𝓝 (U.stoneGenerator hU x)) := by
  have hx : (x : H) ∈ U.domain := by
    simpa only [U.stoneGenerator_domain hU, U.mem_complexDomain_iff hU] using x.property
  have h := U.hasDerivAt_zero ⟨(x : H), hx⟩
  rw [hasDerivAt_iff_tendsto_slope] at h
  have hq := h.const_smul (-I)
  simp only [slope_def_module, sub_zero, U.map_zero_apply] at hq
  have hgen : U.stoneGenerator hU x = (-I) • U.generator
      ⟨(x : H), by rw [U.generator_domain]; exact hx⟩ := by
    rw [U.stoneGenerator_apply, U.complexGenerator_apply]
  rw [hgen]
  unfold stoneDiffQuot
  simpa only [one_div] using hq

omit [CompleteSpace H] in
/-- A convergent Stone quotient puts the vector in the native generator domain. -/
theorem mem_stoneGenerator_domain_of_tendsto {x y : H}
    (h : Tendsto (U.stoneDiffQuot x) (𝓝[≠] (0 : ℝ)) (𝓝 y)) :
    x ∈ (U.stoneGenerator hU).domain := by
  have hq := h.const_smul I
  simp only [stoneDiffQuot, smul_smul, mul_neg, I_mul_I, neg_neg, one_smul] at hq
  have hx : x ∈ U.domain := (U.mem_domain_iff_tendsto x).mpr
    ⟨I • y, hq.mono_left (nhdsWithin_mono 0 fun t ht => ne_of_gt ht)⟩
  simpa only [U.stoneGenerator_domain hU, U.mem_complexDomain_iff hU] using hx

omit [CompleteSpace H] in
/-- A complex bounded commutant intertwines the Stone normalization of the native generator. -/
theorem stoneGenerator_commute (T : H →L[ℂ] H)
    (hT : ∀ (t : ℝ) (y : H), T (U t y) = U t (T y))
    (x : (U.stoneGenerator hU).domain) :
    ∃ hmem : T (x : H) ∈ (U.stoneGenerator hU).domain,
      U.stoneGenerator hU ⟨T (x : H), hmem⟩ = T (U.stoneGenerator hU x) := by
  have hx : (x : H) ∈ (U.complexGenerator hU).domain := by
    simpa only [U.complexGenerator_domain hU, U.stoneGenerator_domain hU] using x.property
  obtain ⟨hmem, hcomm⟩ := hU.complexGenerator_commute T (fun t y => (hT t y).symm) ⟨x, hx⟩
  have hm : T (x : H) ∈ (U.stoneGenerator hU).domain := by
    simpa only [U.complexGenerator_domain hU, U.stoneGenerator_domain hU] using hmem
  refine ⟨hm, ?_⟩
  rw [U.stoneGenerator_apply, U.stoneGenerator_apply, map_smul]
  exact congrArg ((-I) • ·) hcomm

end TauCeti.Semigroups.StronglyContinuousGroup
