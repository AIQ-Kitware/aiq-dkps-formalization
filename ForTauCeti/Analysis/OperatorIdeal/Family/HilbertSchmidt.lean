/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidtEnergy
import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# The Hilbert--Schmidt operator ideal

The **Hilbert--Schmidt norm** of a bounded operator between Hilbert spaces is the square
root of its Hilbert--Schmidt energy,

```
‖T‖_HS = (∑' i, ‖T (b i)‖ₑ ^ 2) ^ (1/2),
```

which by `ContinuousLinearMap.hilbertSchmidtEnergy_indep` does not depend on the Hilbert
basis `b`.  Like the energy it takes values in `ℝ≥0∞` and is therefore defined for every
bounded operator, being `∞` exactly off the ideal.

The point of the file is the final construction: these operators form a
`TauCeti.SymmetricOperatorIdealFamily`, the second concrete instance of that structure
after the Ky Fan families.  Two instances built from genuinely different mathematics is
what makes the structure worth having, and the Hilbert--Schmidt one is the instance the
literature reaches for first.

## Main definitions and results

* `ContinuousLinearMap.hilbertSchmidtENorm`: the Hilbert--Schmidt norm, valued in `ℝ≥0∞`;
* `ContinuousLinearMap.hilbertSchmidtENorm_add_le`: the triangle inequality, which is
  Minkowski's inequality at `p = 2`;
* `ContinuousLinearMap.enorm_le_hilbertSchmidtENorm`: it dominates the operator norm;
* `ContinuousLinearMap.hilbertSchmidtENorm_comp_le`: the two-sided ideal bound;
* `ContinuousLinearMap.hilbertSchmidtENorm_adjoint`: it is adjoint-invariant;
* `TauCeti.hilbertSchmidtIdealFamily`: the resulting symmetric operator ideal family.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.  `vendor/Spectra` models Hilbert--Schmidt operators as a Hilbert
  tensor product and does not build an operator ideal from them.
-/

open scoped ENNReal NNReal InnerProductSpace

public section

namespace ENNReal

variable {ι : Type*}

/-- **Minkowski's inequality in `ℓᵖ` for `tsum`, over `ℝ≥0∞`.**  Mathlib's
`ENNReal.Lp_add_le` is stated for a `Finset`, and its `tsum` counterpart exists only over
`ℝ≥0` (`NNReal.Lp_add_le_tsum`), where it carries summability hypotheses on both summands.
This is the `ℝ≥0∞` version, which needs no summability hypothesis at all — that is exactly
why the operator-ideal gauges are `ℝ≥0∞`-valued, since it lets their laws hold
unconditionally at non-members.

The proof is the standard supremum argument: the finite inequality bounds every partial sum
of the left side by the `p`-th power of the right side, and `∑'` is the supremum of its
partial sums. -/
theorem tsum_rpow_add_le {p : ℝ} (hp : 1 ≤ p) (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ p) ^ p⁻¹ ≤
      (∑' i, f i ^ p) ^ p⁻¹ + (∑' i, g i ^ p) ^ p⁻¹ := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set A := (∑' i, f i ^ p) ^ p⁻¹ with hA
  set B := (∑' i, g i ^ p) ^ p⁻¹ with hB
  have hpow : ∀ x : ℝ≥0∞, (x ^ p⁻¹) ^ p = x := fun x => by
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have key : ∀ s : Finset ι, ∑ i ∈ s, (f i + g i) ^ p ≤ (A + B) ^ p := by
    intro s
    have hfin := ENNReal.Lp_add_le (s := s) (f := f) (g := g) (p := p) hp
    rw [one_div] at hfin
    have hfA : (∑ i ∈ s, f i ^ p) ^ p⁻¹ ≤ A :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    have hgB : (∑ i ∈ s, g i ^ p) ^ p⁻¹ ≤ B :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    calc ∑ i ∈ s, (f i + g i) ^ p
        = ((∑ i ∈ s, (f i + g i) ^ p) ^ p⁻¹) ^ p := (hpow _).symm
      _ ≤ (A + B) ^ p :=
          ENNReal.rpow_le_rpow (hfin.trans (add_le_add hfA hgB)) hp0.le
  have hsum : ∑' i, (f i + g i) ^ p ≤ (A + B) ^ p :=
    ENNReal.tsum_eq_iSup_sum.trans_le (iSup_le key)
  calc (∑' i, (f i + g i) ^ p) ^ p⁻¹
      ≤ ((A + B) ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = A + B := by rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- **Minkowski's inequality at `p = 2` for `tsum`**, the instance the Hilbert--Schmidt
energy uses.  Stated separately because its consumers carry the `^ 2` in `ℕ`-power form. -/
theorem tsum_sq_add_rpow_le (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ 2) ^ (2 : ℝ)⁻¹ ≤
      (∑' i, f i ^ 2) ^ (2 : ℝ)⁻¹ + (∑' i, g i ^ 2) ^ (2 : ℝ)⁻¹ := by
  simpa only [← ENNReal.rpow_two] using tsum_rpow_add_le (p := 2) one_le_two f g

end ENNReal

namespace TauCeti

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The index set of `TauCeti.chosenHilbertBasis`: a choice of Hilbert basis of `E`, used to
give the Hilbert--Schmidt norm a definition that mentions no basis.  Nothing depends on
*which* basis this is — every statement about it is proved from
`ContinuousLinearMap.hilbertSchmidtEnergy_indep`. -/
noncomputable def chosenHilbertBasisSet (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : Set E :=
  Classical.choose (exists_hilbertBasis 𝕜 E)

/-- A choice of Hilbert basis of `E`, indexed by `TauCeti.chosenHilbertBasisSet`. -/
noncomputable def chosenHilbertBasis (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    HilbertBasis (chosenHilbertBasisSet 𝕜 E) 𝕜 E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 E))

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type*}

/-- The **Hilbert--Schmidt norm** of `T`, valued in `ℝ≥0∞` and therefore defined for every
bounded operator: it is `∞` exactly when `T` is not Hilbert--Schmidt. -/
noncomputable def hilbertSchmidtENorm (T : E →L[𝕜] F) : ℝ≥0∞ :=
  (T.hilbertSchmidtEnergy (TauCeti.chosenHilbertBasis 𝕜 E)) ^ (2 : ℝ)⁻¹

/-- The Hilbert--Schmidt norm computed in *any* Hilbert basis. -/
theorem hilbertSchmidtENorm_eq (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtENorm = (T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹ := by
  rw [hilbertSchmidtENorm, T.hilbertSchmidtEnergy_indep _ b]

/-- Squaring the Hilbert--Schmidt norm returns the energy. -/
theorem hilbertSchmidtENorm_rpow_two (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtENorm ^ (2 : ℝ) = T.hilbertSchmidtEnergy b := by
  rw [T.hilbertSchmidtENorm_eq b, ← ENNReal.rpow_mul]
  norm_num

/-- Squaring the Hilbert--Schmidt norm returns the energy, natural-power form. -/
theorem hilbertSchmidtENorm_sq (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtENorm ^ 2 = T.hilbertSchmidtEnergy b := by
  rw [← ENNReal.rpow_two, T.hilbertSchmidtENorm_rpow_two b]

omit [CompleteSpace F] in
/-- The zero operator has zero Hilbert--Schmidt norm. -/
@[simp] theorem hilbertSchmidtENorm_zero : (0 : E →L[𝕜] F).hilbertSchmidtENorm = 0 := by
  rw [hilbertSchmidtENorm, hilbertSchmidtEnergy_zero]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

omit [CompleteSpace F] in
/-- The Hilbert--Schmidt norm is unchanged by negation. -/
@[simp] theorem hilbertSchmidtENorm_neg (T : E →L[𝕜] F) :
    (-T).hilbertSchmidtENorm = T.hilbertSchmidtENorm := by
  rw [hilbertSchmidtENorm, hilbertSchmidtENorm, hilbertSchmidtEnergy_neg]

omit [CompleteSpace F] in
/-- The Hilbert--Schmidt norm is absolutely homogeneous, in `ℝ≥0∞`. -/
theorem hilbertSchmidtENorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).hilbertSchmidtENorm = ‖c‖ₑ * T.hilbertSchmidtENorm := by
  rw [hilbertSchmidtENorm, hilbertSchmidtENorm, hilbertSchmidtEnergy_smul,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast ‖c‖ₑ 2,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The triangle inequality**, which is Minkowski's inequality at `p = 2`. -/
theorem hilbertSchmidtENorm_add_le (S T : E →L[𝕜] F) :
    (S + T).hilbertSchmidtENorm ≤ S.hilbertSchmidtENorm + T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [(S + T).hilbertSchmidtENorm_eq b, S.hilbertSchmidtENorm_eq b, T.hilbertSchmidtENorm_eq b]
  refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) <|
    ENNReal.tsum_sq_add_rpow_le (fun i => ‖S (b i)‖ₑ) (fun i => ‖T (b i)‖ₑ)
  refine ENNReal.tsum_le_tsum fun i => ?_
  gcongr
  exact enorm_add_le _ _

/-- **The Hilbert--Schmidt norm dominates the operator norm.** -/
theorem enorm_le_hilbertSchmidtENorm (T : E →L[𝕜] F) : ‖T‖ₑ ≤ T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  refine opENorm_le_bound _ fun x => ?_
  have hbase : ‖T x‖ₑ ^ (2 : ℝ) ≤ (T.hilbertSchmidtENorm * ‖x‖ₑ) ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), T.hilbertSchmidtENorm_rpow_two b,
      ENNReal.rpow_two, ENNReal.rpow_two]
    exact T.enorm_apply_sq_le_hilbertSchmidtEnergy_mul b x
  have h2 := ENNReal.rpow_le_rpow hbase (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one, ENNReal.rpow_one] at h2

/-- **Adjoint invariance.** -/
theorem hilbertSchmidtENorm_adjoint (T : E →L[𝕜] F) :
    T.adjoint.hilbertSchmidtENorm = T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨v, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [T.adjoint.hilbertSchmidtENorm_eq c, T.hilbertSchmidtENorm_eq b,
    ← T.hilbertSchmidtEnergy_adjoint b c]

/-- Postcomposition contracts the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtENorm_comp_left_le (A : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (A ∘L T).hilbertSchmidtENorm ≤ ‖A‖ₑ * T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hsplit : ‖A‖ₑ * (T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹
      = (‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹ := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  rw [(A ∘L T).hilbertSchmidtENorm_eq b, T.hilbertSchmidtENorm_eq b, hsplit]
  exact ENNReal.rpow_le_rpow (hilbertSchmidtEnergy_comp_left_le A T b) (by norm_num)

/-- Precomposition contracts the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtENorm_comp_right_le (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (T ∘L B).hilbertSchmidtENorm ≤ T.hilbertSchmidtENorm * ‖B‖ₑ := by
  have h := ContinuousLinearMap.hilbertSchmidtENorm_comp_left_le B.adjoint T.adjoint
  rw [← ContinuousLinearMap.adjoint_comp, hilbertSchmidtENorm_adjoint,
    hilbertSchmidtENorm_adjoint, B.enorm_adjoint] at h
  rwa [mul_comm]

/-- `T` is a **Hilbert--Schmidt operator** when its Hilbert--Schmidt norm is finite.

The predicate is stated through the `ℝ≥0∞`-valued norm rather than through a summability
hypothesis so that it carries no choice of basis; `isHilbertSchmidt_iff_summable` recovers
the concrete form. -/
def IsHilbertSchmidt (T : E →L[𝕜] F) : Prop := T.hilbertSchmidtENorm ≠ ∞

/-- An operator is Hilbert--Schmidt exactly when its energy is finite; this is the bridge between
the predicate and the summability condition that is actually checked. -/
theorem isHilbertSchmidt_iff_energy_ne_top (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.IsHilbertSchmidt ↔ T.hilbertSchmidtEnergy b ≠ ∞ := by
  rw [IsHilbertSchmidt, T.hilbertSchmidtENorm_eq b, Ne, Ne,
    ENNReal.rpow_eq_top_iff_of_pos (by norm_num)]

/-- Concretely, `T` is Hilbert--Schmidt exactly when the squared column norms are
summable in any — equivalently, some — Hilbert basis. -/
theorem isHilbertSchmidt_iff_summable (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.IsHilbertSchmidt ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  rw [T.isHilbertSchmidt_iff_energy_ne_top b, hilbertSchmidtEnergy]
  have hcoe : ∀ i, ‖T (b i)‖ₑ ^ 2 = ((‖T (b i)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := fun i => by
    simp [enorm_eq_nnnorm]
  simp only [hcoe]
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp

/-- **The two-sided ideal bound.** -/
theorem hilbertSchmidtENorm_comp_le (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).hilbertSchmidtENorm ≤ ‖L‖ₑ * T.hilbertSchmidtENorm * ‖R‖ₑ := by
  refine ((L ∘L T).hilbertSchmidtENorm_comp_right_le R).trans ?_
  gcongr
  exact L.hilbertSchmidtENorm_comp_left_le T

end ContinuousLinearMap

namespace TauCeti

universe u v

/-- **The Hilbert--Schmidt operator ideal.**

This is the second instance of `TauCeti.SymmetricOperatorIdealFamily`, after the Ky Fan
families of `DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean`.  The two are
built from unrelated mathematics — approximation numbers there, orthonormal expansions here
— which is the evidence that the structure captures the right notion. -/
noncomputable def hilbertSchmidtIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := A.hilbertSchmidtENorm
  gauge_add_le A B := A.hilbertSchmidtENorm_add_le B
  gauge_smul c A := A.hilbertSchmidtENorm_smul c
  enorm_le_gauge A := A.enorm_le_hilbertSchmidtENorm
  gauge_comp_le L A R := ContinuousLinearMap.hilbertSchmidtENorm_comp_le L A R
  gauge_adjoint A := A.hilbertSchmidtENorm_adjoint

/-- Membership in the Hilbert--Schmidt ideal is exactly `IsHilbertSchmidt`. -/
theorem mem_hilbertSchmidtIdealFamily_carrier_iff {𝕜 : Type u} [RCLike 𝕜] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    A ∈ (hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.carrier ↔
      A.IsHilbertSchmidt := (Iff.rfl)
/-- The gauge of the Hilbert--Schmidt family is the Hilbert--Schmidt norm. -/
@[simp] theorem hilbertSchmidtIdealFamily_gauge {𝕜 : Type u} [RCLike 𝕜] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    (hilbertSchmidtIdealFamily.{u, v} 𝕜).toOperatorIdealFamily.gauge A =
      A.hilbertSchmidtENorm := (rfl)
end TauCeti
