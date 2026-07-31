/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidtEnergy
import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

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

/-- **Minkowski's inequality at `p = 2` for `tsum`.**  Mathlib's `ENNReal.Lp_add_le` is
stated for a `Finset`; this is the extension to an unconditional sum, which in `ℝ≥0∞` needs
no summability hypothesis.

The proof is the standard supremum argument: the finite inequality bounds every partial sum
of the left side by the square of the right side, and `∑'` is the supremum of its partial
sums. -/
theorem tsum_sq_add_rpow_le (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ 2) ^ (2 : ℝ)⁻¹ ≤
      (∑' i, f i ^ 2) ^ (2 : ℝ)⁻¹ + (∑' i, g i ^ 2) ^ (2 : ℝ)⁻¹ := by
  simp only [← ENNReal.rpow_two]
  set A := (∑' i, f i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ with hA
  set B := (∑' i, g i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ with hB
  have hsq : ∀ x : ℝ≥0∞, (x ^ (2 : ℝ)⁻¹) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have key : ∀ s : Finset ι, ∑ i ∈ s, (f i + g i) ^ (2 : ℝ) ≤ (A + B) ^ (2 : ℝ) := by
    intro s
    have hfin := ENNReal.Lp_add_le (s := s) (f := f) (g := g) (p := 2) one_le_two
    rw [one_div] at hfin
    have hfA : (∑ i ∈ s, f i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤ A :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num)
    have hgB : (∑ i ∈ s, g i ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤ B :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by norm_num)
    calc ∑ i ∈ s, (f i + g i) ^ (2 : ℝ)
        = ((∑ i ∈ s, (f i + g i) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) ^ (2 : ℝ) := (hsq _).symm
      _ ≤ (A + B) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (hfin.trans (add_le_add hfA hgB)) (by norm_num)
  have hsum : ∑' i, (f i + g i) ^ (2 : ℝ) ≤ (A + B) ^ (2 : ℝ) :=
    ENNReal.tsum_eq_iSup_sum.trans_le (iSup_le key)
  calc (∑' i, (f i + g i) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹
      ≤ ((A + B) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = A + B := by rw [← ENNReal.rpow_mul]; norm_num

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

/-- **Fatou for the Hilbert--Schmidt gauge.**  The gauge is lower semicontinuous along
operator-norm convergence: if `T i → T` pointwise on a basis, the limit's energy is at most
the `liminf` of the energies.

This is the step that replaces the Ky Fan shortcut.  `kyFanIdealFamily` gets completeness
from `‖A‖ ≤ kyFanGauge k A ≤ k ‖A‖`, so a gauge-Cauchy sequence is norm-Cauchy *and* the
norm limit is automatically a gauge limit.  The Hilbert--Schmidt gauge is not equivalent to
the operator norm, so the second half fails and the limit has to be controlled term by term
instead -- which is exactly Fatou's lemma against the counting measure. -/
theorem hilbertSchmidtENorm_le_liminf {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι] (b : HilbertBasis ι 𝕜 E)
    {u : Filter ℕ} [u.NeBot] [u.IsCountablyGenerated]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hptwise : ∀ i, Filter.Tendsto (fun n => ‖T n (b i)‖ₑ ^ 2) u
      (nhds (‖L (b i)‖ₑ ^ 2))) :
    L.hilbertSchmidtENorm ^ (2 : ℝ) ≤
      Filter.liminf (fun n => (T n).hilbertSchmidtENorm ^ (2 : ℝ)) u := by
  classical
  have hL : L.hilbertSchmidtENorm ^ (2 : ℝ) = ∑' i, ‖L (b i)‖ₑ ^ 2 :=
    L.hilbertSchmidtENorm_rpow_two b
  have hT : ∀ n, (T n).hilbertSchmidtENorm ^ (2 : ℝ) = ∑' i, ‖T n (b i)‖ₑ ^ 2 :=
    fun n => (T n).hilbertSchmidtENorm_rpow_two b
  rw [hL]
  simp only [hT]
  have hlim : ∀ i, ‖L (b i)‖ₑ ^ 2 = Filter.liminf (fun n => ‖T n (b i)‖ₑ ^ 2) u :=
    fun i => ((hptwise i).liminf_eq).symm
  simp only [hlim]
  simpa only [MeasureTheory.lintegral_count] using
    MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count)
      (f := fun n i => ‖T n (b i)‖ₑ ^ 2) (fun n => measurable_of_countable _)

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
