/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import Mathlib.Analysis.MeanInequalities

/-!
# Extended Hilbert–Schmidt gauge laws

This donor retains the extended-valued gauge and its membership/limit consequences
while consumers move to the accepted rectangular family. Tau Ceti owns the energy,
real norm, operator-ideal family, and completeness; no parallel constructor or
completeness proof remains here.

## Main definitions and results

* `ContinuousLinearMap.hilbertSchmidtENorm`: the Hilbert--Schmidt norm, valued in `ℝ≥0∞`;
* `ContinuousLinearMap.hilbertSchmidtENorm_add_le`: the triangle inequality, which is
  Minkowski's inequality at `p = 2`;
* `ContinuousLinearMap.enorm_le_hilbertSchmidtENorm`: it dominates the operator norm;
* `ContinuousLinearMap.hilbertSchmidtENorm_comp_le`: the two-sided ideal bound;
* `ContinuousLinearMap.hilbertSchmidtENorm_adjoint`: it is adjoint-invariant;
* The ideal family and its completeness are consumed from
  `TauCeti.SymmetricOperatorIdealFamily.hilbertSchmidt`.

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
  simpa only [one_div] using S.rpow_hilbertSchmidtEnergy_add_le T b

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
    T.hilbertSchmidtEnergy_adjoint b c]

/-- Postcomposition contracts the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtENorm_comp_left_le (A : F →L[𝕜] G) (T : E →L[𝕜] F) :
    (A ∘L T).hilbertSchmidtENorm ≤ ‖A‖ₑ * T.hilbertSchmidtENorm := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hsplit : ‖A‖ₑ * (T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹
      = (‖A‖ₑ ^ 2 * T.hilbertSchmidtEnergy b) ^ (2 : ℝ)⁻¹ := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  rw [(A ∘L T).hilbertSchmidtENorm_eq b, T.hilbertSchmidtENorm_eq b, hsplit]
  exact ENNReal.rpow_le_rpow (hilbertSchmidtEnergy_comp_le_left A T b) (by norm_num)

/-- Precomposition contracts the Hilbert--Schmidt norm. -/
theorem hilbertSchmidtENorm_comp_right_le (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (T ∘L B).hilbertSchmidtENorm ≤ T.hilbertSchmidtENorm * ‖B‖ₑ := by
  have h := ContinuousLinearMap.hilbertSchmidtENorm_comp_left_le B.adjoint T.adjoint
  rw [← ContinuousLinearMap.adjoint_comp, hilbertSchmidtENorm_adjoint,
    hilbertSchmidtENorm_adjoint, LinearIsometryEquiv.enorm_map adjoint B] at h
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
  rw [T.isHilbertSchmidt_iff_energy_ne_top b, hilbertSchmidtEnergy_def]
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

/-! ### Closure properties of the class

The Hilbert--Schmidt operators form a self-adjoint two-sided ideal, and each of the
closure facts below is the corresponding `hilbertSchmidtENorm` estimate read as a
finiteness statement.  Nothing here needs a basis, a choice, or spectral theory: the
`ℝ≥0∞`-valued norm already carries all of it.
-/

omit [CompleteSpace F] in
/-- The zero operator is Hilbert--Schmidt. -/
@[simp] theorem isHilbertSchmidt_zero : (0 : E →L[𝕜] F).IsHilbertSchmidt := by
  simp [IsHilbertSchmidt]

omit [CompleteSpace F] in
/-- Negation does not change the class. -/
@[simp] theorem isHilbertSchmidt_neg_iff (T : E →L[𝕜] F) :
    (-T).IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hilbertSchmidtENorm_neg]

omit [CompleteSpace F] in
/-- A scalar multiple of a Hilbert--Schmidt operator is Hilbert--Schmidt. -/
theorem IsHilbertSchmidt.smul {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt) (c : 𝕜) :
    (c • T).IsHilbertSchmidt := by
  rw [IsHilbertSchmidt, hilbertSchmidtENorm_smul]
  exact ENNReal.mul_ne_top (by simp) hT

omit [CompleteSpace F] in
/-- Scaling by a nonzero scalar does not change the class. -/
theorem isHilbertSchmidt_smul_iff {c : 𝕜} (hc : c ≠ 0) (T : E →L[𝕜] F) :
    (c • T).IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  refine ⟨fun h => ?_, fun h => h.smul c⟩
  have := h.smul c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- **The class is closed under addition**, by the triangle inequality. -/
theorem IsHilbertSchmidt.add {S T : E →L[𝕜] F}
    (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) : (S + T).IsHilbertSchmidt :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hS, hT⟩) (hilbertSchmidtENorm_add_le S T)

/-- **The class is closed under subtraction.** -/
theorem IsHilbertSchmidt.sub {S T : E →L[𝕜] F}
    (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) : (S - T).IsHilbertSchmidt := by
  rw [sub_eq_add_neg]
  exact hS.add ((isHilbertSchmidt_neg_iff T).2 hT)

/-- **The class is self-adjoint.** -/
@[simp] theorem isHilbertSchmidt_adjoint_iff (T : E →L[𝕜] F) :
    T.adjoint.IsHilbertSchmidt ↔ T.IsHilbertSchmidt := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hilbertSchmidtENorm_adjoint]

/-- Postcomposition with a bounded operator stays in the class. -/
theorem IsHilbertSchmidt.comp_left {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt)
    (A : F →L[𝕜] G) : (A ∘L T).IsHilbertSchmidt :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hT)
    (hilbertSchmidtENorm_comp_left_le A T)

/-- Precomposition with a bounded operator stays in the class. -/
theorem IsHilbertSchmidt.comp_right {T : F →L[𝕜] G} (hT : T.IsHilbertSchmidt)
    (B : E →L[𝕜] F) : (T ∘L B).IsHilbertSchmidt :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hT (by simp))
    (hilbertSchmidtENorm_comp_right_le T B)

/-- **The two-sided ideal property**, as a statement about the class. -/
theorem IsHilbertSchmidt.comp {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt)
    (L : F →L[𝕜] G) (R : H →L[𝕜] E) : (L ∘L T ∘L R).IsHilbertSchmidt :=
  (hT.comp_left L).comp_right R

/-- **Every operator out of a finite-dimensional space is Hilbert--Schmidt**: the column
sum has finitely many terms.  This is the entry point a finite-dimensional argument needs,
and it is why the finite-dimensional theory never has to mention the class at all. -/
theorem isHilbertSchmidt_of_finiteDimensional [FiniteDimensional 𝕜 E] (T : E →L[𝕜] F) :
    T.IsHilbertSchmidt :=
  (T.isHilbertSchmidt_iff_summable
    (stdOrthonormalBasis 𝕜 E).toHilbertBasis).2 (summable_of_hasFiniteSupport (Set.toFinite _))

/-- **Fatou for the Hilbert--Schmidt gauge.**  The gauge is lower semicontinuous along
operator-norm convergence: if `T i → T` pointwise on a basis, the limit's energy is at most
the `liminf` of the energies.

This is the step that replaces the Ky Fan shortcut. TauCeti's canonical Ky Fan family gets
completeness from `‖A‖ ≤ kyFanGauge k A ≤ k ‖A‖`, so a gauge-Cauchy sequence is norm-Cauchy
*and* the norm limit is automatically a gauge limit. The Hilbert--Schmidt gauge is not
equivalent to the operator norm, so the limit has to be controlled term by term instead.
Fatou's lemma provides the needed bound as a `tsum` of `ℝ≥0∞`.

The proof is by finite sections rather than through `MeasureTheory.lintegral_liminf_le`
against the counting measure.  The two are the same argument, but the measure route obliges
the *basis index type* to carry `MeasurableSpace`, `MeasurableSingletonClass` and
`DiscreteMeasurableSpace`, and the filter to be countably generated, none of which the
statement is about; `∑'` over `ℝ≥0∞` is already a supremum of finite partial sums, so the
same Fatou step is `Filter.liminf_le_liminf` on each section. -/
theorem hilbertSchmidtENorm_le_liminf {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hptwise : ∀ i, Filter.Tendsto (fun n => ‖T n (b i)‖ₑ ^ 2) u
      (nhds (‖L (b i)‖ₑ ^ 2))) :
    L.hilbertSchmidtENorm ^ (2 : ℝ) ≤
      Filter.liminf (fun n => (T n).hilbertSchmidtENorm ^ (2 : ℝ)) u := by
  classical
  have hT : ∀ n, (T n).hilbertSchmidtENorm ^ (2 : ℝ) = ∑' i, ‖T n (b i)‖ₑ ^ 2 :=
    fun n => by rw [(T n).hilbertSchmidtENorm_rpow_two b, hilbertSchmidtEnergy_def]
  rw [L.hilbertSchmidtENorm_rpow_two b, L.hilbertSchmidtEnergy_eq_iSup_sum b]
  refine iSup_le fun s => ?_
  have hfin : Filter.Tendsto (fun n => ∑ i ∈ s, ‖T n (b i)‖ₑ ^ 2) u
      (nhds (∑ i ∈ s, ‖L (b i)‖ₑ ^ 2)) :=
    tendsto_finsetSum _ fun i _ => hptwise i
  calc ∑ i ∈ s, ‖L (b i)‖ₑ ^ 2
      = Filter.liminf (fun n => ∑ i ∈ s, ‖T n (b i)‖ₑ ^ 2) u := hfin.liminf_eq.symm
    _ ≤ Filter.liminf (fun n => (T n).hilbertSchmidtENorm ^ (2 : ℝ)) u :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => by
          rw [hT n]; exact ENNReal.sum_le_tsum s)


/-! ### The real-valued norm

The gauge of an operator ideal is `ℝ≥0∞`-valued, because a gauge has to be defined on
operators outside the ideal.  An estimate *inside* the ideal is an inequality between real
numbers, and stating it in `ℝ≥0∞` forces every consumer to carry finiteness through
arithmetic that does not need it.  So the ideal keeps the extended norm and this is its
real-valued reading, defined on all operators and equal to zero off the ideal.

The two are interchangeable exactly where it matters: `ofReal_hilbertSchmidtNorm` turns a
real statement into the extended one for a Hilbert--Schmidt operator, and
`hilbertSchmidtNorm_eq_toReal` identifies the accepted real norm with this gauge. -/

/-- The accepted real norm is the real value of the extended ideal gauge. -/
theorem hilbertSchmidtNorm_eq_toReal (T : E →L[𝕜] F) :
    T.hilbertSchmidtNorm = T.hilbertSchmidtENorm.toReal := by
  rw [T.hilbertSchmidtNorm_eq_toReal_rpow (TauCeti.chosenHilbertBasis 𝕜 E),
    T.hilbertSchmidtENorm_eq (TauCeti.chosenHilbertBasis 𝕜 E), one_div]

/-- On the ideal, the real norm determines the extended one. -/
theorem ofReal_hilbertSchmidtNorm {T : E →L[𝕜] F} (hT : T.IsHilbertSchmidt) :
    ENNReal.ofReal T.hilbertSchmidtNorm = T.hilbertSchmidtENorm :=
  by rw [hilbertSchmidtNorm_eq_toReal, ENNReal.ofReal_toReal hT]

/-- The real Hilbert--Schmidt norm is unchanged by negation. -/
@[simp] theorem hilbertSchmidtNorm_neg (T : E →L[𝕜] F) :
    (-T).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  simp only [hilbertSchmidtNorm_eq_toReal, hilbertSchmidtENorm_neg]

/-- **Contractions do not enlarge the Hilbert--Schmidt norm.**  This is the
two-sided ideal bound with both factors of norm at most one. -/
theorem hilbertSchmidtNorm_comp_isometries_le (L : F →L[𝕜] G) {T : E →L[𝕜] F}
    (hT : T.IsHilbertSchmidt) (R : H →L[𝕜] E) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    (L ∘L T ∘L R).hilbertSchmidtNorm ≤ T.hilbertSchmidtNorm := by
  calc (L ∘L T ∘L R).hilbertSchmidtNorm
      ≤ ‖L‖ * T.hilbertSchmidtNorm * ‖R‖ := hilbertSchmidtNorm_comp_comp_le L T R
          (TauCeti.chosenHilbertBasis 𝕜 E)
          ((T.isHilbertSchmidt_iff_energy_ne_top _).mp hT)
    _ ≤ 1 * T.hilbertSchmidtNorm * 1 := by
        gcongr <;> simp [hilbertSchmidtNorm_nonneg T]
    _ = T.hilbertSchmidtNorm := by ring



end ContinuousLinearMap
