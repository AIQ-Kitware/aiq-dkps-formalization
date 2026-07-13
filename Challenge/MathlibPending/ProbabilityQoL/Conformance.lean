/-
# Probability QoL micro-lemmas (pending: too small to stand alone)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
/-!
## Comparator maintenance rule

The proof holes in this module are deliberate challenge placeholders. Do not
discharge them in this repository and do not count them as formalization debt.
Implementations belong in the project modules imported by the paired
`Leaderboard.lean`; Comparator verifies that those implementations match these
statements and use only the permitted kernel dependencies.
-/

import Mathlib

namespace ForMathlib

open MeasureTheory
open scoped ENNReal

/-- For a probability measure, `1 - μ sᶜ ≤ μ s`, with no measurability assumption on `s`. -/
theorem one_sub_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) : 1 - μ sᶜ ≤ μ s := by
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
    _ = μ (s ∪ sᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ s + μ sᶜ := measure_union_le s sᶜ

/-- **Uncentered second-moment Chebyshev.** -/
theorem meas_gt_le_ofReal_integral_sq_div_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY_int : Integrable (fun ω => Y ω ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∫ ω, Y ω ^ 2 ∂P ≤ v) :
    P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  have hη2 : (0 : ℝ) < η ^ 2 := by positivity
  have hnonneg : 0 ≤ᵐ[P] fun ω => Y ω ^ 2 := ae_of_all _ fun ω => sq_nonneg _
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hY_int (η ^ 2)
  have hsub : {ω | η < Y ω} ⊆ {ω | η ^ 2 ≤ Y ω ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith [hω, hη, mul_pos (by linarith : (0 : ℝ) < Y ω - η)
      (by linarith : (0 : ℝ) < Y ω + η)]
  have hPreal : P.real {ω | η ^ 2 ≤ Y ω ^ 2} ≤ v / η ^ 2 := by
    rw [le_div_iff₀ hη2]
    calc P.real {ω | η ^ 2 ≤ Y ω ^ 2} * η ^ 2
        = η ^ 2 * P.real {ω | η ^ 2 ≤ Y ω ^ 2} := mul_comm _ _
      _ ≤ ∫ ω, Y ω ^ 2 ∂P := hmark
      _ ≤ v := hmoment
  calc P {ω | η < Y ω} ≤ P {ω | η ^ 2 ≤ Y ω ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | η ^ 2 ≤ Y ω ^ 2}) :=
        (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (v / η ^ 2) := ENNReal.ofReal_le_ofReal hPreal

end ForMathlib
