/-
# TendstoInMeasure from a vanishing rate (pending: verify substantive)

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

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}

theorem tendstoInMeasure_of_tendsto_measure_dist_le_rate [PseudoMetricSpace E]
    [IsProbabilityMeasure μ] {f : ι → α → E} {g : α → E} {rate : ι → ℝ}
    (hrate : Tendsto rate l (𝓝 0))
    (hmeas : ∀ i, NullMeasurableSet {x | dist (f i x) (g x) ≤ rate i} μ)
    (hprob : Tendsto (fun i => μ {x | dist (f i x) (g x) ≤ rate i}) l (𝓝 1)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  have hofReal : Tendsto (fun i => ENNReal.ofReal (rate i)) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hrate
  have hev : ∀ᶠ i in l, ENNReal.ofReal (rate i) < ε :=
    hofReal.eventually_lt tendsto_const_nhds hε
  have hcompl : Tendsto (fun i => μ {x | dist (f i x) (g x) ≤ rate i}ᶜ) l (𝓝 0) := by
    have h1 : Tendsto (fun i => (1 : ℝ≥0∞) - μ {x | dist (f i x) (g x) ≤ rate i}) l (𝓝 0) :=
      (ENNReal.tendsto_const_sub_nhds_zero_iff ENNReal.one_ne_top
        (fun _ => prob_le_one)).mpr hprob
    refine h1.congr fun i => ?_
    rw [measure_compl₀ (hmeas i) (measure_ne_top μ _), measure_univ]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcompl
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev] with i hi
  apply measure_mono
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  rw [Set.mem_compl_iff, Set.mem_setOf_eq]
  intro hle
  rw [edist_dist] at hx
  have hmono : ENNReal.ofReal (dist (f i x) (g x)) ≤ ENNReal.ofReal (rate i) :=
    ENNReal.ofReal_le_ofReal hle
  exact absurd ((hx.trans hmono).trans_lt hi) (lt_irrefl ε)

end ForMathlib
