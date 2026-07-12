/-
# CFC-in-element + compact-existential measurability (pending: destination unsettled)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open MeasureTheory Set

variable {Ω A : Type*} [MeasurableSpace Ω]
  [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [ContinuousStar A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NormOneClass A]
  [MeasurableSpace A] [BorelSpace A]

/-- **Measurability of the continuous functional calculus in the element.** -/
theorem measurable_cfc_comp
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : Ω → A) (hB : Measurable B) (hsa : ∀ ω, IsSelfAdjoint (B ω)) :
    Measurable (fun ω => cfc f (B ω)) := by
  sorry

end ForMathlib

namespace ForMathlib

open Filter Topology TopologicalSpace

/-- **Measurability of a compactly-quantified existential constraint.** -/
theorem measurableSet_exists_mem_le
    {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Y} (hS : IsCompact S)
    {F : Y → Ω → ℝ}
    (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hFm : ∀ y ∈ S, Measurable (F y)) (c : ℝ) :
    MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ c} := by
  haveI : TopologicalSpace.SeparableSpace S := hS.isSeparable.separableSpace
  obtain ⟨t, htc, htd⟩ := TopologicalSpace.exists_countable_dense (S : Set Y)
  have hset : {ω | ∃ y ∈ S, F y ω ≤ c} =
      ⋂ n : ℕ, ⋃ p ∈ t, {ω | F (p : Y) ω ≤ c + 1 / (n + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hyS, hy⟩ n
      have hcont : Continuous (fun p : S => F (p : Y) ω) := (hFc ω).restrict
      have hyU : (⟨y, hyS⟩ : S) ∈
          (fun p : S => F (p : Y) ω) ⁻¹' Set.Iio (c + 1 / (n + 1)) := by
        have : (0 : ℝ) < 1 / (n + 1) := by positivity
        simp only [Set.mem_preimage, Set.mem_Iio]; linarith
      obtain ⟨p, hpt, hpU⟩ :=
        htd.exists_mem_open (hcont.isOpen_preimage _ isOpen_Iio) ⟨_, hyU⟩
      exact ⟨p, hpt, le_of_lt hpU⟩
    · intro h
      choose p hpt hp using h
      obtain ⟨y, hyS, φ, hφ, hlim⟩ := hS.tendsto_subseq (fun n => (p n).2)
      refine ⟨y, hyS, ?_⟩
      have hcont : Continuous (fun q : S => F (q : Y) ω) := (hFc ω).restrict
      have hsub : Tendsto (fun k => (p (φ k) : S)) atTop (𝓝 (⟨y, hyS⟩ : S)) := by
        rw [tendsto_subtype_rng]; exact hlim
      have hFlim : Tendsto (fun k => F (p (φ k) : Y) ω) atTop (𝓝 (F y ω)) :=
        (hcont.tendsto _).comp hsub
      have hrate : Tendsto (fun k => c + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 c) := by
        have : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
        simpa using (tendsto_const_nhds.add this)
      exact le_of_tendsto_of_tendsto' hFlim hrate fun k => hp (φ k)
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  refine MeasurableSet.biUnion htc fun p _ => ?_
  exact measurableSet_le (hFm (p : Y) p.2) measurable_const

end ForMathlib
