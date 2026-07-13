/-
# CFC-in-element + compact-existential measurability (pending: destination unsettled)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/

import Mathlib

/-!
## Comparator maintenance rule

The proof holes in this module are deliberate challenge placeholders. Do not
discharge them in this repository and do not count them as formalization debt.
Implementations belong in the project modules imported by the paired
`Leaderboard.lean`; Comparator verifies that those implementations match these
statements and use only the permitted kernel dependencies.
-/


namespace ForMathlib

open MeasureTheory Set

variable {Ω A : Type*} [MeasurableSpace Ω]
  [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [ContinuousStar A] [CompleteSpace A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NormOneClass A]
  [MeasurableSpace A] [BorelSpace A]

/-- **Measurability from a countable restrict-cover.** -/
theorem measurable_of_iUnion_restrict {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {g : Ω → A} {s : ℕ → Set Ω}
    (hs : ∀ k, MeasurableSet (s k)) (hcov : (⋃ k, s k) = univ)
    (hg : ∀ k, Measurable ((s k).restrict g)) : Measurable g := by
  intro t ht
  have hpre : g ⁻¹' t = ⋃ k, ((↑) : s k → Ω) '' ((s k).restrict g ⁻¹' t) := by
    apply Set.eq_of_subset_of_subset
    · intro ω hω
      have hmem : ω ∈ (⋃ k, s k) := by rw [hcov]; trivial
      rw [Set.mem_iUnion] at hmem
      obtain ⟨k, hk⟩ := hmem
      rw [Set.mem_iUnion]
      exact ⟨k, ⟨ω, hk⟩, hω, rfl⟩
    · intro ω hω
      rw [Set.mem_iUnion] at hω
      obtain ⟨k, ⟨x, hx⟩, hxt, rfl⟩ := hω
      exact hxt
  rw [hpre]
  refine MeasurableSet.iUnion fun k => ?_
  exact (MeasurableEmbedding.subtype_coe (hs k)).measurableSet_image.mpr (hg k ht)

/-- **Measurability of the continuous functional calculus in the element.** -/
theorem measurable_cfc_comp
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : Ω → A) (hB : Measurable B) (hsa : ∀ ω, IsSelfAdjoint (B ω)) :
    Measurable (fun ω => cfc f (B ω)) := by
  -- Cover `Ω` by the pieces `{ω | ‖B ω‖ ≤ k}`, `k : ℕ`.
  set s : ℕ → Set Ω := fun k => {ω | ‖B ω‖ ≤ (k : ℝ)} with hsdef
  have hsmeas : ∀ k, MeasurableSet (s k) := fun k => hB.norm measurableSet_Iic
  have hcover : (⋃ k, s k) = univ := by
    ext ω
    simp only [hsdef, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := exists_nat_ge ‖B ω‖
    exact ⟨k, hk⟩
  refine measurable_of_iUnion_restrict hsmeas hcover (fun k => ?_)
  -- On `{a | IsSelfAdjoint a ∧ spectrum ⊆ closedBall 0 k}`, `cfc f` is continuous.
  have hcontOn : ContinuousOn (cfc f)
      {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)} :=
    continuousOn_cfc A (isCompact_closedBall 0 (k : ℝ)) f hf.continuousOn
  -- `B` maps the `k`-piece into that set (spectrum bounded by the norm).
  have hmaps : ∀ ω : (s k),
      B ω ∈ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)} := by
    rintro ⟨ω, hω⟩
    exact ⟨hsa ω, (spectrum.subset_closedBall_norm (B ω)).trans
      (Metric.closedBall_subset_closedBall hω)⟩
  -- Restrict `cfc f` to a continuous map and compose with the measurable corestriction.
  have hcont' : Continuous
      (fun x : {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)} =>
        cfc f (x : A)) := continuousOn_iff_continuous_restrict.mp hcontOn
  have hcore : Measurable
      (fun ω : (s k) =>
        (⟨B ω, hmaps ω⟩ :
          {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Metric.closedBall 0 (k : ℝ)})) :=
    (hB.comp measurable_subtype_coe).subtype_mk
  exact hcont'.measurable.comp hcore

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
