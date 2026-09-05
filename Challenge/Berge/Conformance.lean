/-
# Berge maximum theorem fragments (pending: likely too narrow)

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


namespace TauCeti
open Filter Topology Set

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

/-- Stability of constrained minimizers under approximate minimization. -/
theorem exists_subseq_tendsto_isMinOn_of_approxMinOn
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K)
    {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x ∈ K, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x ∈ K, ∀ k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, IsMinOn F K ψ ∧
      Tendsto (fun t => z (φ t)) atTop (𝓝 ψ) := by
  obtain ⟨ψ, hψK, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq hz
  refine ⟨φ, hφ_mono, ψ, hψK, ?_, hφ_tendsto⟩
  rw [isMinOn_iff]
  intro x hx
  have hcont : Tendsto (fun t => F (z (φ t))) atTop (𝓝 (F ψ)) :=
    (hF.tendsto ψ).comp hφ_tendsto
  have hrhs : Tendsto (fun t => F x + ε x (φ t)) atTop (𝓝 (F x)) := by
    have hεφ : Tendsto (fun t => ε x (φ t)) atTop (𝓝 0) :=
      (hε x hx).comp hφ_mono.tendsto_atTop
    simpa using tendsto_const_nhds.add hεφ
  exact le_of_tendsto_of_tendsto hcont hrhs
    (Eventually.of_forall fun t => happrox x hx (φ t))

section
variable [FirstCountableTopology X]

/-- Sequential uniform convergence on a compact set from joint continuity. -/
theorem tendsto_eval_sub_of_isCompact
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hx : ∀ k, x k ∈ K) :
    Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) := by
  have hgp0 : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨a, _ha, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq (fun n => hx (ns n))
  refine ⟨φ, ?_⟩
  have hns' : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ_mono.tendsto_atTop
  have hpns : Tendsto (fun n => p (ns (φ n))) atTop (𝓝 p₀) := hp.comp hns'
  have h1 : Tendsto (fun n => g (p (ns (φ n))) (x (ns (φ n)))) atTop (𝓝 (g p₀ a)) :=
    (hg.tendsto (p₀, a)).comp (hpns.prodMk_nhds hφ_tendsto)
  have h2 : Tendsto (fun n => g p₀ (x (ns (φ n)))) atTop (𝓝 (g p₀ a)) :=
    (hgp0.tendsto a).comp hφ_tendsto
  simpa using h1.sub h2

/-- Sequential upper hemicontinuity of the argmin correspondence. -/
theorem tendsto_subseq_isMinOn_of_isMinOn
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K)
    (hxmin : ∀ k, IsMinOn (g (p k)) K (x k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  have hgp0 : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  have hsub : Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) :=
    tendsto_eval_sub_of_isCompact hK hg hp hxK
  refine exists_subseq_tendsto_isMinOn_of_approxMinOn hK hgp0 hxK
    (ε := fun y k => (g (p k) y - g p₀ y) + (g p₀ (x k) - g (p k) (x k))) ?_ ?_
  · intro y _hy
    have ha : Tendsto (fun k => g (p k) y - g p₀ y) atTop (𝓝 0) := by
      have hy' : Tendsto (fun k => g (p k) y) atTop (𝓝 (g p₀ y)) :=
        (hg.tendsto (p₀, y)).comp (hp.prodMk_nhds tendsto_const_nhds)
      have hc : Tendsto (fun _ : ℕ => g p₀ y) atTop (𝓝 (g p₀ y)) := tendsto_const_nhds
      simpa using hy'.sub hc
    have hb : Tendsto (fun k => g p₀ (x k) - g (p k) (x k)) atTop (𝓝 0) := by
      simpa [neg_sub] using hsub.neg
    simpa using ha.add hb
  · intro y hy k
    have hmin : g (p k) (x k) ≤ g (p k) y := (isMinOn_iff.mp (hxmin k)) y hy
    linarith

end

/-- Uniform `ε`–`δ` modulus form (finite family of continuous invariants). -/
theorem exists_modulus_isMinOn_family {P X : Type*} [PseudoMetricSpace P]
    [TopologicalSpace X] [FirstCountableTopology X]
    {ι : Type*} [Finite ι]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {ρ : ι → X → X → ℝ} (hρ : ∀ i, Continuous (Function.uncurry (ρ i)))
    (hρ0 : ∀ i x, ρ i x x = 0)
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ ∀ i, ρ i x x₀ < ε := by
  by_contra hcon
  push Not at hcon
  have hex := fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  choose p x hxK hxmin hpδ hbad using hex
  have hp : Tendsto p atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) hpδ tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, _hφ, x₀, hx₀K, hx₀min, htend⟩ :=
    tendsto_subseq_isMinOn_of_isMinOn hK hg hp hxK hxmin
  have hev : ∀ i, ∀ᶠ t in atTop, ρ i (x (φ t)) x₀ < ε := by
    intro i
    have hcont : Tendsto (fun t => ρ i (x (φ t)) x₀) atTop (𝓝 0) := by
      have := (hρ i).tendsto (x₀, x₀) |>.comp (htend.prodMk_nhds tendsto_const_nhds)
      rwa [show Function.uncurry (ρ i) (x₀, x₀) = 0 from hρ0 i x₀] at this
    exact hcont.eventually (eventually_lt_nhds hε)
  obtain ⟨t, ht⟩ := (eventually_all.mpr hev).exists
  obtain ⟨i, hi⟩ := hbad (φ t) x₀ hx₀K hx₀min
  exact absurd (ht i) (not_lt.mpr hi)

/-- Uniform closeness on a compact set, from the tube lemma rather than from
sequential compactness -- which is what keeps `X` free of
`[FirstCountableTopology]`. -/
private theorem eventually_forall_abs_sub_lt_of_isCompact' {X : Type*}
    [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) (p₀ : P) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, |g p x - g p₀ x| < ε := by
  refine hK.eventually_forall_of_forall_eventually fun x₀ _ => ?_
  have hcont : ContinuousAt (fun z : P × X => |g z.1 z.2 - g p₀ z.2|) (p₀, x₀) :=
    ((hg.continuousAt).sub
      ((hg.comp (continuous_const.prodMk continuous_snd)).continuousAt)).abs
  have hzero : |g p₀ x₀ - g p₀ x₀| = 0 := by simp
  exact hcont (by simpa [hzero] using Iio_mem_nhds hε)

/-- **Upper hemicontinuity of the argmin correspondence over a fixed compact set,
with no countability or separation hypothesis.**

Stated exactly as the library proves it.  `[FirstCountableTopology X]`,
`[T2Space X]` and `[(𝓝 p₀).IsCountablyGenerated]` are artifacts of routing the
proof through `UpperHemicontinuousAt.of_sequences`, not features of the
mathematics, and this statement carries none of them.  The argument is the
classical one through open `V` and the compact remainder `K \ V`. -/
theorem upperHemicontinuousAt_isMinOn {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) (p₀ : P) :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := by
  refine UpperHemicontinuousAt.of_forall_isOpen fun V hV hsub => ?_
  have hcont : ∀ q : P, ContinuousOn (g q) K := fun q =>
    (hg.comp (continuous_const.prodMk continuous_id)).continuousOn
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · filter_upwards with p using fun x hx => absurd hx.1 (Set.notMem_empty x)
  by_cases hKV : K ⊆ V
  · filter_upwards with p using fun x hx => hKV hx.1
  have hKVc : IsCompact (K \ V) := hK.diff hV
  have hKVne : (K \ V).Nonempty := by
    obtain ⟨x, hxK, hxV⟩ := Set.not_subset.mp hKV
    exact ⟨x, hxK, hxV⟩
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKne (hcont p₀)
  obtain ⟨y₀, hy₀mem, hy₀min⟩ := hKVc.exists_isMinOn hKVne ((hcont p₀).mono Set.sdiff_subset)
  have hgap : g p₀ x₀ < g p₀ y₀ := by
    rcases lt_or_ge (g p₀ x₀) (g p₀ y₀) with h | h
    · exact h
    · exact absurd (hsub ⟨hy₀mem.1, fun z hz => le_trans h (hx₀min hz)⟩) hy₀mem.2
  set ε := (g p₀ y₀ - g p₀ x₀) / 3 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [eventually_forall_abs_sub_lt_of_isCompact' hK hg p₀ hε] with p hp x hx
  by_contra hxV
  have hxKV : x ∈ K \ V := ⟨hx.1, hxV⟩
  have h1 : g p₀ y₀ ≤ g p₀ x := hy₀min hxKV
  have h2 : |g p x - g p₀ x| < ε := hp x hx.1
  have h3 : |g p x₀ - g p₀ x₀| < ε := hp x₀ hx₀K
  have h4 : g p x ≤ g p x₀ := hx.2 hx₀K
  have e2 := abs_lt.mp h2
  have e3 := abs_lt.mp h3
  have : g p₀ y₀ - g p₀ x₀ < 2 * ε := by linarith
  rw [hεdef] at this
  linarith

-- `[FirstCountableTopology X]` precedes `[FirstCountableTopology P]` to match the
-- ForMathlib source, where the former is an accumulated section instance and the
-- latter the theorem's own; the comparator needs the exact instance order.
theorem continuous_iInf_of_isCompact [FirstCountableTopology X] [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := by
  haveI : Nonempty ↥K := hKne.to_subtype
  have hgcont : ∀ q : P, Continuous (g q) :=
    fun q => hg.comp (continuous_const.prodMk continuous_id)
  have hbdd : ∀ q : P, BddBelow (Set.range fun x : ↥K => g q ↑x) := by
    intro q
    refine (hK.bddBelow_image (hgcont q).continuousOn).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨↑x, x.2, rfl⟩
  have hVle : ∀ (q : P) (y : X), y ∈ K → (⨅ x : ↥K, g q ↑x) ≤ g q y :=
    fun q y hy => ciInf_le (hbdd q) ⟨y, hy⟩
  have hval : ∀ (q : P) (xq : X), xq ∈ K → IsMinOn (g q) K xq →
      (⨅ x : ↥K, g q ↑x) = g q xq := by
    intro q xq hxqK hmin
    exact le_antisymm (hVle q xq hxqK) (le_ciInf fun x => (isMinOn_iff.mp hmin) ↑x x.2)
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKne (hgcont p₀).continuousOn
  choose xseq hxseqK hxseqmin using fun k => hK.exists_isMinOn hKne (hgcont (p k)).continuousOn
  have hVp0 : (⨅ x : ↥K, g p₀ ↑x) = g p₀ x₀ := hval p₀ x₀ hx₀K hx₀min
  have hi : Tendsto (fun k => g (p k) x₀) atTop (𝓝 (⨅ x : ↥K, g p₀ ↑x)) := by
    rw [hVp0]
    exact (hg.tendsto (p₀, x₀)).comp (hp.prodMk_nhds tendsto_const_nhds)
  have hlo : Tendsto (fun k => (⨅ x : ↥K, g p₀ ↑x) +
      (g (p k) (xseq k) - g p₀ (xseq k))) atTop (𝓝 (⨅ x : ↥K, g p₀ ↑x)) := by
    have := tendsto_eval_sub_of_isCompact hK hg hp hxseqK
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hi (fun k => ?_) (fun k => ?_)
  · simp only [Function.comp_apply]
    have hV : (⨅ x : ↥K, g (p k) ↑x) = g (p k) (xseq k) :=
      hval (p k) (xseq k) (hxseqK k) (hxseqmin k)
    have := hVle p₀ (xseq k) (hxseqK k)
    rw [hV]; linarith
  · simpa using hVle (p k) x₀ hx₀K

theorem exists_modulus_isMinOn {P X : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_modulus_isMinOn_family hK hg
    (ρ := fun _ : Unit => dist) (fun _ => continuous_dist) (fun _ => dist_self) p₀ hε
  refine ⟨δ, hδ, fun p x hxK hxmin hpd => ?_⟩
  obtain ⟨x₀, hx₀K, hx₀min, hclose⟩ := h p x hxK hxmin hpd
  exact ⟨x₀, hx₀K, hx₀min, hclose ()⟩

end TauCeti