/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib

/-!
# Davis--Kahan 1970, Section 9: domain limitation example

The source displays a geometric trial sequence whose image under a diagonal
unbounded operator is the constant sequence, hence is not square summable.  It
then notes that an arbitrarily small modification repairs the domain issue.
Here the repair is made explicit by finite truncation.  The statements below
are sequence-level and avoid pretending that an undefined residual is a vector
of `ell^2`.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- The geometric trial sequence. -/
def rawTrialSequence (μ : ℝ) (n : ℕ) : ℝ := μ ^ n

/-- The diagonal multiplier used in the source example. -/
noncomputable def diagonalMultiplier (μ : ℝ) (n : ℕ) : ℝ := (μ ^ n)⁻¹

/-- The pointwise image of the geometric trial sequence. -/
noncomputable def rawDiagonalImage (μ : ℝ) (n : ℕ) : ℝ :=
  diagonalMultiplier μ n * rawTrialSequence μ n

/-- The diagonal multiplier exactly cancels the geometric trial sequence, so every entry of the
image is `1`.  This is why the partial energies grow like `N` and the raw sequence is outside the
domain. -/
lemma rawDiagonalImage_eq_one {μ : ℝ} (hμ : μ ≠ 0) (n : ℕ) :
    rawDiagonalImage μ n = 1 := by
  unfold rawDiagonalImage diagonalMultiplier rawTrialSequence
  exact inv_mul_cancel₀ (pow_ne_zero n hμ)

/-- Every length-`N` partial square energy of the raw image equals `N`; this is
the finite certificate of divergence used by the domain counterexample. -/
theorem rawDiagonalImage_partial_energy
    {μ : ℝ} (hμ : μ ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, rawDiagonalImage μ n ^ 2 = N := by
  simp [rawDiagonalImage_eq_one hμ]

/-- Finite truncation gives a concrete nearby sequence in the diagonal
operator's domain. -/
def truncatedTrialSequence (μ : ℝ) (N n : ℕ) : ℝ :=
  if n < N then μ ^ n else 0

/-- Image of the truncated trial sequence. -/
noncomputable def truncatedDiagonalImage (μ : ℝ) (N n : ℕ) : ℝ :=
  diagonalMultiplier μ n * truncatedTrialSequence μ N n

/-- Below the cut the truncation agrees with the raw sequence. -/
lemma truncatedTrialSequence_eq_raw {μ : ℝ} {N n : ℕ} (hn : n < N) :
    truncatedTrialSequence μ N n = rawTrialSequence μ n := by
  simp [truncatedTrialSequence, rawTrialSequence, hn]

/-- Above the cut the truncation vanishes, which is what puts it in the domain. -/
lemma truncatedTrialSequence_eq_zero {μ : ℝ} {N n : ℕ} (hn : N ≤ n) :
    truncatedTrialSequence μ N n = 0 := by
  simp [truncatedTrialSequence, not_lt.mpr hn]

/-- Below the cut the truncated image is still `1`. -/
lemma truncatedDiagonalImage_eq_one
    {μ : ℝ} (hμ : μ ≠ 0) {N n : ℕ} (hn : n < N) :
    truncatedDiagonalImage μ N n = 1 := by
  simp [truncatedDiagonalImage, truncatedTrialSequence, diagonalMultiplier,
    hn, inv_mul_cancel₀ (pow_ne_zero n hμ)]

/-- Above the cut it vanishes, so the truncated image has finite energy `N` -- finite for each `N`,
unbounded in `N`, which is exactly the domain obstruction. -/
lemma truncatedDiagonalImage_eq_zero
    {μ : ℝ} {N n : ℕ} (hn : N ≤ n) :
    truncatedDiagonalImage μ N n = 0 := by
  simp [truncatedDiagonalImage, truncatedTrialSequence, not_lt.mpr hn]

/-- The corrected residual has exactly `N` units of square energy and finite
support. -/
theorem truncatedDiagonalImage_energy
    {μ : ℝ} (hμ : μ ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, truncatedDiagonalImage μ N n ^ 2 = N := by
  -- the rewrite is conditional on `n < N`, so it has to happen under the
  -- membership hypothesis rather than in a bare `simp` set
  have hterm : ∀ n ∈ Finset.range N, truncatedDiagonalImage μ N n ^ 2 = 1 := by
    intro n hn
    rw [truncatedDiagonalImage_eq_one hμ (Finset.mem_range.mp hn), one_pow]
  rw [Finset.sum_congr rfl hterm]
  simp

/-- Outside the truncation range the corrected image vanishes. -/
theorem truncatedDiagonalImage_support
    (μ : ℝ) (N n : ℕ) (hn : N ≤ n) :
    truncatedDiagonalImage μ N n = 0 :=
  truncatedDiagonalImage_eq_zero hn

/-- Truncation changes only the geometric tail. -/
theorem raw_sub_truncated
    (μ : ℝ) (N n : ℕ) :
    rawTrialSequence μ n - truncatedTrialSequence μ N n =
      if n < N then 0 else μ ^ n := by
  by_cases hn : n < N
  · simp [rawTrialSequence, truncatedTrialSequence, hn]
  · simp [rawTrialSequence, truncatedTrialSequence, hn]

/-- On every fixed initial segment, sufficiently long truncations agree exactly
with the original trial sequence. -/
theorem truncation_eventually_agrees_on_prefix
    (μ : ℝ) (K N : ℕ) (hKN : K ≤ N) :
    ∀ n < K, truncatedTrialSequence μ N n = rawTrialSequence μ n := by
  intro n hn
  exact truncatedTrialSequence_eq_raw (lt_of_lt_of_le hn hKN)

/-! ## The example as an operator on `ℓ²`

The sequence lemmas above are the arithmetic of the source example.  This section
puts them where the source puts them: an honest unbounded diagonal operator on
`ℓ²(ℕ)`, its maximal domain, and a trial vector that is *in the space* and *in the
form domain* but *not in the operator domain*.

That is the whole point of the example.  A residual-based theorem needs `D x`,
which does not exist here; a form-based theorem needs `∑ dₙ |xₙ|²`, which is
finite.  So the two families of estimates are genuinely different in scope, and
the difference is not an artefact of how one states them. -/

open scoped ENNReal

/-- The ambient sequence space of the example. -/
abbrev DomainLimitationSpace : Type := lp (fun _ : ℕ => ℝ) 2

/-- **The maximal domain of the diagonal operator with multiplier `d`**: the
vectors whose scaled sequence is still square summable. -/
def diagonalDomain (d : ℕ → ℝ) : Submodule ℝ DomainLimitationSpace where
  carrier := {x | Memℓp (fun n => d n * (x : ℕ → ℝ) n) 2}
  add_mem' {x y} hx hy := by
    have h : (fun n => d n * ((x + y : DomainLimitationSpace) : ℕ → ℝ) n)
        = fun n => d n * (x : ℕ → ℝ) n + d n * (y : ℕ → ℝ) n := by
      funext n
      show d n * ((x : ℕ → ℝ) n + (y : ℕ → ℝ) n) = _
      ring
    rw [Set.mem_setOf_eq, h]
    exact hx.add hy
  zero_mem' := by
    have h : (fun n => d n * ((0 : DomainLimitationSpace) : ℕ → ℝ) n) = fun _ => 0 := by
      funext n
      show d n * (0 : ℝ) = 0
      ring
    rw [Set.mem_setOf_eq, h]
    exact zero_memℓp
  smul_mem' c {x} hx := by
    have h : (fun n => d n * ((c • x : DomainLimitationSpace) : ℕ → ℝ) n)
        = fun n => c • (d n * (x : ℕ → ℝ) n) := by
      funext n
      show d n * (c * (x : ℕ → ℝ) n) = c * (d n * (x : ℕ → ℝ) n)
      ring
    rw [Set.mem_setOf_eq, h]
    exact hx.const_smul c

theorem mem_diagonalDomain_iff (d : ℕ → ℝ) (x : DomainLimitationSpace) :
    x ∈ diagonalDomain d ↔ Memℓp (fun n => d n * (x : ℕ → ℝ) n) 2 := Iff.rfl

/-- **The unbounded diagonal operator**, on its maximal domain. -/
noncomputable def diagonalOperator (d : ℕ → ℝ) :
    DomainLimitationSpace →ₗ.[ℝ] DomainLimitationSpace where
  domain := diagonalDomain d
  toFun :=
    { toFun := fun x => ⟨fun n => d n * ((x : DomainLimitationSpace) : ℕ → ℝ) n, x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        funext n
        show d n * (((x : DomainLimitationSpace) : ℕ → ℝ) n
            + ((y : DomainLimitationSpace) : ℕ → ℝ) n)
          = d n * ((x : DomainLimitationSpace) : ℕ → ℝ) n
            + d n * ((y : DomainLimitationSpace) : ℕ → ℝ) n
        ring
      map_smul' := fun c x => by
        apply Subtype.ext
        funext n
        show d n * (c * ((x : DomainLimitationSpace) : ℕ → ℝ) n)
          = c * (d n * ((x : DomainLimitationSpace) : ℕ → ℝ) n)
        ring }

@[simp]
theorem diagonalOperator_apply (d : ℕ → ℝ) (x : (diagonalOperator d).domain) (n : ℕ) :
    ((diagonalOperator d x : DomainLimitationSpace) : ℕ → ℝ) n
      = d n * ((x : DomainLimitationSpace) : ℕ → ℝ) n := rfl

/-- The `ℓ²` membership criterion, with the exponent already evaluated. -/
theorem memℓp_two_of_summable_sq {f : ℕ → ℝ}
    (hf : Summable fun n => f n ^ 2) : Memℓp f 2 := by
  refine memℓp_gen ?_
  have h : (fun n => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) = fun n => f n ^ 2 := by
    funext n
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [h]
  exact hf

/-- The converse reading of the same criterion. -/
theorem summable_sq_of_memℓp_two {f : ℕ → ℝ} (hf : Memℓp f 2) :
    Summable fun n => f n ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (f := f) (by norm_num)).1 hf
  have heq : (fun n => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) = fun n => f n ^ 2 := by
    funext n
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rwa [heq] at h

/-- The geometric trial vector of the source example. -/
noncomputable def geometricTrial {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    DomainLimitationSpace :=
  ⟨fun n => rawTrialSequence μ n, by
    refine memℓp_two_of_summable_sq ?_
    have h : (fun n : ℕ => rawTrialSequence μ n ^ 2) = fun n : ℕ => (μ ^ 2) ^ n := by
      funext n
      rw [rawTrialSequence, ← pow_mul, ← pow_mul, mul_comm]
    rw [h]
    exact summable_geometric_of_lt_one (by positivity) (by nlinarith)⟩

@[simp]
theorem geometricTrial_apply {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (n : ℕ) :
    ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n = μ ^ n := rfl

/-- **The trial vector is outside the operator domain.**  Its image is the
constant sequence `1`, whose squares are not summable. -/
theorem geometricTrial_notMem_diagonalDomain
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    geometricTrial hμ0.le hμ1 ∉ diagonalDomain (diagonalMultiplier μ) := by
  intro hmem
  rw [mem_diagonalDomain_iff] at hmem
  have himage : (fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n)
      = fun _ : ℕ => (1 : ℝ) := by
    funext n
    rw [geometricTrial_apply]
    exact rawDiagonalImage_eq_one (ne_of_gt hμ0) n
  rw [himage] at hmem
  have hsum : Summable fun _ : ℕ => (1 : ℝ) ^ 2 := summable_sq_of_memℓp_two hmem
  simp only [one_pow] at hsum
  have hzero : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hsum.tendsto_atTop_zero tendsto_const_nhds
  exact zero_ne_one hzero

/-- **The trial vector is inside the form domain.**  The form sum `∑ dₙ |xₙ|²` is
the geometric series `∑ μⁿ`, which converges.

This is the asymmetry the source is pointing at: the same vector supplies a
useful Rayleigh quotient and no residual at all. -/
theorem geometricTrial_form_summable {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    Summable fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2 := by
  have h : (fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      = fun n => μ ^ n := by
    funext n
    have hne : μ ^ n ≠ 0 := ne_of_gt (pow_pos hμ0 n)
    rw [geometricTrial_apply, diagonalMultiplier]
    field_simp
  rw [h]
  exact summable_geometric_of_lt_one hμ0.le hμ1

/-- The finite truncation, as a vector of the space. -/
noncomputable def truncatedTrial (μ : ℝ) (N : ℕ) : DomainLimitationSpace :=
  ⟨fun n => truncatedTrialSequence μ N n, by
    refine memℓp_two_of_summable_sq ?_
    refine summable_of_ne_finset_zero (s := Finset.range N) ?_
    intro n hn
    rw [truncatedTrialSequence_eq_zero (by simpa using hn), sq, mul_zero]⟩

@[simp]
theorem truncatedTrial_apply (μ : ℝ) (N n : ℕ) :
    ((truncatedTrial μ N : DomainLimitationSpace) : ℕ → ℝ) n
      = truncatedTrialSequence μ N n := rfl

/-- **The truncation is inside the operator domain**: its image has finite
support.  This is the source's "arbitrarily small modification" that repairs the
domain obstruction. -/
theorem truncatedTrial_mem_diagonalDomain (μ : ℝ) (N : ℕ) :
    truncatedTrial μ N ∈ diagonalDomain (diagonalMultiplier μ) := by
  rw [mem_diagonalDomain_iff]
  refine memℓp_two_of_summable_sq ?_
  refine summable_of_ne_finset_zero (s := Finset.range N) ?_
  intro n hn
  rw [truncatedTrial_apply, truncatedTrialSequence_eq_zero (by simpa using hn),
    mul_zero, sq, mul_zero]

/-- On every prescribed prefix, long enough truncations agree with the trial
vector exactly. -/
theorem truncatedTrial_eq_geometricTrial_of_lt
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) {K N : ℕ} (hKN : K ≤ N) {n : ℕ} (hn : n < K) :
    ((truncatedTrial μ N : DomainLimitationSpace) : ℕ → ℝ) n
      = ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n := by
  rw [truncatedTrial_apply, geometricTrial_apply,
    truncatedTrialSequence_eq_raw (lt_of_lt_of_le hn hKN), rawTrialSequence]

end Section9
end DavisKahan1970
end TauCeti
