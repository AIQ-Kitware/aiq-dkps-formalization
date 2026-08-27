/-
Theorem 1 of Acharyya et al. (2024) names a fixed limiting configuration without a uniqueness
premise, and that is not provable.

The paper's Theorem 1 concludes that along some subsequence the pairwise distances of the
estimates converge in probability to those of *a* minimizer `psi` of the limiting dissimilarity
matrix.  The package's `rawStress_mds_stability` proves this with an extra hypothesis,
`RawStress.UniquePairProfile`, asserting that all minimizers share one pairwise-distance
profile.

This file shows the extra hypothesis is a repair rather than an added assumption: without it
the conclusion is false.  The obstruction is not exotic.  Raw stress depends on the
dissimilarity matrix only through its entries, so when that matrix is invariant under relabeling
the models -- the equilateral matrix on three objects is -- the minimizer set is closed under
relabeling too.  In one dimension three points cannot be mutually equidistant unless they
coincide, and coinciding is not optimal, so relabeling produces a genuinely different profile.
A selection that returns one labeling on half the sample points and the other on the rest then
satisfies every hypothesis of the printed theorem while no fixed profile serves both.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import Acharyya2024.Common
import Acharyya2024.RawStress
import Acharyya2024.Consistency

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Acharyya2024.ProfileNonuniqueness

open Acharyya2024.Consistency (coinMeasure coinMeasure_ge_half)

/-- The equilateral dissimilarity matrix on three objects: every distinct pair at distance one.
It is invariant under relabeling, which is the whole source of the obstruction. -/
noncomputable def equilateral : DisMat 3 := fun i j => if i = j then 0 else 1

/-- In one dimension the norm is the absolute difference of the single coordinate. -/
theorem norm_sub_one_dim (x y : Rvec 1) : ‖x - y‖ = |x 0 - y 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- A one-dimensional competitor: two objects at the same place, the third at distance one. -/
noncomputable def witness : Config 3 1 :=
  fun i => EuclideanSpace.single 0 (if i = 1 then (1 : Real) else 0)

theorem rawStress_witness : rawStress 3 1 equilateral witness = 2 := by
  simp only [rawStress, Fin.sum_univ_three, witness, norm_sub_one_dim, equilateral]
  norm_num [EuclideanSpace.single_apply, Fin.ext_iff]

/-- A configuration whose points all coincide has raw stress `6` against the equilateral
matrix, one for each of the six ordered distinct pairs. -/
theorem rawStress_of_dist_zero (z : Config 3 1) (h : ∀ i j, ‖z i - z j‖ = 0) :
    rawStress 3 1 equilateral z = 6 := by
  simp only [rawStress, Fin.sum_univ_three, h, equilateral]
  norm_num [Fin.ext_iff]

/-- Three points on a line cannot be mutually equidistant unless they coincide. -/
theorem dist_eq_zero_of_equidistant (z : Config 3 1)
    (h1 : ‖z 0 - z 1‖ = ‖z 0 - z 2‖) (h2 : ‖z 0 - z 1‖ = ‖z 1 - z 2‖) :
    ‖z 0 - z 1‖ = 0 := by
  rw [norm_sub_one_dim] at h1 h2 ⊢
  rw [norm_sub_one_dim] at h1 h2
  rcases abs_cases (z 0 0 - z 1 0) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases (z 0 0 - z 2 0) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases abs_cases (z 1 0 - z 2 0) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
        rw [e1] at h1 h2 ⊢ <;> rw [e2] at h1 <;> rw [e3] at h2 <;> linarith

/-- **A minimizer of the equilateral matrix has two distinct pairwise distances.** -/
theorem exists_distinct_pairDist (z : Config 3 1) (hz : z ∈ MDS 3 1 equilateral) :
    ‖z 0 - z 1‖ ≠ ‖z 0 - z 2‖ ∨ ‖z 0 - z 1‖ ≠ ‖z 1 - z 2‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hz01 : ‖z 0 - z 1‖ = 0 := dist_eq_zero_of_equidistant z h1 h2
  have hall : ∀ i j : Fin 3, ‖z i - z j‖ = 0 := by
    have h02 : ‖z 0 - z 2‖ = 0 := by rw [← h1]; exact hz01
    have h12 : ‖z 1 - z 2‖ = 0 := by rw [← h2]; exact hz01
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [norm_sub_rev (z 1) (z 0), norm_sub_rev (z 2) (z 0), norm_sub_rev (z 2) (z 1)]
  have h6 : rawStress 3 1 equilateral z = 6 := rawStress_of_dist_zero z hall
  have hle : rawStress 3 1 equilateral z ≤ rawStress 3 1 equilateral witness := hz witness
  rw [h6, rawStress_witness] at hle
  linarith

/-- Relabeling the models preserves the equilateral matrix. -/
theorem equilateral_comp_perm (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    equilateral (σ i) (σ j) = equilateral i j := by
  simp only [equilateral]
  by_cases h : i = j
  · simp [h]
  · have hσij : ¬ (σ i = σ j) := fun hc => h (σ.injective hc)
    simp [h, hσij]

/-- Relabeling the models preserves the raw stress, hence the minimizer set. -/
theorem mds_comp_perm (σ : Equiv.Perm (Fin 3)) (z : Config 3 1)
    (hz : z ∈ MDS 3 1 equilateral) : (fun i => z (σ i)) ∈ MDS 3 1 equilateral := by
  have hstress : ∀ w : Config 3 1,
      rawStress 3 1 equilateral (fun i => w (σ i)) = rawStress 3 1 equilateral w := by
    intro w
    simp only [rawStress]
    calc ∑ i : Fin 3, ∑ j : Fin 3, (‖w (σ i) - w (σ j)‖ - equilateral i j) ^ 2
        = ∑ i : Fin 3, ∑ j : Fin 3, (‖w (σ i) - w (σ j)‖ - equilateral (σ i) (σ j)) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [equilateral_comp_perm]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, (‖w i - w j‖ - equilateral i j) ^ 2 := by
          rw [← Equiv.sum_comp σ (fun i => ∑ j : Fin 3, (‖w i - w j‖ - equilateral i j) ^ 2)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Equiv.sum_comp σ (fun j => (‖w (σ i) - w j‖ - equilateral (σ i) j) ^ 2)]
  intro w
  rw [hstress z]
  exact hz w

/--
**Theorem 1's fixed limiting profile is not available without a uniqueness premise.**

There is a sequence of dissimilarity matrices converging in probability to the equilateral
matrix -- constantly equal to it, in fact -- and a selection of raw-stress minimizers of them,
for which no subsequence and no minimizer `psi` of the limit make the pairwise distances
converge in probability to those of `psi`.

Every hypothesis of the printed theorem holds, in its strongest form.  What fails is the
conclusion, because the minimizer set carries two distinct pairwise-distance profiles and the
selection returns each with probability one half.  `RawStress.UniquePairProfile` is exactly what
rules this out, so the package's extra hypothesis is a repair of the source and not an
assumption added to it.
-/
theorem no_fixed_limiting_profile :
    ∃ (Dseq : Nat → Bool → DisMat 3) (ψhat : Nat → Bool → Config 3 1),
      (∀ r ω, ψhat r ω ∈ MDS 3 1 (Dseq r ω)) ∧
      ConvergesInProbabilityZero coinMeasure
        (fun r ω => frobSub (Dseq r ω) equilateral) ∧
      ¬ ∃ u : Nat → Nat, Subseq u ∧ ∃ ψ : Config 3 1, ψ ∈ MDS 3 1 equilateral ∧
          ∀ i j : Fin 3, ConvergesInProbability coinMeasure
            (fun t ω => pairDistErr (ψhat (u t) ω) ψ i j) 0 := by
  classical
  set z : Config 3 1 := RawStress.mdsConfig (n := 3) (d := 1) equilateral with hzdef
  have hz : z ∈ MDS 3 1 equilateral := RawStress.mdsConfig_mem (n := 3) (d := 1) equilateral
  -- a relabeling with a different distance at the pair `(0, 1)`
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3),
      ‖z (σ 0) - z (σ 1)‖ ≠ ‖z 0 - z 1‖ := by
    rcases exists_distinct_pairDist z hz with h | h
    · exact ⟨Equiv.swap 1 2, by simpa [Equiv.swap_apply_of_ne_of_ne] using h.symm⟩
    · refine ⟨Equiv.swap 0 2, ?_⟩
      have : ‖z (Equiv.swap (0 : Fin 3) 2 0) - z (Equiv.swap (0 : Fin 3) 2 1)‖
          = ‖z 1 - z 2‖ := by
        simp [Equiv.swap_apply_of_ne_of_ne, norm_sub_rev (z 2) (z 1)]
      rw [this]
      exact fun hc => h hc.symm
  set z' : Config 3 1 := fun i => z (σ i) with hz'def
  have hz' : z' ∈ MDS 3 1 equilateral := mds_comp_perm σ z hz
  refine ⟨fun _ _ => equilateral, fun _ ω => if ω then z else z', ?_, ?_, ?_⟩
  · intro r ω; cases ω <;> simpa using ‹_›
  · intro ε hε
    have hset : ∀ _r : Nat,
        {ω : Bool | dist (frobSub equilateral equilateral) 0 > ε} = (∅ : Set Bool) := by
      intro _r
      ext ω
      simp [frobSub, frob, frobSq, not_lt.mpr hε.le]
    refine Filter.Tendsto.congr (fun r => ?_)
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (𝓝 0))
    rw [hset r, measure_empty]
  · rintro ⟨u, -, ψ, -, hconv⟩
    set d0 : Real := ‖z 0 - z 1‖ with hd0
    set d1 : Real := ‖z' 0 - z' 1‖ with hd1
    have hne : d1 ≠ d0 := hσ
    set ε : Real := |d1 - d0| / 3 with hεdef
    have hεpos : 0 < ε := by
      have hpos : 0 < |d1 - d0| := abs_pos.mpr (sub_ne_zero.mpr hne)
      rw [hεdef]
      linarith
    have hbad : ∀ t : Nat,
        true ∈ {ω : Bool | dist (pairDistErr (if ω then z else z') ψ 0 1) 0 > ε} ∨
        false ∈ {ω : Bool | dist (pairDistErr (if ω then z else z') ψ 0 1) 0 > ε} := by
      intro t
      by_contra hno
      push Not at hno
      obtain ⟨h1, h2⟩ := hno
      simp only [Set.mem_ofPred_eq, gt_iff_lt, not_lt, Real.dist_eq, sub_zero,
        abs_of_nonneg (abs_nonneg _), pairDistErr, pairDist] at h1 h2
      have e1 : |d0 - ‖ψ 0 - ψ 1‖| ≤ ε := by simpa [hd0] using h1
      have e2 : |d1 - ‖ψ 0 - ψ 1‖| ≤ ε := by simpa [hd1] using h2
      have : |d1 - d0| ≤ ε + ε := by
        calc |d1 - d0| = |(d1 - ‖ψ 0 - ψ 1‖) - (d0 - ‖ψ 0 - ψ 1‖)| := by ring_nf
          _ ≤ |d1 - ‖ψ 0 - ψ 1‖| + |d0 - ‖ψ 0 - ψ 1‖| := abs_sub _ _
          _ ≤ ε + ε := add_le_add e2 e1
      rw [hεdef] at this
      have hpos : 0 < |d1 - d0| := abs_pos.mpr (sub_ne_zero.mpr hne)
      linarith
    have hhalf : ∀ t : Nat, (1 / 2 : ENNReal) ≤ coinMeasure
        {ω : Bool | dist (pairDistErr (if ω then z else z') ψ 0 1) 0 > ε} :=
      fun t => coinMeasure_ge_half (hbad t)
    have hlim := hconv 0 1 ε hεpos
    have hle : (1 / 2 : ENNReal) ≤ 0 :=
      ge_of_tendsto hlim (Filter.Eventually.of_forall fun t => hhalf (u t))
    simp at hle

end Acharyya2024.ProfileNonuniqueness
