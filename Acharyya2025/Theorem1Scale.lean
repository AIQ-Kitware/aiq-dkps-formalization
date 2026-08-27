/-
Theorem 1 of Acharyya et al. (2025) is false as printed.

The theorem asserts, with no hypothesis on the scale of the population responses, that

  P[ |Bhat_ii' - B_ii'| < eps  for all i, i' ]  >=  1 - 16 sum_i sum_j gamma_ij / (r m eps^2),

where gamma_ij is the trace of the covariance of the response distribution F_ij.

The two sides do not respond to the population scale in the same way.  `B` is built from the
*squares* of the dissimilarities, so a deviation of the sample response means enters the entries
of `Bhat - B` multiplied by the population scale; `gamma_ij` measures only the variability of the
responses and is untouched by translating the population means apart.  Pushing two models far
apart therefore makes the left side small while the right side stays fixed.

`prob_entrywiseClose_lt_paper_bound` is that counterexample, at `n = 2` models, `m = 1` query,
`p = 1`, and `r = 1` replicate, where the three competing dissimilarity normalisations coincide,
so the refutation does not depend on which one is meant.

This is the missing hypothesis the formalization had already surfaced: the compiled bridge
`Acharyya2025.Bridge.entrywise_close_to_cmds_entrywise_close_of_bounded` carries an entrywise
bound `R` on the dissimilarities, documented there as an assumption beyond the paper.  The
counterexample shows it cannot be dropped.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import Acharyya2024.Consistency
import Acharyya2025.Deterministic

open scoped BigOperators Topology
open MeasureTheory

namespace Acharyya2025.Theorem1Scale

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2024.Consistency (coinMeasure)

/-- The norm on a `1 x 1` response matrix is the absolute value of its single entry. -/
theorem norm_mat_one_one (x : Mat 1 1) : ‖x‖ = |x (0, 0)| := by
  rw [EuclideanSpace.norm_eq]
  simp [Fintype.sum_prod_type, Real.sqrt_sq_eq_abs]

/-- Integration against the fair two-point measure. -/
theorem integral_coinMeasure (f : Bool → Real) :
    ∫ ω, f ω ∂coinMeasure = (1 / 2) * f true + (1 / 2) * f false := by
  haveI hf1 : IsFiniteMeasure ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) true) :=
    ⟨by simp⟩
  haveI hf2 : IsFiniteMeasure ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) false) :=
    ⟨by simp⟩
  have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) true) :=
    Integrable.of_finite
  have h2 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (α := Bool) false) :=
    Integrable.of_finite
  rw [coinMeasure, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  norm_num

/-- The sample response means of the counterexample: model `0` answers `0`, model `1` answers
`20` plus or minus `1` on a fair coin. -/
noncomputable def Xbar : Bool → Fin 2 → Mat 1 1 :=
  fun ω i => if i = 1 then EuclideanSpace.single (0, 0) (if ω then (21 : Real) else 19) else 0

/-- Their population means: `0` and `20`. -/
noncomputable def μ : Fin 2 → Mat 1 1 :=
  fun i => if i = 1 then EuclideanSpace.single (0, 0) (20 : Real) else 0

/-- The response variabilities: model `1` has trace-covariance `1`, model `0` none. -/
noncomputable def γ : Fin 2 → Fin 1 → Real := fun i _ => if i = 1 then 1 else 0

theorem secondMoment_eq (i : Fin 2) :
    ∫ ω, ‖Xbar ω i - μ i‖ ^ 2 ∂coinMeasure = ∑ j, γ i j := by
  fin_cases i <;>
    simp [integral_coinMeasure, Xbar, μ, γ, norm_mat_one_one, EuclideanSpace.single_apply] <;>
      norm_num

/-- The doubly centred matrix of a two-point configuration, at the diagonal entry. -/
theorem classicalMDSMatrix_two (X : Fin 2 → Mat 1 1) :
    classicalMDSMatrix (responseDist X) 0 0 = ‖X 0 - X 1‖ ^ 2 / 4 := by
  simp only [classicalMDSMatrix, doubleCenter, rowMean, colMean, grandMean, responseDist,
    responseDistEntry, Fin.sum_univ_two]
  norm_num [norm_sub_rev (X 0) (X 1)]
  ring

/--
**Theorem 1 as printed is false.**

At `n = 2`, `m = 1`, `p = 1`, `r = 1` the printed bound claims the entrywise event has
probability at least `9/25`, while the event is empty.  The population means are `0` and `20`
and the response variability is `1`, so pushing the two models apart makes every sample value of
`Bhat_00` at least `9.75` away from `B_00 = 100`, at a tolerance of `5`.

Since `m = 1`, the `1/m`, `1/sqrt m` and unnormalized dissimilarity conventions agree here, so
the refutation is independent of which one the source intends.
-/
theorem prob_entrywiseClose_lt_paper_bound :
    coinMeasure {ω : Bool | ∀ i i' : Fin 2,
        |classicalMDSMatrix (responseDist (Xbar ω)) i i'
          - classicalMDSMatrix (responseDist μ) i i'| < (5 : Real)}
      < 1 - ENNReal.ofReal (16 * (∑ i, ∑ j, γ i j) / ((1 : Real) * 1 * 5 ^ 2)) := by
  have hXnorm : ∀ ω : Bool, ‖Xbar ω 0 - Xbar ω 1‖ = if ω then (21 : Real) else 19 := by
    intro ω
    cases ω <;> simp [Xbar, norm_mat_one_one, EuclideanSpace.single_apply] <;> norm_num
  have hμnorm : ‖μ 0 - μ 1‖ = (20 : Real) := by
    simp [μ, norm_mat_one_one, EuclideanSpace.single_apply]
  have hempty : {ω : Bool | ∀ i i' : Fin 2,
      |classicalMDSMatrix (responseDist (Xbar ω)) i i'
        - classicalMDSMatrix (responseDist μ) i i'| < (5 : Real)} = (∅ : Set Bool) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
    refine ⟨0, 0, ?_⟩
    rw [classicalMDSMatrix_two, classicalMDSMatrix_two, hXnorm, hμnorm]
    cases ω <;> norm_num
  rw [hempty, measure_empty]
  have hγ : (∑ i, ∑ j, γ i j) = (1 : Real) := by
    simp [γ, Fin.sum_univ_two, Fin.sum_univ_one]
  rw [hγ]
  norm_num

end Acharyya2025.Theorem1Scale
