/-
Continuous multidimensional scaling: the infinite-sample-size raw stress of
Acharyya et al. (2024), Section 2.

The paper's finite raw stress sums over a fixed model collection.  When the number of objects
is not finite the pairwise dissimilarities cannot be arranged in a matrix, so the source
replaces the sum by a double integral against a model distribution `P` on a compact metric
space `M`, and replaces the configuration by a Borel-measurable embedding `h : M → R^d`:

  sigma((Delta, P), h) = int int (‖h m' - h m''‖ - Delta m' m'')^2 P(dm') P(dm'').

`mds` is then an embedding minimizing this over all Borel-measurable embeddings.  Existence is
attributed to the cited continuous-MDS literature via Remark 3 (the Euclidean pseudometrics
form a closed and complete set), and is not reproved here; `ContinuousMDS` is the minimizer set,
which is the honest formal reading of "the embedding function that minimizes".

The reason to have the definition at all is that the growing-model results -- Lemma 2 and
Theorem 5 -- state their conclusions as `L^p(P x P)` convergence to `‖mds phi_1 - mds phi_2‖`,
which cannot even be written without it.

`continuousRawStress_empiricalPopulation` is the compatibility theorem: against the empirical
measure of a finite population, the continuous raw stress is the finite raw stress divided by
the square of the population size.  So the continuum definition is a genuine extension of the
finite one the rest of the package uses, not a parallel notion.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import Acharyya2024.Common
import TauCeti.Probability.Process.EmpiricalMeasure

open scoped BigOperators Topology
open MeasureTheory

namespace Acharyya2024.ContinuousMDS

variable {M : Type*} [MeasurableSpace M]

/--
**Continuous raw stress** (source, Section 2, infinite sample size).

`Delta` is the dissimilarity function on the model space, `P` the model distribution, and `h`
the embedding.  Following the Lean convention for `∫`, a non-integrable integrand contributes
zero; the definition is used only where the integrand is integrable, which on a compact model
space with a continuous embedding it is.
-/
noncomputable def continuousRawStress (d : Nat) (Δ : M → M → Real) (P : Measure M)
    (h : M → Rvec d) : Real :=
  ∫ m', ∫ m'', (‖h m' - h m''‖ - Δ m' m'') ^ 2 ∂P ∂P

/--
**The continuous-MDS embeddings**: the Borel-measurable embeddings minimizing continuous raw
stress among all Borel-measurable embeddings.  The source writes `mds` for a chosen element of
this set; as with the finite `MDS`, the minimizer is determined only up to a rigid motion, so
the set is the faithful object and a choice is a further step.
-/
def ContinuousMDS (d : Nat) (Δ : M → M → Real) (P : Measure M) : Set (M → Rvec d) :=
  {h | Measurable h ∧ ∀ h' : M → Rvec d, Measurable h' →
      continuousRawStress d Δ P h ≤ continuousRawStress d Δ P h'}

/--
**Assumption 2's dissimilarity function.** On a model space sitting inside a normed space, the
source takes `Delta (phi_i) (phi_i') = ‖phi_i - phi_i'‖`; this is the induced dissimilarity.
-/
noncomputable def ambientDissimilarity {q : Nat} (M' : Set (Rvec q)) : M' → M' → Real :=
  fun m m' => ‖(m : Rvec q) - (m' : Rvec q)‖

/--
**Compatibility with the finite raw stress.**

Against the empirical measure of a nonempty finite population, continuous raw stress is the
finite raw stress of the embedded population, divided by the square of the population size.
The continuum definition therefore extends the finite one rather than competing with it.
-/
theorem continuousRawStress_empiricalPopulation
    {κ : Type*} [Fintype κ] [Nonempty κ] (d : Nat)
    (φ : κ → M) (Δ : M → M → Real) (h : M → Rvec d)
    (hh : Measurable h) (hΔ : ∀ m, Measurable (Δ m))
    (hΔ' : ∀ m, Measurable fun m' => Δ m' m) :
    continuousRawStress d Δ
        (TauCeti.Probability.empiricalPopulation φ : Measure M) h
      = ((Fintype.card κ : Real))⁻¹ * ((Fintype.card κ : Real))⁻¹ *
          ∑ i, ∑ j, (‖h (φ i) - h (φ j)‖ - Δ (φ i) (φ j)) ^ 2 := by
  classical
  have hinner : ∀ m' : M,
      ∫ m'', (‖h m' - h m''‖ - Δ m' m'') ^ 2
          ∂(TauCeti.Probability.empiricalPopulation φ : Measure M)
        = ((Fintype.card κ : Real))⁻¹ * ∑ j, (‖h m' - h (φ j)‖ - Δ m' (φ j)) ^ 2 := by
    intro m'
    have hmeas : StronglyMeasurable fun m'' : M => (‖h m' - h m''‖ - Δ m' m'') ^ 2 :=
      (((measurable_const.sub hh).norm.sub (hΔ m')).pow_const 2).stronglyMeasurable
    rw [TauCeti.Probability.integral_empiricalPopulation hmeas, smul_eq_mul]
  rw [continuousRawStress]
  simp_rw [hinner]
  have houter : StronglyMeasurable fun m' : M =>
      ((Fintype.card κ : Real))⁻¹ * ∑ j, (‖h m' - h (φ j)‖ - Δ m' (φ j)) ^ 2 := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)).stronglyMeasurable
    exact (((hh.sub measurable_const).norm.sub (hΔ' (φ j))).pow_const 2)
  rw [TauCeti.Probability.integral_empiricalPopulation houter, smul_eq_mul, ← Finset.mul_sum,
    ← mul_assoc]

/--
The `Fin n` case, written against the package's `rawStress`: continuous raw stress against the
empirical measure of `n` models is `n^{-2}` times the finite raw stress of the embedded models
with the induced dissimilarity matrix.
-/
theorem continuousRawStress_empiricalPopulation_fin
    {n d : Nat} [NeZero n]
    (φ : Fin n → M) (Δ : M → M → Real) (h : M → Rvec d)
    (hh : Measurable h) (hΔ : ∀ m, Measurable (Δ m))
    (hΔ' : ∀ m, Measurable fun m' => Δ m' m) :
    continuousRawStress d Δ
        (TauCeti.Probability.empiricalPopulation φ : Measure M) h
      = ((n : Real))⁻¹ * ((n : Real))⁻¹ *
          rawStress n d (fun i j => Δ (φ i) (φ j)) (fun i => h (φ i)) := by
  have := continuousRawStress_empiricalPopulation (κ := Fin n) d φ Δ h hh hΔ hΔ'
  simpa [rawStress] using this

end Acharyya2024.ContinuousMDS
