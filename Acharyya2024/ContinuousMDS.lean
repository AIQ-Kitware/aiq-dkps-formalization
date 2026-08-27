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
import Acharyya2024.RawStress
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

/-! ### The `L^p(P x P)` discrepancy of Lemma 2 and Theorem 5 -/

/--
The `L^p(P x P)` pairwise-distance discrepancy the source's Lemma 2 and Theorem 5 drive to
zero: the double integral of `| ‖psi m' - psi m''‖ - ‖chi m' - chi m''‖ |^p` against the model
distribution, where `chi` is the continuous-MDS embedding.
-/
noncomputable def lpPairDistErr (d : Nat) (P : Measure M) (p : Real)
    (ψ χ : M → Rvec d) : Real :=
  ∫ m', ∫ m'', |‖ψ m' - ψ m''‖ - ‖χ m' - χ m''‖| ^ p ∂P ∂P

/-- Against the empirical measure of a finite population, the `L^p` discrepancy is the average
of the pairwise errors. -/
theorem lpPairDistErr_empiricalPopulation
    {κ : Type*} [Fintype κ] [Nonempty κ] (d : Nat) {p : Real} (hp : 0 ≤ p)
    (φ : κ → M) (ψ χ : M → Rvec d) (hψ : Measurable ψ) (hχ : Measurable χ) :
    lpPairDistErr d (TauCeti.Probability.empiricalPopulation φ : Measure M) p ψ χ
      = ((Fintype.card κ : Real))⁻¹ * ((Fintype.card κ : Real))⁻¹ *
          ∑ i, ∑ j, |‖ψ (φ i) - ψ (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p := by
  classical
  have hinner : ∀ m' : M,
      ∫ m'', |‖ψ m' - ψ m''‖ - ‖χ m' - χ m''‖| ^ p
          ∂(TauCeti.Probability.empiricalPopulation φ : Measure M)
        = ((Fintype.card κ : Real))⁻¹ *
            ∑ j, |‖ψ m' - ψ (φ j)‖ - ‖χ m' - χ (φ j)‖| ^ p := by
    intro m'
    have hmeas : StronglyMeasurable
        fun m'' : M => |‖ψ m' - ψ m''‖ - ‖χ m' - χ m''‖| ^ p :=
      ((Real.continuous_rpow_const hp).measurable.comp
        (((measurable_const.sub hψ).norm.sub
          (measurable_const.sub hχ).norm).abs)).stronglyMeasurable
    rw [TauCeti.Probability.integral_empiricalPopulation hmeas, smul_eq_mul]
  rw [lpPairDistErr]
  simp_rw [hinner]
  have houter : StronglyMeasurable fun m' : M =>
      ((Fintype.card κ : Real))⁻¹ *
        ∑ j, |‖ψ m' - ψ (φ j)‖ - ‖χ m' - χ (φ j)‖| ^ p := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)).stronglyMeasurable
    exact (Real.continuous_rpow_const hp).measurable.comp
      (((hψ.sub measurable_const).norm.sub
        (hχ.sub measurable_const).norm).abs)
  rw [TauCeti.Probability.integral_empiricalPopulation houter, smul_eq_mul, ← Finset.mul_sum,
    ← mul_assoc]

/--
**Lemma 2 for the empirical model distribution.**

If every pairwise distance of the estimates converges in probability to the corresponding
distance of the continuous-MDS embedding, then the `L^p(P x P)` discrepancy converges in
probability to zero, for every `p >= 1` and against the empirical measure of the models.

Two differences from the printed lemma, both in the direction of strength: the conclusion holds
along the full sequence rather than along a subsequence, and it is uniform in `p`.  The
restriction is that `P` is the empirical measure of the sampled models rather than the
population law they are drawn from; lifting that is the remaining content of Lemma 2, which the
source attributes to the cited continuous-MDS literature.
-/
theorem tendsto_measure_lpPairDistErr_gt
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {κ : Type*} [Fintype κ] [Nonempty κ] {d : Nat} (p : Real) (hp : 1 ≤ p)
    (φ : κ → M) (ψ : Nat → Ω → M → Rvec d) (χ : M → Rvec d)
    (hψ : ∀ u ω, Measurable (ψ u ω)) (hχ : Measurable χ)
    (hconv : ∀ i j, ∀ δ > (0 : Real), Filter.Tendsto
      (fun u => Q {ω | δ < |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖|})
      Filter.atTop (𝓝 0))
    {ε : Real} (hε : 0 < ε) :
    Filter.Tendsto
      (fun u => Q {ω | ε < lpPairDistErr d
        (TauCeti.Probability.empiricalPopulation φ : Measure M) p (ψ u ω) χ})
      Filter.atTop (𝓝 0) := by
  classical
  set δ : Real := min 1 ε with hδdef
  have hδpos : 0 < δ := lt_min one_pos hε
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  have hcard : (0 : Real) < (Fintype.card κ : Real) := by
    exact_mod_cast Fintype.card_pos
  -- a uniform pairwise bound `δ` forces the averaged `p`-th power below `ε`
  have hsub : ∀ u, {ω | ε < lpPairDistErr d
        (TauCeti.Probability.empiricalPopulation φ : Measure M) p (ψ u ω) χ}
      ⊆ ⋃ q : κ × κ,
          {ω | δ < |‖ψ u ω (φ q.1) - ψ u ω (φ q.2)‖ - ‖χ (φ q.1) - χ (φ q.2)‖|} := by
    intro u ω hω
    by_contra hno
    simp only [Set.mem_iUnion, not_exists, Set.mem_ofPred_eq, not_lt] at hno
    have hterm : ∀ i j : κ,
        |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p ≤ ε := by
      intro i j
      have h1 : |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p ≤ δ ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) (hno (i, j)) (by linarith)
      have h2 : δ ^ p ≤ δ ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_ge hδpos hδ1 hp
      rw [Real.rpow_one] at h2
      linarith
    have hsum : ∑ i : κ, ∑ j : κ,
        |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p
        ≤ (Fintype.card κ : Real) * ((Fintype.card κ : Real) * ε) := by
      calc ∑ i : κ, ∑ j : κ,
              |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p
          ≤ ∑ _i : κ, ((Fintype.card κ : Real) * ε) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc ∑ j : κ, |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p
                ≤ ∑ _j : κ, ε := Finset.sum_le_sum fun j _ => hterm i j
              _ = (Fintype.card κ : Real) * ε := by
                  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = (Fintype.card κ : Real) * ((Fintype.card κ : Real) * ε) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Set.mem_ofPred_eq,
      lpPairDistErr_empiricalPopulation d (by linarith : (0:Real) ≤ p) φ (ψ u ω) χ
        (hψ u ω) hχ] at hω
    have hfin : ((Fintype.card κ : Real))⁻¹ * ((Fintype.card κ : Real))⁻¹ *
        ∑ i : κ, ∑ j : κ,
          |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p ≤ ε := by
      have hpos : (0 : Real) < ((Fintype.card κ : Real))⁻¹ * ((Fintype.card κ : Real))⁻¹ := by
        positivity
      calc ((Fintype.card κ : Real))⁻¹ * ((Fintype.card κ : Real))⁻¹ *
            ∑ i : κ, ∑ j : κ,
              |‖ψ u ω (φ i) - ψ u ω (φ j)‖ - ‖χ (φ i) - χ (φ j)‖| ^ p
          ≤ ((Fintype.card κ : Real))⁻¹ * ((Fintype.card κ : Real))⁻¹ *
              ((Fintype.card κ : Real) * ((Fintype.card κ : Real) * ε)) := by
            exact mul_le_mul_of_nonneg_left hsum hpos.le
        _ = ε := by field_simp
    linarith
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (g := fun _ : Nat => (0 : ENNReal))
    (h := fun u => ∑ q : κ × κ,
      Q {ω | δ < |‖ψ u ω (φ q.1) - ψ u ω (φ q.2)‖ - ‖χ (φ q.1) - χ (φ q.2)‖|}) ?_
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun u => ?_)
  · have := tendsto_finset_sum (Finset.univ : Finset (κ × κ))
      (fun q _ => hconv q.1 q.2 δ hδpos)
    simpa using this
  · calc Q {ω | ε < lpPairDistErr d
            (TauCeti.Probability.empiricalPopulation φ : Measure M) p (ψ u ω) χ}
        ≤ Q (⋃ q : κ × κ,
            {ω | δ < |‖ψ u ω (φ q.1) - ψ u ω (φ q.2)‖ - ‖χ (φ q.1) - χ (φ q.2)‖|}) :=
          measure_mono (hsub u)
      _ ≤ ∑' q : κ × κ,
            Q {ω | δ < |‖ψ u ω (φ q.1) - ψ u ω (φ q.2)‖ - ‖χ (φ q.1) - χ (φ q.2)‖|} :=
          measure_iUnion_le _
      _ = ∑ q : κ × κ,
            Q {ω | δ < |‖ψ u ω (φ q.1) - ψ u ω (φ q.2)‖ - ‖χ (φ q.1) - χ (φ q.2)‖|} :=
          tsum_fintype _

/-! ### The out-of-sample estimated embedding

Lemma 2 and Theorem 5 integrate `‖psihat_1 - psihat_2‖` against `P × P`, so the estimate has to
be defined at arbitrary models and not only at the sampled ones.  Acharyya 2024 leaves this
implicit in writing `psihat_1, psihat_2` under an integral over the model distribution; Quench
2026 states the map explicitly as `Psihat_Q`.  Without it the population conclusion cannot even
be written down, which is why it is fixed here.

`estimatedEmbedding` below is the augment-one-at-a-time construction: put the model into the
reference collection and read off its coordinate in a raw-stress minimizer of the enlarged
matrix.  That is the right object when there is a *single* target model, which is the situation
the downstream augmented pipelines are in.  It is **not** the map Lemma 2 and Theorem 5 need,
because each model gets its own minimizer and hence its own frame, so `‖Psihat x - Psihat y‖`
would compare coordinates in two unrelated frames.  `frameEmbedding`, further down, is the map
those results need. -/

/--
**The estimated embedding as a map on the whole model space**: augment `x` into the reference
sample `φ` and read its coordinate off the canonical raw-stress minimizer of the enlarged
dissimilarity matrix.
-/
noncomputable def estimatedEmbedding {M : Type*} (d n : Nat) (Δ : M → M → Real)
    (φ : Fin n → M) (x : M) : Rvec d :=
  RawStress.mdsConfig (n := n + 1) (d := d)
    (fun i j => Δ (Fin.snoc (α := fun _ => M) φ x i) (Fin.snoc (α := fun _ => M) φ x j)) (Fin.last n)

/-- The augmented configuration behind `estimatedEmbedding` is a raw-stress minimizer of the
augmented dissimilarity matrix, so the definition is not vacuous. -/
theorem estimatedEmbedding_mem_mds {M : Type*} (d n : Nat) (Δ : M → M → Real)
    (φ : Fin n → M) (x : M) :
    RawStress.mdsConfig (n := n + 1) (d := d)
      (fun i j => Δ (Fin.snoc (α := fun _ => M) φ x i) (Fin.snoc (α := fun _ => M) φ x j))
      ∈ MDS (n + 1) d (fun i j => Δ (Fin.snoc (α := fun _ => M) φ x i) (Fin.snoc (α := fun _ => M) φ x j)) :=
  RawStress.mdsConfig_mem _

/-- `estimatedEmbedding` is the last coordinate of that minimizer. -/
theorem estimatedEmbedding_eq {M : Type*} (d n : Nat) (Δ : M → M → Real)
    (φ : Fin n → M) (x : M) :
    estimatedEmbedding d n Δ φ x
      = RawStress.mdsConfig (n := n + 1) (d := d)
          (fun i j => Δ (Fin.snoc (α := fun _ => M) φ x i) (Fin.snoc (α := fun _ => M) φ x j)) (Fin.last n) :=
  rfl

/--
**The `L^p` discrepancy is invariant under a rigid motion of the estimate.**

Multidimensional scaling determines an embedding only up to a rigid motion, so a coordinatewise
error between two embeddings is not a well-posed quantity while this pairwise-distance
discrepancy is.  That is why the source states Lemma 2 and Theorem 5 in this form.
-/
theorem lpPairDistErr_rigidMotion_left {M : Type*} [MeasurableSpace M] (d : Nat)
    (P : Measure M) (p : Real) (ψ χ : M → Rvec d)
    (W : Rvec d ≃ₗᵢ[Real] Rvec d) (b : Rvec d) :
    lpPairDistErr d P p (fun x => W (ψ x) + b) χ = lpPairDistErr d P p ψ χ := by
  have key : ∀ x y : M, ‖(W (ψ x) + b) - (W (ψ y) + b)‖ = ‖ψ x - ψ y‖ := by
    intro x y
    have h : (W (ψ x) + b) - (W (ψ y) + b) = W (ψ x - ψ y) := by rw [map_sub]; abel
    rw [h, LinearIsometryEquiv.norm_map]
  unfold lpPairDistErr
  simp_rw [key]

/-- The same for a rigid motion of the target. -/
theorem lpPairDistErr_rigidMotion_right {M : Type*} [MeasurableSpace M] (d : Nat)
    (P : Measure M) (p : Real) (ψ χ : M → Rvec d)
    (W : Rvec d ≃ₗᵢ[Real] Rvec d) (b : Rvec d) :
    lpPairDistErr d P p ψ (fun x => W (χ x) + b) = lpPairDistErr d P p ψ χ := by
  have key : ∀ x y : M, ‖(W (χ x) + b) - (W (χ y) + b)‖ = ‖χ x - χ y‖ := by
    intro x y
    have h : (W (χ x) + b) - (W (χ y) + b) = W (χ x - χ y) := by rw [map_sub]; abel
    rw [h, LinearIsometryEquiv.norm_map]
  unfold lpPairDistErr
  simp_rw [key]

/-! ### A common frame: the out-of-sample extension

`estimatedEmbedding` above augments one model at a time, and that is not good enough for the
source's integral.  The minimizer of the matrix augmented by `x` and the minimizer of the matrix
augmented by `y` are each determined only up to their *own* rigid motion, so `‖Psihat x - Psihat
y‖` compares coordinates in two unrelated frames and is not a well-defined quantity.  The
integrand of Lemma 2 and Theorem 5 needs both models embedded in one frame.

The classical remedy, and the one the phrase "out-of-sample embedding" refers to, is to fix a
configuration for the reference sample and place each new model against it: `Psihat x` minimizes
the one-point raw stress of `x` against the fixed reference configuration.  Every model is then
placed in the same frame, and the pairwise distances the source integrates are well defined. -/

/-- **One-point raw stress**: how badly `v` matches the target dissimilarities `c` against a
fixed reference configuration `z`. -/
noncomputable def pointStress {n d : Nat} (z : Config n d) (c : Fin n → Real) (v : Rvec d) :
    Real :=
  ∑ i, (‖v - z i‖ - c i) ^ 2

theorem continuous_pointStress {n d : Nat} (z : Config n d) (c : Fin n → Real) :
    Continuous (pointStress z c) := by
  unfold pointStress
  exact continuous_finset_sum _ fun i _ =>
    (((continuous_id.sub continuous_const).norm.sub continuous_const).pow 2)

/--
**The one-point raw stress attains its minimum.**

It is continuous and coercive: far from the reference configuration the term of any single
reference point already exceeds the value at that point, so a minimizer over a large closed
ball -- which exists by compactness -- is a global minimizer.
-/
theorem exists_min_pointStress {n d : Nat} (hn : 0 < n) (z : Config n d) (c : Fin n → Real) :
    ∃ v : Rvec d, ∀ w : Rvec d, pointStress z c v ≤ pointStress z c w := by
  classical
  have hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i₀⟩ := hne
  set B : Real := pointStress z c (z i₀) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  set R : Real := ‖z i₀‖ + |c i₀| + Real.sqrt B + 1 with hR
  have hsqrt : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hzR : ‖z i₀‖ ≤ R := by
    rw [hR]; linarith [abs_nonneg (c i₀)]
  obtain ⟨v, hv_mem, hv_min⟩ :=
    (isCompact_closedBall (0 : Rvec d) R).exists_isMinOn
      ⟨z i₀, by simpa [Metric.mem_closedBall] using hzR⟩
      (continuous_pointStress z c).continuousOn
  refine ⟨v, fun w => ?_⟩
  have hvB : pointStress z c v ≤ B :=
    hv_min (by simpa [Metric.mem_closedBall] using hzR)
  by_cases hw : ‖w‖ ≤ R
  · exact hv_min (by simpa [Metric.mem_closedBall] using hw)
  · push Not at hw
    have hstep : Real.sqrt B + 1 ≤ ‖w - z i₀‖ - c i₀ := by
      have h1 : ‖w‖ - ‖z i₀‖ ≤ ‖w - z i₀‖ := norm_sub_norm_le _ _
      have h2 : c i₀ ≤ |c i₀| := le_abs_self _
      rw [hR] at hw
      linarith
    have hsq : B < (‖w - z i₀‖ - c i₀) ^ 2 := by
      have hpos : (0 : Real) ≤ Real.sqrt B + 1 := by linarith
      have hmono : (Real.sqrt B + 1) ^ 2 ≤ (‖w - z i₀‖ - c i₀) ^ 2 :=
        pow_le_pow_left₀ hpos hstep 2
      have hBsq : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
      nlinarith [hmono, hBsq, hsqrt]
    have hsingle : (‖w - z i₀‖ - c i₀) ^ 2 ≤ pointStress z c w :=
      Finset.single_le_sum (f := fun i => (‖w - z i‖ - c i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
    linarith

open Classical in
/-- **The out-of-sample extension**: the position minimizing the one-point raw stress of the
target dissimilarities `c` against the fixed reference configuration `z`. -/
noncomputable def outOfSampleExtension {n d : Nat} (hn : 0 < n) (z : Config n d)
    (c : Fin n → Real) : Rvec d :=
  (exists_min_pointStress hn z c).choose

theorem outOfSampleExtension_min {n d : Nat} (hn : 0 < n) (z : Config n d) (c : Fin n → Real)
    (w : Rvec d) :
    pointStress z c (outOfSampleExtension hn z c) ≤ pointStress z c w :=
  (exists_min_pointStress hn z c).choose_spec w

/--
**The estimated embedding in a common frame.**

Each model of the space is placed against one fixed configuration of the reference sample, so
the pairwise distances that Lemma 2 and Theorem 5 integrate are comparisons within a single
frame.  This is the map those results need; `estimatedEmbedding` is not, because it re-solves
the whole problem for each model and so produces a fresh frame each time.
-/
noncomputable def frameEmbedding {M : Type*} (d n : Nat) (hn : 0 < n) (Δ : M → M → Real)
    (φ : Fin n → M) (z : Config n d) (x : M) : Rvec d :=
  outOfSampleExtension hn z (fun i => Δ x (φ i))

/-- The frame embedding minimizes the one-point stress at every model. -/
theorem frameEmbedding_min {M : Type*} (d n : Nat) (hn : 0 < n) (Δ : M → M → Real)
    (φ : Fin n → M) (z : Config n d) (x : M) (w : Rvec d) :
    pointStress z (fun i => Δ x (φ i)) (frameEmbedding d n hn Δ φ z x)
      ≤ pointStress z (fun i => Δ x (φ i)) w :=
  outOfSampleExtension_min hn z _ w

/-- Moving the reference frame by a rigid motion moves the whole embedding by the same rigid
motion, so the pairwise distances it produces do not depend on the frame chosen. -/
theorem pointStress_rigidMotion {n d : Nat} (z : Config n d) (c : Fin n → Real)
    (W : Rvec d ≃ₗᵢ[Real] Rvec d) (b : Rvec d) (v : Rvec d) :
    pointStress (fun i => W (z i) + b) c (W v + b) = pointStress z c v := by
  unfold pointStress
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (W v + b) - (W (z i) + b) = W (v - z i) := by rw [map_sub]; abel
  rw [h, LinearIsometryEquiv.norm_map]

end Acharyya2024.ContinuousMDS
