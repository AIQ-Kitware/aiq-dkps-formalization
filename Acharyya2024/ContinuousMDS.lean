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
import TauCeti.Probability.StrongLaw

open scoped BigOperators Topology
open MeasureTheory Filter

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

/-- **Coercivity of the one-point raw stress.**  Far enough from a reference point, the term of
that single reference point already exceeds the whole stress at the point itself. -/
theorem lt_pointStress_of_norm_gt {n d : Nat} (z : Config n d) (c : Fin n → Real) (i₀ : Fin n)
    {w : Rvec d}
    (hw : ‖z i₀‖ + |c i₀| + Real.sqrt (pointStress z c (z i₀)) + 1 < ‖w‖) :
    pointStress z c (z i₀) < pointStress z c w := by
  classical
  set B : Real := pointStress z c (z i₀) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrt : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hstep : Real.sqrt B + 1 ≤ ‖w - z i₀‖ - c i₀ := by
    have h1 : ‖w‖ - ‖z i₀‖ ≤ ‖w - z i₀‖ := norm_sub_norm_le _ _
    have h2 : c i₀ ≤ |c i₀| := le_abs_self _
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

/--
**The one-point raw stress attains its minimum.**

It is continuous and coercive, so a minimizer over a large closed ball -- which exists by
compactness -- is a global minimizer.
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
    have := lt_pointStress_of_norm_gt z c i₀ (by rw [← hR]; exact hw)
    linarith

/-- A global minimizer of the one-point raw stress is bounded by the coercivity radius. -/
theorem norm_le_of_min_pointStress {n d : Nat} (z : Config n d) (c : Fin n → Real)
    (i₀ : Fin n) {v : Rvec d} (hv : ∀ w : Rvec d, pointStress z c v ≤ pointStress z c w) :
    ‖v‖ ≤ ‖z i₀‖ + |c i₀| + Real.sqrt (pointStress z c (z i₀)) + 1 := by
  by_contra hcon
  push Not at hcon
  have h1 := lt_pointStress_of_norm_gt z c i₀ hcon
  have h2 := hv (z i₀)
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

/-! ### Stability of the out-of-sample extension

This is the argmin step for the out-of-sample map, the analogue for a single new point of the
raw-stress stability the package proves for whole configurations.  If the reference
configuration and the target dissimilarities converge, and the limiting one-point stress has a
unique minimizer, then the out-of-sample positions converge to it.

The proof is compactness: the minimizers are bounded by the coercivity radius, which converges;
every subsequential limit minimizes the limiting stress, hence is *the* minimizer; and a bounded
sequence all of whose subsequential limits agree converges. -/

/-- The one-point raw stress is jointly continuous in the reference configuration, the target
dissimilarities and the point, along sequences. -/
theorem tendsto_pointStress {n d : Nat} {z : Nat → Config n d} {ψ : Config n d}
    {c : Nat → Fin n → Real} {c' : Fin n → Real} {v : Nat → Rvec d} {v' : Rvec d}
    (hz : ∀ i, Tendsto (fun u => z u i) atTop (𝓝 (ψ i)))
    (hc : ∀ i, Tendsto (fun u => c u i) atTop (𝓝 (c' i)))
    (hv : Tendsto v atTop (𝓝 v')) :
    Tendsto (fun u => pointStress (z u) (c u) (v u)) atTop (𝓝 (pointStress ψ c' v')) := by
  unfold pointStress
  refine tendsto_finset_sum _ fun i _ => ?_
  exact ((hv.sub (hz i)).norm.sub (hc i)).pow 2

/--
**Stability of the out-of-sample extension.**

If the reference configuration and the target dissimilarities converge, and the limiting
one-point stress has a unique minimizer `v'`, then the out-of-sample positions converge to `v'`.
-/
theorem tendsto_outOfSampleExtension {n d : Nat} (hn : 0 < n)
    {z : Nat → Config n d} {ψ : Config n d}
    {c : Nat → Fin n → Real} {c' : Fin n → Real} {v' : Rvec d}
    (hz : ∀ i, Tendsto (fun u => z u i) atTop (𝓝 (ψ i)))
    (hc : ∀ i, Tendsto (fun u => c u i) atTop (𝓝 (c' i)))
    (hmin : ∀ w : Rvec d, pointStress ψ c' v' ≤ pointStress ψ c' w)
    (huniq : ∀ w : Rvec d, (∀ w' : Rvec d, pointStress ψ c' w ≤ pointStress ψ c' w') → w = v') :
    Tendsto (fun u => outOfSampleExtension hn (z u) (c u)) atTop (𝓝 v') := by
  classical
  have hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i₀⟩ := hne
  set V : Nat → Rvec d := fun u => outOfSampleExtension hn (z u) (c u) with hV
  have hVmin : ∀ u, ∀ w : Rvec d, pointStress (z u) (c u) (V u) ≤ pointStress (z u) (c u) w :=
    fun u w => outOfSampleExtension_min hn (z u) (c u) w
  -- the coercivity radius converges, so the minimizers are bounded
  set Rseq : Nat → Real :=
    fun u => ‖z u i₀‖ + |c u i₀| + Real.sqrt (pointStress (z u) (c u) (z u i₀)) + 1 with hRseq
  have hRlim : Tendsto Rseq atTop
      (𝓝 (‖ψ i₀‖ + |c' i₀| + Real.sqrt (pointStress ψ c' (ψ i₀)) + 1)) := by
    have hstress : Tendsto (fun u => pointStress (z u) (c u) (z u i₀)) atTop
        (𝓝 (pointStress ψ c' (ψ i₀))) := tendsto_pointStress hz hc (hz i₀)
    exact (((hz i₀).norm.add (hc i₀).abs).add
      (Real.continuous_sqrt.continuousAt.tendsto.comp hstress)).add tendsto_const_nhds
  obtain ⟨Rb, hRb⟩ := (Metric.isBounded_range_of_tendsto _ hRlim).subset_closedBall 0
  have hVbound : ∀ u, ‖V u‖ ≤ Rb := by
    intro u
    refine le_trans (norm_le_of_min_pointStress (z u) (c u) i₀ (hVmin u)) ?_
    have := hRb (Set.mem_range_self u)
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  -- every subsequential limit minimizes the limiting stress, hence equals `v'`
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hmem : ∀ k, V (ns k) ∈ Metric.closedBall (0 : Rvec d) Rb := by
    intro k
    rw [mem_closedBall_zero_iff]
    exact hVbound (ns k)
  obtain ⟨L, -, ms, hmsmono, hms⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  refine ⟨ms, ?_⟩
  have hsub : Tendsto (fun k => ns (ms k)) atTop atTop :=
    hns.comp hmsmono.tendsto_atTop
  have hLmin : ∀ w : Rvec d, pointStress ψ c' L ≤ pointStress ψ c' w := by
    intro w
    have hlhs : Tendsto (fun k => pointStress (z (ns (ms k))) (c (ns (ms k))) (V (ns (ms k))))
        atTop (𝓝 (pointStress ψ c' L)) :=
      tendsto_pointStress (fun i => (hz i).comp hsub) (fun i => (hc i).comp hsub) hms
    have hrhs : Tendsto (fun k => pointStress (z (ns (ms k))) (c (ns (ms k))) w)
        atTop (𝓝 (pointStress ψ c' w)) :=
      tendsto_pointStress (fun i => (hz i).comp hsub) (fun i => (hc i).comp hsub)
        tendsto_const_nhds
    exact le_of_tendsto_of_tendsto hlhs hrhs
      (Filter.Eventually.of_forall fun k => hVmin (ns (ms k)) w)
  have hLeq : L = v' := huniq L hLmin
  rw [← hLeq]
  exact hms

/-! ### From pointwise convergence to the `L^p` conclusion

With the estimated embedding in hand, the passage from convergence at almost every pair of
models to the source's `L^p(P × P)` conclusion is dominated convergence, and nothing else.  The
double integral is an integral against the product measure, so no double average over a sample
appears and no law of large numbers is involved. -/

/-- The `L^p` pairwise-distance discrepancy is an integral against the product measure. -/
theorem lpPairDistErr_eq_integral_prod {M : Type*} [MeasurableSpace M] (d : Nat)
    (P : Measure M) [SFinite P] (p : Real) (ψ χ : M → Rvec d)
    (hint : Integrable
      (fun q : M × M => |‖ψ q.1 - ψ q.2‖ - ‖χ q.1 - χ q.2‖| ^ p) (P.prod P)) :
    lpPairDistErr d P p ψ χ
      = ∫ q, |‖ψ q.1 - ψ q.2‖ - ‖χ q.1 - χ q.2‖| ^ p ∂(P.prod P) := by
  rw [lpPairDistErr, integral_prod _ hint]

/--
**Lemma 2's conclusion from convergence at almost every pair.**

If the pairwise-distance discrepancy of the estimated embeddings tends to zero at `P × P`-almost
every pair of models, and is dominated by a fixed integrable envelope, then the source's
`L^p(P × P)` discrepancy tends to zero.

This is the whole distance from a pointwise statement to the printed conclusion: dominated
convergence on the product measure.  In particular no law of large numbers enters, because the
integral is against `P × P` and not against an empirical measure.
-/
theorem tendsto_lpPairDistErr_of_ae_tendsto {M : Type*} [MeasurableSpace M] (d : Nat)
    (P : Measure M) [IsProbabilityMeasure P] (p : Real)
    (Ψ : Nat → M → Rvec d) (χ : M → Rvec d)
    (G : M × M → Real) (hG : Integrable G (P.prod P))
    (hmeas : ∀ u, AEStronglyMeasurable
      (fun q : M × M => |‖Ψ u q.1 - Ψ u q.2‖ - ‖χ q.1 - χ q.2‖| ^ p) (P.prod P))
    (hdom : ∀ u, ∀ᵐ q ∂(P.prod P),
      ‖|‖Ψ u q.1 - Ψ u q.2‖ - ‖χ q.1 - χ q.2‖| ^ p‖ ≤ G q)
    (hae : ∀ᵐ q ∂(P.prod P), Tendsto
      (fun u => |‖Ψ u q.1 - Ψ u q.2‖ - ‖χ q.1 - χ q.2‖| ^ p) atTop (𝓝 0)) :
    Tendsto (fun u => lpPairDistErr d P p (Ψ u) χ) atTop (𝓝 0) := by
  have hint : ∀ u, Integrable
      (fun q : M × M => |‖Ψ u q.1 - Ψ u q.2‖ - ‖χ q.1 - χ q.2‖| ^ p) (P.prod P) :=
    fun u => Integrable.mono' hG (hmeas u) (hdom u)
  have hlim := tendsto_integral_of_dominated_convergence G hmeas hG hdom hae
  rw [integral_zero] at hlim
  refine hlim.congr fun u => ?_
  exact (lpPairDistErr_eq_integral_prod d P p (Ψ u) χ (hint u)).symm

/-! ### Lemma 2's conclusion for a fixed reference sample

Assembling the pieces: the out-of-sample positions converge at every model
(`tendsto_outOfSampleExtension`), so the pairwise-distance discrepancy converges at every pair,
and dominated convergence (`tendsto_lpPairDistErr_of_ae_tendsto`) turns that into the source's
`L^p(P × P)` conclusion.

What this proves is the conclusion's shape, with the population embedding taken relative to a
*fixed* reference sample.  The source's `mds` is the continuous-MDS map, which is the limit of
these as the reference collection grows; identifying the two is the residual. -/

/--
**Lemma 2's `L^p` conclusion, against the population embedding of a fixed reference sample.**

`z u` are the estimated reference configurations and `ψ` their limit; `Δhat u` the estimated
dissimilarities and `Δ` their limit.  The uniqueness hypothesis is the identifiability premise
the argmin step needs, of the same kind as `RawStress.UniquePairProfile`; the uniform bound is
what a bounded dissimilarity function on a compact model space supplies.
-/
theorem tendsto_lpPairDistErr_frameEmbedding {M : Type*} [MeasurableSpace M]
    {d n : Nat} (hn : 0 < n) (P : Measure M) [IsProbabilityMeasure P]
    {p : Real} (hp : 0 < p)
    (Δhat : Nat → M → M → Real) (Δ : M → M → Real) (φ : Fin n → M)
    (z : Nat → Config n d) (ψ : Config n d)
    (hz : ∀ i, Tendsto (fun u => z u i) atTop (𝓝 (ψ i)))
    (hΔ : ∀ x i, Tendsto (fun u => Δhat u x (φ i)) atTop (𝓝 (Δ x (φ i))))
    (huniq : ∀ x : M, ∀ w : Rvec d,
      (∀ w' : Rvec d, pointStress ψ (fun i => Δ x (φ i)) w
        ≤ pointStress ψ (fun i => Δ x (φ i)) w') →
      w = frameEmbedding d n hn Δ φ ψ x)
    {C : Real} (hC : 0 ≤ C)
    (hbdd : ∀ u, ∀ x y : M,
      |‖frameEmbedding d n hn (Δhat u) φ (z u) x - frameEmbedding d n hn (Δhat u) φ (z u) y‖
        - ‖frameEmbedding d n hn Δ φ ψ x - frameEmbedding d n hn Δ φ ψ y‖| ≤ C)
    (hmeas : ∀ u, AEStronglyMeasurable
      (fun q : M × M =>
        |‖frameEmbedding d n hn (Δhat u) φ (z u) q.1
            - frameEmbedding d n hn (Δhat u) φ (z u) q.2‖
          - ‖frameEmbedding d n hn Δ φ ψ q.1 - frameEmbedding d n hn Δ φ ψ q.2‖| ^ p)
      (P.prod P)) :
    Tendsto (fun u => lpPairDistErr d P p
      (frameEmbedding d n hn (Δhat u) φ (z u)) (frameEmbedding d n hn Δ φ ψ))
      atTop (𝓝 0) := by
  classical
  -- the out-of-sample position converges at every model
  have hpt : ∀ x : M, Tendsto (fun u => frameEmbedding d n hn (Δhat u) φ (z u) x) atTop
      (𝓝 (frameEmbedding d n hn Δ φ ψ x)) := by
    intro x
    have hmin : ∀ w : Rvec d,
        pointStress ψ (fun i => Δ x (φ i)) (frameEmbedding d n hn Δ φ ψ x)
          ≤ pointStress ψ (fun i => Δ x (φ i)) w :=
      fun w => frameEmbedding_min d n hn Δ φ ψ x w
    exact tendsto_outOfSampleExtension hn hz (fun i => hΔ x i) hmin (huniq x)
  -- hence the pairwise-distance discrepancy converges at every pair
  have hae : ∀ᵐ q ∂(P.prod P), Tendsto
      (fun u => |‖frameEmbedding d n hn (Δhat u) φ (z u) q.1
          - frameEmbedding d n hn (Δhat u) φ (z u) q.2‖
        - ‖frameEmbedding d n hn Δ φ ψ q.1 - frameEmbedding d n hn Δ φ ψ q.2‖| ^ p)
      atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun q => ?_
    have hnorm : Tendsto
        (fun u => ‖frameEmbedding d n hn (Δhat u) φ (z u) q.1
            - frameEmbedding d n hn (Δhat u) φ (z u) q.2‖) atTop
        (𝓝 ‖frameEmbedding d n hn Δ φ ψ q.1 - frameEmbedding d n hn Δ φ ψ q.2‖) :=
      ((hpt q.1).sub (hpt q.2)).norm
    have hsub : Tendsto
        (fun u => |‖frameEmbedding d n hn (Δhat u) φ (z u) q.1
            - frameEmbedding d n hn (Δhat u) φ (z u) q.2‖
          - ‖frameEmbedding d n hn Δ φ ψ q.1 - frameEmbedding d n hn Δ φ ψ q.2‖|)
        atTop (𝓝 0) := by
      have h0 := (hnorm.sub (tendsto_const_nhds
        (x := ‖frameEmbedding d n hn Δ φ ψ q.1 - frameEmbedding d n hn Δ φ ψ q.2‖))).abs
      simpa using h0
    have hrpow : Tendsto (fun t : Real => t ^ p) (𝓝[≥] (0 : Real)) (𝓝 0) := by
      have h : ContinuousWithinAt (fun t : Real => t ^ p) (Set.Ici (0 : Real)) 0 :=
        (Real.continuousAt_rpow_const (0 : Real) p (Or.inr hp.le)).continuousWithinAt
      have h2 : Tendsto (fun t : Real => t ^ p) (𝓝[≥] (0 : Real)) (𝓝 ((0 : Real) ^ p)) := h
      rwa [Real.zero_rpow hp.ne'] at h2
    refine hrpow.comp (tendsto_nhdsWithin_iff.mpr ⟨hsub, ?_⟩)
    exact Filter.Eventually.of_forall fun u => Set.mem_Ici.mpr (abs_nonneg _)
  -- dominated convergence finishes
  refine tendsto_lpPairDistErr_of_ae_tendsto d P p _ _ (fun _ => C ^ p)
    (integrable_const _) hmeas (fun u => Filter.Eventually.of_forall fun q => ?_) hae
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
  exact Real.rpow_le_rpow (abs_nonneg _) (hbdd u q.1 q.2) hp.le

/-! ### The population one-point stress

`pointStress` places a model against a finite reference sample.  Its population counterpart
places a model against the whole model distribution, and is what the source's `mds` minimizes
pointwise.  Defining it, and proving its minimizer exists, gives the target of Lemma 2's
conclusion a definition at the population level.

Boundedness of the reference embedding and of the target dissimilarities is what a compact model
space with a continuous embedding supplies, and it is what makes the integral finite and the
functional continuous and coercive. -/

/-- **The population one-point stress**: the continuous analogue of `pointStress`, placing `v`
against the whole model distribution rather than a finite sample. -/
noncomputable def continuousPointStress {M : Type*} [MeasurableSpace M] (d : Nat)
    (P : Measure M) (χ : M → Rvec d) (c : M → Real) (v : Rvec d) : Real :=
  ∫ m, (‖v - χ m‖ - c m) ^ 2 ∂P

variable {M : Type*} [MeasurableSpace M]

/-- Under a bounded reference embedding and bounded target dissimilarities, the integrand is
uniformly bounded on any ball of positions. -/
theorem continuousPointStress_integrand_le {d : Nat} {χ : M → Rvec d} {c : M → Real} {K : Real}
    (hχ : ∀ m, ‖χ m‖ ≤ K) (hc : ∀ m, |c m| ≤ K) (v : Rvec d) (m : M) :
    |(‖v - χ m‖ - c m) ^ 2| ≤ (‖v‖ + 2 * K) ^ 2 := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc m)
  have h1 : ‖v - χ m‖ ≤ ‖v‖ + K :=
    le_trans (norm_sub_le _ _) (by linarith [hχ m])
  have h2 : |‖v - χ m‖ - c m| ≤ ‖v‖ + 2 * K := by
    have := abs_le.mp (hc m)
    have hnn : 0 ≤ ‖v - χ m‖ := norm_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have hnn : 0 ≤ ‖v‖ + 2 * K := by positivity
  rw [abs_of_nonneg (sq_nonneg _), ← abs_of_nonneg hnn]
  calc (‖v - χ m‖ - c m) ^ 2 = |‖v - χ m‖ - c m| ^ 2 := (sq_abs _).symm
    _ ≤ (‖v‖ + 2 * K) ^ 2 := by
        refine pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = |‖v‖ + 2 * K| ^ 2 := by rw [abs_of_nonneg hnn]

/-- The population one-point stress is continuous in the position. -/
theorem continuous_continuousPointStress {d : Nat} (P : Measure M) [IsFiniteMeasure P]
    {χ : M → Rvec d} {c : M → Real} {K : Real}
    (hχmeas : AEStronglyMeasurable χ P) (hcmeas : AEStronglyMeasurable c P)
    (hχ : ∀ m, ‖χ m‖ ≤ K) (hc : ∀ m, |c m| ≤ K) :
    Continuous (continuousPointStress d P χ c) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  refine continuousAt_of_dominated (bound := fun _ => (‖v₀‖ + 1 + 2 * K) ^ 2) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun v =>
      (((aestronglyMeasurable_const.sub hχmeas).norm.sub hcmeas).pow 2)
  · filter_upwards [Metric.ball_mem_nhds v₀ one_pos] with v hv
    refine Filter.Eventually.of_forall fun m => ?_
    have hvle : ‖v‖ ≤ ‖v₀‖ + 1 := by
      have := (mem_ball_iff_norm.mp hv).le
      calc ‖v‖ = ‖v - v₀ + v₀‖ := by abel_nf
        _ ≤ ‖v - v₀‖ + ‖v₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖v₀‖ := by linarith
        _ = ‖v₀‖ + 1 := by ring
    have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc m)
    refine le_trans ?_ (pow_le_pow_left₀ (by linarith [norm_nonneg v])
      (by linarith : ‖v‖ + 2 * K ≤ ‖v₀‖ + 1 + 2 * K) 2)
    simpa [Real.norm_eq_abs] using continuousPointStress_integrand_le hχ hc v m
  · refine Filter.Eventually.of_forall fun m => ?_
    exact (((continuous_id.sub continuous_const).norm.sub continuous_const).pow 2).continuousAt

/-- The integrand of the population one-point stress is integrable under the boundedness
hypotheses. -/
theorem integrable_continuousPointStress_integrand {d : Nat} (P : Measure M) [IsFiniteMeasure P]
    {χ : M → Rvec d} {c : M → Real} {K : Real}
    (hχmeas : AEStronglyMeasurable χ P) (hcmeas : AEStronglyMeasurable c P)
    (hχ : ∀ m, ‖χ m‖ ≤ K) (hc : ∀ m, |c m| ≤ K) (v : Rvec d) :
    Integrable (fun m => (‖v - χ m‖ - c m) ^ 2) P := by
  refine Integrable.mono' (integrable_const ((‖v‖ + 2 * K) ^ 2))
    (((aestronglyMeasurable_const.sub hχmeas).norm.sub hcmeas).pow 2)
    (Filter.Eventually.of_forall fun m => ?_)
  simpa [Real.norm_eq_abs] using continuousPointStress_integrand_le hχ hc v m

/--
**The population one-point stress attains its minimum.**

Continuous by `continuous_continuousPointStress` and coercive: far from the reference the
integrand is bounded below by `(‖v‖ - 2K)²`, which eventually exceeds the value at the origin.
So the target of Lemma 2's conclusion is a genuine minimizer, not a posited object.
-/
theorem exists_min_continuousPointStress {d : Nat} (P : Measure M) [IsProbabilityMeasure P]
    {χ : M → Rvec d} {c : M → Real} {K : Real}
    (hχmeas : AEStronglyMeasurable χ P) (hcmeas : AEStronglyMeasurable c P)
    (hχ : ∀ m, ‖χ m‖ ≤ K) (hc : ∀ m, |c m| ≤ K) :
    ∃ v : Rvec d, ∀ w : Rvec d,
      continuousPointStress d P χ c v ≤ continuousPointStress d P χ c w := by
  classical
  have hne : Nonempty M := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 : P Set.univ = 0 := by
      have : (Set.univ : Set M) = ∅ := Set.univ_eq_empty_iff.mpr hcon
      rw [this, measure_empty]
    rw [measure_univ] at h1
    exact one_ne_zero h1
  obtain ⟨m₀⟩ := hne
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc m₀)
  set R : Real := 4 * K + 1 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  -- the value at the origin
  have hzero : continuousPointStress d P χ c 0 ≤ (2 * K) ^ 2 := by
    rw [continuousPointStress]
    have hle : ∀ m, (‖(0 : Rvec d) - χ m‖ - c m) ^ 2 ≤ (2 * K) ^ 2 := by
      intro m
      have h1 : ‖(0 : Rvec d) - χ m‖ ≤ K := by simpa using hχ m
      have h2 := abs_le.mp (hc m)
      have hnn : 0 ≤ ‖(0 : Rvec d) - χ m‖ := norm_nonneg _
      have habs : |‖(0 : Rvec d) - χ m‖ - c m| ≤ 2 * K := by
        rw [abs_le]; constructor <;> linarith
      calc (‖(0 : Rvec d) - χ m‖ - c m) ^ 2
          = |‖(0 : Rvec d) - χ m‖ - c m| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc ∫ m, (‖(0 : Rvec d) - χ m‖ - c m) ^ 2 ∂P
        ≤ ∫ _m, (2 * K) ^ 2 ∂P :=
          integral_mono (integrable_continuousPointStress_integrand P hχmeas hcmeas hχ hc 0)
            (integrable_const _) hle
      _ = (2 * K) ^ 2 := by simp
  -- coercivity
  have hcoer : ∀ w : Rvec d, R < ‖w‖ → (2 * K) ^ 2 < continuousPointStress d P χ c w := by
    intro w hw
    have hge : ∀ m, (2 * K + 1) ^ 2 ≤ (‖w - χ m‖ - c m) ^ 2 := by
      intro m
      have h1 : ‖w‖ - ‖χ m‖ ≤ ‖w - χ m‖ := norm_sub_norm_le _ _
      have h2 := abs_le.mp (hc m)
      have h3 : 2 * K + 1 ≤ ‖w - χ m‖ - c m := by
        rw [hR] at hw
        linarith [hχ m]
      exact pow_le_pow_left₀ (by linarith) h3 2
    have hint : ∫ _m, (2 * K + 1) ^ 2 ∂P ≤ continuousPointStress d P χ c w := by
      rw [continuousPointStress]
      exact integral_mono (integrable_const _)
        (integrable_continuousPointStress_integrand P hχmeas hcmeas hχ hc w) hge
    have hval : ∫ _m : M, (2 * K + 1) ^ 2 ∂P = (2 * K + 1) ^ 2 := by simp
    rw [hval] at hint
    nlinarith [hint, hK]
  -- compactness on the ball, then globality
  obtain ⟨v, hv_mem, hv_min⟩ :=
    (isCompact_closedBall (0 : Rvec d) R).exists_isMinOn
      ⟨0, by simp [Metric.mem_closedBall, hRpos.le]⟩
      (continuous_continuousPointStress P hχmeas hcmeas hχ hc).continuousOn
  refine ⟨v, fun w => ?_⟩
  have hv0 : continuousPointStress d P χ c v ≤ continuousPointStress d P χ c 0 :=
    hv_min (by simp [Metric.mem_closedBall, hRpos.le])
  by_cases hw : ‖w‖ ≤ R
  · exact hv_min (by simpa [Metric.mem_closedBall] using hw)
  · push Not at hw
    have := hcoer w hw
    linarith

/-! ### Equi-Lipschitz bounds for the one-point stresses

Pointwise convergence of objectives is not enough to move minimizers; locally uniform
convergence is.  For these stresses the gap is closed by an equi-Lipschitz estimate: on any ball
of positions, each summand is Lipschitz with a constant depending only on the ball and on the
bound for the reference embedding and the dissimilarities, not on the sample.  Pointwise
convergence on a countable dense set then upgrades to locally uniform convergence. -/

/-- One summand of the one-point stress is Lipschitz in the position, with a constant depending
only on the ball and the bounds. -/
theorem abs_sub_pointStress_term_le {d : Nat} (zi : Rvec d) (ci : Real) (v w : Rvec d)
    {R K : Real} (hv : ‖v‖ ≤ R) (hw : ‖w‖ ≤ R) (hz : ‖zi‖ ≤ K) (hc : |ci| ≤ K) :
    |(‖v - zi‖ - ci) ^ 2 - (‖w - zi‖ - ci) ^ 2| ≤ 2 * (R + 2 * K) * ‖v - w‖ := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hc
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hv
  set a : Real := ‖v - zi‖ - ci with ha
  set b : Real := ‖w - zi‖ - ci with hb
  have hdiff : |a - b| ≤ ‖v - w‖ := by
    have h1 : a - b = ‖v - zi‖ - ‖w - zi‖ := by rw [ha, hb]; ring
    rw [h1]
    have h2 : |‖v - zi‖ - ‖w - zi‖| ≤ ‖(v - zi) - (w - zi)‖ := abs_norm_sub_norm_le _ _
    have h3 : (v - zi) - (w - zi) = v - w := by abel
    rwa [h3] at h2
  have habs : ∀ u : Rvec d, ‖u‖ ≤ R → |‖u - zi‖ - ci| ≤ R + 2 * K := by
    intro u hu
    have h1 : ‖u - zi‖ ≤ R + K := le_trans (norm_sub_le _ _) (by linarith)
    have h2 := abs_le.mp hc
    have hnn : 0 ≤ ‖u - zi‖ := norm_nonneg _
    rw [abs_le]; constructor <;> linarith
  have hsum : |a + b| ≤ 2 * (R + 2 * K) := by
    have h1 := habs v hv
    have h2 := habs w hw
    calc |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ ≤ (R + 2 * K) + (R + 2 * K) := add_le_add h1 h2
      _ = 2 * (R + 2 * K) := by ring
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [hfac, abs_mul]
  have hnn : (0 : Real) ≤ ‖v - w‖ := norm_nonneg _
  have hnn2 : (0 : Real) ≤ 2 * (R + 2 * K) := by linarith
  calc |a - b| * |a + b| ≤ ‖v - w‖ * (2 * (R + 2 * K)) :=
        mul_le_mul hdiff hsum (abs_nonneg _) hnn
    _ = 2 * (R + 2 * K) * ‖v - w‖ := by ring

/-- The averaged one-point stress is Lipschitz on any ball, with a constant independent of the
sample size. -/
theorem abs_sub_pointStress_le {n d : Nat} (z : Config n d) (c : Fin n → Real)
    (v w : Rvec d) {R K : Real} (hv : ‖v‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hz : ∀ i, ‖z i‖ ≤ K) (hc : ∀ i, |c i| ≤ K) :
    |pointStress z c v - pointStress z c w| ≤ (n : Real) * (2 * (R + 2 * K)) * ‖v - w‖ := by
  unfold pointStress
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, ((‖v - z i‖ - c i) ^ 2 - (‖w - z i‖ - c i) ^ 2)|
      ≤ ∑ i, |(‖v - z i‖ - c i) ^ 2 - (‖w - z i‖ - c i) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * (R + 2 * K) * ‖v - w‖ :=
        Finset.sum_le_sum fun i _ =>
          abs_sub_pointStress_term_le (z i) (c i) v w hv hw (hz i) (hc i)
    _ = (n : Real) * (2 * (R + 2 * K)) * ‖v - w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The argmin step for a growing reference collection

`tendsto_outOfSampleExtension` moves minimizers when the objectives converge because the
reference sample is *fixed* and only its configuration moves.  When the reference collection
grows the objectives are different functions on every stage, and pointwise convergence alone
does not move minimizers.  What does is pointwise convergence together with an equi-Lipschitz
bound on balls -- exactly what `abs_sub_pointStress_le` provides for these stresses.

This is the deterministic half of the remaining identification.  The probabilistic half is the
strong law, which supplies the pointwise convergence. -/

/--
**Minimizers converge under pointwise convergence and an equi-Lipschitz bound.**

`G u` are the objectives, `g` their pointwise limit, `V u` a minimizer of `G u`, and `v'` the
unique minimizer of `g`.  The equi-Lipschitz hypothesis is what makes the value at a moving
point converge, which pointwise convergence alone does not give.
-/
theorem tendsto_argmin_of_tendsto_of_equiLipschitz {d : Nat}
    {G : Nat → Rvec d → Real} {g : Rvec d → Real} {V : Nat → Rvec d} {v' : Rvec d}
    (hlip : ∀ R : Real, ∃ L : Real, 0 ≤ L ∧ ∀ u : Nat, ∀ v w : Rvec d,
      ‖v‖ ≤ R → ‖w‖ ≤ R → |G u v - G u w| ≤ L * ‖v - w‖)
    (hptw : ∀ v : Rvec d, Tendsto (fun u => G u v) atTop (𝓝 (g v)))
    (hV : ∀ u : Nat, ∀ w : Rvec d, G u (V u) ≤ G u w)
    {Rb : Real} (hbdd : ∀ u : Nat, ‖V u‖ ≤ Rb)
    (huniq : ∀ w : Rvec d, (∀ w' : Rvec d, g w ≤ g w') → w = v') :
    Tendsto V atTop (𝓝 v') := by
  classical
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hmem : ∀ k, V (ns k) ∈ Metric.closedBall (0 : Rvec d) Rb := by
    intro k
    rw [mem_closedBall_zero_iff]
    exact hbdd (ns k)
  obtain ⟨L, -, ms, hmsmono, hms⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  refine ⟨ms, ?_⟩
  have hsub : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hmsmono.tendsto_atTop
  -- the limit point is in the ball, so a single Lipschitz constant covers the whole tail
  have hLb : ‖L‖ ≤ Rb :=
    le_of_tendsto hms.norm (Filter.Eventually.of_forall fun k => hbdd (ns (ms k)))
  obtain ⟨C, hC0, hCle⟩ := hlip Rb
  -- values at the moving minimizers converge to the value at the limit
  have hvals : Tendsto (fun k => G (ns (ms k)) (V (ns (ms k)))) atTop (𝓝 (g L)) := by
    have hgap : Tendsto (fun k => G (ns (ms k)) (V (ns (ms k))) - G (ns (ms k)) L)
        atTop (𝓝 0) := by
      have hbound : ∀ k, ‖G (ns (ms k)) (V (ns (ms k))) - G (ns (ms k)) L‖
          ≤ C * ‖V (ns (ms k)) - L‖ := by
        intro k
        rw [Real.norm_eq_abs]
        exact hCle (ns (ms k)) (V (ns (ms k))) L (hbdd (ns (ms k))) hLb
      have hd : Tendsto (fun k => C * ‖V (ns (ms k)) - L‖) atTop (𝓝 0) := by
        have h0 : Tendsto (fun k => ‖V (ns (ms k)) - L‖) atTop (𝓝 0) := by
          simpa using (hms.sub (tendsto_const_nhds (x := L))).norm
        simpa using h0.const_mul C
      exact squeeze_zero_norm hbound hd
    have hbase : Tendsto (fun k => G (ns (ms k)) L) atTop (𝓝 (g L)) := (hptw L).comp hsub
    simpa using hgap.add hbase
  -- so the limit point minimizes `g`
  have hLmin : ∀ w : Rvec d, g L ≤ g w := by
    intro w
    exact le_of_tendsto_of_tendsto hvals ((hptw w).comp hsub)
      (Filter.Eventually.of_forall fun k => hV (ns (ms k)) w)
  rw [← huniq L hLmin]
  exact hms

/-! ### The probabilistic input: the strong law for the averaged one-point stress

The averaged one-point stress against an iid reference sample is an average of a bounded
measurable function of one coordinate, so the strong law applies directly.  This is the last
ingredient the argmin step needs. -/

/--
**The averaged one-point stress converges to its population counterpart.**

For an iid reference sample, and at each fixed position, the averaged one-point stress against
the sample converges almost surely to the population one-point stress.  This is the strong law
applied to the summand, which is bounded and measurable, hence integrable.
-/
theorem ae_tendsto_averaged_pointStress {d : Nat} (P : Measure M) [IsProbabilityMeasure P]
    {χ : M → Rvec d} {c : M → Real} {K : Real}
    (hχ : Measurable χ) (hc : Measurable c)
    (hχb : ∀ m, ‖χ m‖ ≤ K) (hcb : ∀ m, |c m| ≤ K) (v : Rvec d) :
    ∀ᵐ φ ∂(Measure.infinitePi fun _ : Nat => P),
      Tendsto (fun n : Nat => (n : Real)⁻¹ *
        pointStress (fun i : Fin n => χ (φ i)) (fun i : Fin n => c (φ i)) v) atTop
        (𝓝 (continuousPointStress d P χ c v)) := by
  classical
  set f : M → Real := fun m => (‖v - χ m‖ - c m) ^ 2 with hf
  have hfmeas : Measurable f := by
    rw [hf]
    exact ((measurable_const.sub hχ).norm.sub hc).pow_const 2
  have hfint : Integrable f P :=
    integrable_continuousPointStress_integrand P hχ.aestronglyMeasurable
      hc.aestronglyMeasurable hχb hcb v
  have hslln := TauCeti.Probability.strong_law_ae_infinitePi P hfmeas hfint
  filter_upwards [hslln] with φ hφ
  have hval : ∫ y, f y ∂P = continuousPointStress d P χ c v := rfl
  rw [hval] at hφ
  refine hφ.congr fun n => ?_
  rw [smul_eq_mul]
  congr 1
  unfold pointStress
  exact (Fin.sum_univ_eq_sum_range (fun i => (‖v - χ (φ i)‖ - c (φ i)) ^ 2) n).symm

/-- **Pointwise convergence spreads from a dense set under an equi-Lipschitz bound.**

The strong law gives convergence at each fixed position, but with a null set that depends on the
position, so only countably many positions can be handled at once.  Equi-Lipschitz bounds turn
convergence on a countable dense set into convergence everywhere, off a single null set. -/
theorem tendsto_of_dense_of_equiLipschitz {d : Nat}
    {G : Nat → Rvec d → Real} {g : Rvec d → Real} (hg : Continuous g)
    (hlip : ∀ R : Real, ∃ L : Real, 0 ≤ L ∧ ∀ u : Nat, ∀ v w : Rvec d,
      ‖v‖ ≤ R → ‖w‖ ≤ R → |G u v - G u w| ≤ L * ‖v - w‖)
    {D : Set (Rvec d)} (hD : Dense D)
    (hptw : ∀ v ∈ D, Tendsto (fun u => G u v) atTop (𝓝 (g v))) :
    ∀ v : Rvec d, Tendsto (fun u => G u v) atTop (𝓝 (g v)) := by
  intro v
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL0, hLle⟩ := hlip (‖v‖ + 1)
  -- a radius small enough for all three error terms
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    Metric.continuousAt_iff.mp hg.continuousAt (ε / 3) (by linarith)
  set δ : Real := min (min 1 δ₂) (ε / (3 * (L + 1))) with hδ
  have hδpos : 0 < δ := by
    refine lt_min (lt_min one_pos hδ₂pos) ?_
    have : (0 : Real) < 3 * (L + 1) := by linarith
    positivity
  obtain ⟨w, hwD, hw⟩ := Metric.mem_closure_iff.mp (hD v) δ hδpos
  have hvw : ‖v - w‖ < δ := by rwa [← dist_eq_norm]
  have hwnorm : ‖w‖ ≤ ‖v‖ + 1 := by
    have h1 : ‖w‖ ≤ ‖v‖ + ‖v - w‖ := by
      calc ‖w‖ = ‖v - (v - w)‖ := by abel_nf
        _ ≤ ‖v‖ + ‖v - w‖ := norm_sub_le _ _
    have h2 : ‖v - w‖ < 1 := lt_of_lt_of_le hvw (le_trans (min_le_left _ _) (min_le_left _ _))
    linarith
  have hgw : |g w - g v| < ε / 3 := by
    have h2 : dist v w < δ₂ := lt_of_lt_of_le hw (le_trans (min_le_left _ _) (min_le_right _ _))
    have := hδ₂ (by rwa [dist_comm] at h2)
    rwa [Real.dist_eq] at this
  have hlipw : ∀ u : Nat, |G u v - G u w| < ε / 3 := by
    intro u
    have h1 := hLle u v w (by linarith) hwnorm
    have h2 : ‖v - w‖ ≤ ε / (3 * (L + 1)) := le_of_lt (lt_of_lt_of_le hvw (min_le_right _ _))
    have h3 : L * ‖v - w‖ ≤ L * (ε / (3 * (L + 1))) :=
      mul_le_mul_of_nonneg_left h2 hL0
    have h4 : L * (ε / (3 * (L + 1))) < ε / 3 := by
      have hden : (0 : Real) < 3 * (L + 1) := by linarith
      have hkey : L * ε * 3 < ε * (3 * (L + 1)) := by nlinarith [hε, hL0]
      calc L * (ε / (3 * (L + 1))) = (L * ε) / (3 * (L + 1)) := by ring
        _ < ε / 3 := by
            rw [div_lt_div_iff₀ hden (by norm_num : (0 : Real) < 3)]
            linarith [hkey]
    linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hptw w hwD) (ε / 3) (by linarith)
  refine ⟨N, fun u hu => ?_⟩
  have h1 := hlipw u
  have h2 := hN u hu
  rw [Real.dist_eq] at h2 ⊢
  calc |G u v - g v| = |(G u v - G u w) + (G u w - g w) + (g w - g v)| := by ring_nf
    _ ≤ |(G u v - G u w) + (G u w - g w)| + |g w - g v| := abs_add_le _ _
    _ ≤ |G u v - G u w| + |G u w - g w| + |g w - g v| := by
        have := abs_add_le (G u v - G u w) (G u w - g w)
        linarith
    _ < ε := by linarith

/-- A minimizer of the one-point stress against a bounded reference is bounded by `4K`, with a
constant independent of the sample size.  This is what makes the argmin step work for a growing
reference collection, where the coercivity radius of `norm_le_of_min_pointStress` would grow. -/
theorem norm_min_pointStress_le_of_bounded {n d : Nat} (hn : 0 < n) (z : Config n d)
    (c : Fin n → Real) {K : Real} (hz : ∀ i, ‖z i‖ ≤ K) (hc : ∀ i, |c i| ≤ K)
    {v : Rvec d} (hv : ∀ w : Rvec d, pointStress z c v ≤ pointStress z c w) :
    ‖v‖ ≤ 4 * K := by
  classical
  haveI hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc (Classical.arbitrary (Fin n)))
  by_contra hcon
  push Not at hcon
  -- at `v` every term exceeds `(2K)²`
  have hbig : ∀ i : Fin n, (2 * K) ^ 2 < (‖v - z i‖ - c i) ^ 2 := by
    intro i
    have h1 : ‖v‖ - ‖z i‖ ≤ ‖v - z i‖ := norm_sub_norm_le _ _
    have h2 := abs_le.mp (hc i)
    have h3 : 2 * K < ‖v - z i‖ - c i := by linarith [hz i]
    have h4 : (0 : Real) ≤ 2 * K := by linarith
    exact pow_lt_pow_left₀ h3 h4 (by norm_num)
  -- at the origin every term is at most `(2K)²`
  have hsmall : ∀ i : Fin n, (‖(0 : Rvec d) - z i‖ - c i) ^ 2 ≤ (2 * K) ^ 2 := by
    intro i
    have h1 : ‖(0 : Rvec d) - z i‖ ≤ K := by simpa using hz i
    have h2 := abs_le.mp (hc i)
    have hnn : 0 ≤ ‖(0 : Rvec d) - z i‖ := norm_nonneg _
    have habs : |‖(0 : Rvec d) - z i‖ - c i| ≤ 2 * K := by
      rw [abs_le]; constructor <;> linarith
    calc (‖(0 : Rvec d) - z i‖ - c i) ^ 2
        = |‖(0 : Rvec d) - z i‖ - c i| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hlt : ∑ _i : Fin n, (2 * K) ^ 2 < pointStress z c v := by
    unfold pointStress
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hbig i
  have hle : pointStress z c (0 : Rvec d) ≤ ∑ _i : Fin n, (2 * K) ^ 2 := by
    unfold pointStress
    exact Finset.sum_le_sum fun i _ => hsmall i
  have := hv (0 : Rvec d)
  linarith

/-! ### The identification, assembled

Every ingredient is now in place, and this is the statement they were for: for an iid reference
sample, the out-of-sample position against the population embedding at the sampled models
converges almost surely to the minimizer of the population one-point stress.

That is the identification the source's `mds` needs, and each step is one of the theorems above:
the strong law at each position, spreading to all positions off a single null set by the
equi-Lipschitz bound, the sample-size-independent bound on the minimizers, and the argmin step
for a growing collection. -/

/--
**The out-of-sample position converges to the population minimizer.**

`χ` is the population embedding and `c` the target dissimilarities against it, both bounded and
measurable -- what a compact model space with a continuous embedding supplies.  `v'` is the
unique minimizer of the population one-point stress, which exists by
`exists_min_continuousPointStress`.
-/
theorem ae_tendsto_outOfSampleExtension_of_iid {d : Nat} (P : Measure M) [IsProbabilityMeasure P]
    {χ : M → Rvec d} {c : M → Real} {K : Real}
    (hχ : Measurable χ) (hc : Measurable c)
    (hχb : ∀ m, ‖χ m‖ ≤ K) (hcb : ∀ m, |c m| ≤ K)
    {v' : Rvec d}
    (huniq : ∀ w : Rvec d,
      (∀ w' : Rvec d, continuousPointStress d P χ c w ≤ continuousPointStress d P χ c w') →
      w = v') :
    ∀ᵐ φ ∂(Measure.infinitePi fun _ : Nat => P),
      Tendsto (fun n : Nat =>
        outOfSampleExtension (n := n + 1) n.succ_pos
          (fun i : Fin (n + 1) => χ (φ i)) (fun i : Fin (n + 1) => c (φ i)))
        atTop (𝓝 v') := by
  classical
  haveI hMne : Nonempty M := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 : P Set.univ = 0 := by
      have : (Set.univ : Set M) = ∅ := Set.univ_eq_empty_iff.mpr hcon
      rw [this, measure_empty]
    rw [measure_univ] at h1
    exact one_ne_zero h1
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hχb (Classical.arbitrary M))
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Rvec d)
  -- the strong law at every position of a countable dense set, off one null set
  have hall : ∀ᵐ φ ∂(Measure.infinitePi fun _ : Nat => P), ∀ v ∈ D,
      Tendsto (fun n : Nat => ((n : Real))⁻¹ *
        pointStress (fun i : Fin n => χ (φ i)) (fun i : Fin n => c (φ i)) v) atTop
        (𝓝 (continuousPointStress d P χ c v)) := by
    rw [ae_ball_iff hDcount]
    intro v _
    exact ae_tendsto_averaged_pointStress P hχ hc hχb hcb v
  filter_upwards [hall] with φ hφ
  -- the shifted objectives, normalized so the Lipschitz constant does not grow
  set G : Nat → Rvec d → Real := fun n v => (((n : Real) + 1))⁻¹ *
    pointStress (fun i : Fin (n + 1) => χ (φ i)) (fun i : Fin (n + 1) => c (φ i)) v with hG
  have hshift : Tendsto (fun n : Nat => n + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hptwD : ∀ v ∈ D, Tendsto (fun n : Nat => G n v) atTop
      (𝓝 (continuousPointStress d P χ c v)) := by
    intro v hv
    have := (hφ v hv).comp hshift
    refine this.congr fun n => ?_
    rw [hG]
    norm_num
  -- an equi-Lipschitz bound, uniform in the sample size
  have hlip : ∀ R : Real, ∃ L : Real, 0 ≤ L ∧ ∀ n : Nat, ∀ v w : Rvec d,
      ‖v‖ ≤ R → ‖w‖ ≤ R → |G n v - G n w| ≤ L * ‖v - w‖ := by
    intro R
    refine ⟨2 * (max R 0 + 2 * K), by positivity, fun n v w hv hw => ?_⟩
    have hR : ‖v‖ ≤ max R 0 := le_trans hv (le_max_left _ _)
    have hR' : ‖w‖ ≤ max R 0 := le_trans hw (le_max_left _ _)
    have hbase := abs_sub_pointStress_le (fun i : Fin (n + 1) => χ (φ i))
      (fun i : Fin (n + 1) => c (φ i)) v w hR hR' (fun i => hχb _) (fun i => hcb _)
    have hpos : (0 : Real) < ((n : Real) + 1) := by positivity
    rw [hG]
    simp only [← mul_sub, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos))]
    calc ((n : Real) + 1)⁻¹ * |pointStress (fun i : Fin (n + 1) => χ (φ i))
            (fun i : Fin (n + 1) => c (φ i)) v
          - pointStress (fun i : Fin (n + 1) => χ (φ i)) (fun i : Fin (n + 1) => c (φ i)) w|
        ≤ ((n : Real) + 1)⁻¹ *
            (((n + 1 : Nat) : Real) * (2 * (max R 0 + 2 * K)) * ‖v - w‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hpos))
          simpa using hbase
      _ = 2 * (max R 0 + 2 * K) * ‖v - w‖ := by
          push_cast
          field_simp
  -- the minimizers, and their sample-size-independent bound
  set V : Nat → Rvec d := fun n =>
    outOfSampleExtension (n := n + 1) n.succ_pos
      (fun i : Fin (n + 1) => χ (φ i)) (fun i : Fin (n + 1) => c (φ i)) with hV
  have hVmin : ∀ n : Nat, ∀ w : Rvec d, G n (V n) ≤ G n w := by
    intro n w
    have hpos : (0 : Real) < ((n : Real) + 1) := by positivity
    have h := outOfSampleExtension_min (n := n + 1) n.succ_pos
      (fun i : Fin (n + 1) => χ (φ i)) (fun i : Fin (n + 1) => c (φ i)) w
    rw [hG]
    exact mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hpos))
  have hVbdd : ∀ n : Nat, ‖V n‖ ≤ 4 * K := by
    intro n
    exact norm_min_pointStress_le_of_bounded n.succ_pos _ _ (fun i => hχb _) (fun i => hcb _)
      (outOfSampleExtension_min (n := n + 1) n.succ_pos _ _)
  -- spread the convergence, then move the minimizers
  have hptw := tendsto_of_dense_of_equiLipschitz
    (continuous_continuousPointStress P hχ.aestronglyMeasurable hc.aestronglyMeasurable hχb hcb)
    hlip hDdense hptwD
  exact tendsto_argmin_of_tendsto_of_equiLipschitz hlip hptw hVmin hVbdd huniq

/--
**Every minimizer, not just a chosen one, eventually lies near the limit.**

`tendsto_argmin_of_tendsto_of_equiLipschitz` moves a given sequence of minimizers.  This is the
statement about the minimizer *set*: for every tolerance, eventually every minimizer of `G n` is
within it of `v'`.  Nothing is selected, which is what lets the conclusion be integrated against
-- the event it describes is measurable by `TauCeti.measurableSet_tendsto_isMinOn`.
-/
theorem eventually_forall_isMinOn_dist_lt {d : Nat}
    {G : Nat → Rvec d → Real} {g : Rvec d → Real} {v' : Rvec d}
    (hlip : ∀ R : Real, ∃ L : Real, 0 ≤ L ∧ ∀ u : Nat, ∀ v w : Rvec d,
      ‖v‖ ≤ R → ‖w‖ ≤ R → |G u v - G u w| ≤ L * ‖v - w‖)
    (hptw : ∀ v : Rvec d, Tendsto (fun u => G u v) atTop (𝓝 (g v)))
    {Rb : Real} (hbdd : ∀ u : Nat, ∀ v : Rvec d, (∀ w : Rvec d, G u v ≤ G u w) → ‖v‖ ≤ Rb)
    (huniq : ∀ w : Rvec d, (∀ w' : Rvec d, g w ≤ g w') → w = v') :
    ∀ ε > (0 : Real), ∀ᶠ u in atTop,
      ∀ v : Rvec d, (∀ w : Rvec d, G u v ≤ G u w) → ‖v - v'‖ < ε := by
  classical
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hbad : ∃ᶠ u in atTop, ∃ v : Rvec d,
      (∀ w : Rvec d, G u v ≤ G u w) ∧ ε ≤ ‖v - v'‖ := by
    refine hcon.mono fun u hu => ?_
    push Not at hu
    obtain ⟨v, hv, hd⟩ := hu
    exact ⟨v, hv, hd⟩
  obtain ⟨σ, hσmono, hσ⟩ := Filter.extraction_of_frequently_atTop hbad
  choose V hVmin hVfar using hσ
  -- the bad minimizers are bounded, so they subconverge
  have hmem : ∀ k, V k ∈ Metric.closedBall (0 : Rvec d) Rb := by
    intro k
    rw [mem_closedBall_zero_iff]
    exact hbdd (σ k) (V k) (hVmin k)
  obtain ⟨L, -, ms, hmsmono, hms⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  have hsub : Tendsto (fun k => σ (ms k)) atTop atTop :=
    (hσmono.comp hmsmono).tendsto_atTop
  have hLb : ‖L‖ ≤ Rb :=
    le_of_tendsto hms.norm (Filter.Eventually.of_forall fun k => hbdd _ _ (hVmin (ms k)))
  obtain ⟨C, hC0, hCle⟩ := hlip Rb
  -- the limit of the bad minimizers still minimizes `g`, so it is `v'`
  have hvals : Tendsto (fun k => G (σ (ms k)) (V (ms k))) atTop (𝓝 (g L)) := by
    have hbound : ∀ k, ‖G (σ (ms k)) (V (ms k)) - G (σ (ms k)) L‖ ≤ C * ‖V (ms k) - L‖ := by
      intro k
      rw [Real.norm_eq_abs]
      exact hCle (σ (ms k)) (V (ms k)) L (hbdd _ _ (hVmin (ms k))) hLb
    have hd : Tendsto (fun k => C * ‖V (ms k) - L‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun k => ‖V (ms k) - L‖) atTop (𝓝 0) := by
        simpa using (hms.sub (tendsto_const_nhds (x := L))).norm
      simpa using h0.const_mul C
    have hgap : Tendsto (fun k => G (σ (ms k)) (V (ms k)) - G (σ (ms k)) L) atTop (𝓝 0) :=
      squeeze_zero_norm hbound hd
    have hbase : Tendsto (fun k => G (σ (ms k)) L) atTop (𝓝 (g L)) := (hptw L).comp hsub
    simpa using hgap.add hbase
  have hLmin : ∀ w : Rvec d, g L ≤ g w := fun w =>
    le_of_tendsto_of_tendsto hvals ((hptw w).comp hsub)
      (Filter.Eventually.of_forall fun k => hVmin (ms k) w)
  have hLeq : L = v' := huniq L hLmin
  -- but they stay `ε` away from it
  have hfar : ε ≤ ‖L - v'‖ :=
    ge_of_tendsto ((hms.sub (tendsto_const_nhds (x := v'))).norm)
      (Filter.Eventually.of_forall fun k => hVfar (ms k))
  rw [hLeq, sub_self, norm_zero] at hfar
  linarith

end Acharyya2024.ContinuousMDS
