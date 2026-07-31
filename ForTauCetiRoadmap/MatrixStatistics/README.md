# Roadmap: matrix spectra, concentration, and the toolkit of spectral statistics

Spectral methods in statistics — principal component analysis, spectral embedding,
classical multidimensional scaling — all run one pipeline: estimate a symmetric matrix
from samples, control the estimation error, push that control through eigenvalue and
eigenvector perturbation theory, and read off a stable embedding or a stable minimizer.
Mathlib has the deterministic linear algebra (the Hermitian spectral theorem,
`Matrix.rank`, `Matrix.PosSemidef`) and the probability spine (`ProbabilityTheory.variance`,
independence, the Bochner integral), but **not the estimation layer that connects them**:
nothing bounds a matrix's Euclidean operator norm by its entries, the sorted eigenvalue
indexing `Matrix.IsHermitian.eigenvalues₀` carries almost no theory, no spectral function
of a random matrix is known to be measurable, there is no sample-mean or sample-covariance
moment API, no matrix concentration statement, no Berge maximum theorem, and no
factorization realizing `Matrix.rank` as an inner dimension.

This roadmap builds that toolkit as four Parts that meet in the statistics. A positive
semidefinite matrix of rank at most `d` *is* the Gram matrix of `n` points in `𝕜^d`
(Part A — the multidimensional-scaling embedding step). A minimizer over a fixed compact
feasible set moves upper-hemicontinuously when the objective is perturbed (Part B —
argmin stability). Entrywise error on a symmetric matrix controls spectral error, and
spectral quantities of a *random* symmetric matrix are measurable, so probability
statements about them are well-posed (Part C). A sample covariance concentrates about the
population matrix — entrywise by Chebyshev and a union bound, hence spectrally through
Part C's entrywise-to-operator bridge (Part D). Composed with the spectral-subspace
perturbation roadmap, this is how a perturbation theorem becomes a statistical one: Part D
supplies "`Σ̂` is within `ε` of `Σ` with probability `1 − δ`", Part C makes the spectral
quantities of `Σ̂` measurable, Part B transfers the bound to minimizers of spectral
objectives, and Part A realizes the estimated Gram structure as an explicit embedding.

The goal is to **build the reusable theory of these objects**, not to race to the
composite. The bar for "done": a formalizer working from a spectral-methods paper finds
each object — rank factorizations, argmin correspondences, sorted eigenvalues, spectral
transforms, sample moments — defined at the pinned generality and equipped with its basic
API, so the concentration and stability theorems are consequences of a developed theory
rather than isolated endpoints. A PR that lands a headline bound but leaves the
surrounding object without its API is not yet what we want.

Suggested home: `TauCeti/LinearAlgebra/Matrix/`, `TauCeti/Topology/`,
`TauCeti/Analysis/Matrix/`, `TauCeti/Probability/Moments/`, with two supporting lemmas in
`TauCeti/MeasureTheory/`.

## Generality bar (decide these up front; do not silently specialize)

- **Matrices, deliberately.** Parts C and D are about concrete matrices with entrywise
  hypotheses, not abstract operators. This is not a lapse into coordinates: statistical
  data arrives as a matrix, entrywise, and the bounds a statistician can assume are
  entrywise bounds. The abstract operator theory lives in the FiniteDimensionalOperators
  roadmap; here we build the bridge from entries to spectra.
- **Scalar fields, pinned per part.** Rank factorization (Part A) over an arbitrary
  `Field`; the Gram/positive-semidefinite factorization over `RCLike`. The
  spectral–statistical chain (Parts C–D) is developed over `ℝ` for real symmetric
  matrices; the `RCLike` form of the two norm comparisons is an explicit Part C
  milestone, never a silent assumption.
- **Sorted eigenvalues: transport, never re-prove.** The decreasing indexing is
  Mathlib's `Matrix.IsHermitian.eigenvalues₀` (matrices) and
  `LinearMap.IsSymmetric.eigenvalues` (operators). Facts stated upstream for the
  matrix-indexed `eigenvalues` are *transported* along the defining index equivalence,
  not duplicated.
- **Inner dimensions are `Fin r`, not a subtype.** A caller who wants "at most `d` rows"
  gets `Fin d` directly, with the `≤`-relaxed form stated beside the exact-rank form, so
  no cardinality-equivalence transport is ever needed at a use site.
- **Fixed feasible set, said out loud.** Part B formalizes the *fixed-constraint* case of
  Berge's theorem: the compact `K` does not vary with the parameter. The
  parameter-varying constraint correspondence is a later Part B milestone, and every
  statement's docstring says which case it is.
- **Sequential methods, with their hypotheses visible.** Compactness is consumed through
  subsequences, so the standing hypotheses are `FirstCountableTopology` on the point
  space, `T2Space` exactly where Mathlib's `UpperHemicontinuousAt` needs the compact set
  closed, and `(𝓝 p₀).IsCountablyGenerated` on the parameter filter — not the
  compact-open topology.
- **No new predicates for one-line bounds.** Entrywise control is the hypothesis
  `∀ i j, |A i j| ≤ ε`, and operator control at `LinearMap` level is
  `∀ x, ‖T x‖ ≤ C * ‖x‖`, carried directly (as in Mathlib's `norm_cfc_le` style) — never
  wrapped in a named predicate or an ad-hoc sup norm.
- **Dimension constants are explicit and honest.** The entrywise-to-operator comparison
  carries the factor `n`, and the union bound carries `n²`. Neither is dimension-free and
  neither may be silently dropped: downstream bounds are *wrong*, not merely weak,
  without them. Where the constant is suboptimal by design (Part D), the statement says
  so.
- **Independence is pairwise; means are common.** Sample-moment identities assume
  pairwise independence and a common mean, never full mutual independence or identical
  distribution; the iid forms are corollaries. The scaled-sum identity is stated as
  `r⁻² · Σ` of individual errors (the independence-free shape), not `r⁻¹ ·` average.
- **Uncentered moments are the primitive.** Chebyshev is stated in raw second-moment form
  (no centering, no measurability of the variable itself); the sample covariance is the
  uncentered empirical second-moment matrix; centering is the scatter operator's job.
  `finiteMean` of the empty family is `0` by Mathlib's total-inverse convention, and the
  add-one mean identity is deliberately stated to hold *at* `n = 0`.

## What Mathlib already has (consume, and connect to)

- **Matrix linear algebra:** `Matrix.rank` with `rank_mul_le` and the column-space API;
  `Matrix.PosSemidef` with `posSemidef_conjTranspose_mul_self` and
  `rank_conjTranspose_mul_self`; `Matrix.IsHermitian.spectral_theorem`, `eigenvalues`,
  `eigenvectorUnitary`; `Matrix.toEuclideanLin` and the `ℓ²` operator-norm API
  (`Mathlib/Analysis/CStarAlgebra/Matrix.lean`).
- **Two gaps, stated precisely.** (1) There is **no entrywise-to-operator-norm
  comparison**: nothing bounds `‖toEuclideanLin A‖` by entrywise control of `A`. (2) The
  sorted indexing **`Matrix.IsHermitian.eigenvalues₀` carries almost no theory**: it is
  the primitive from which `eigenvalues` is *defined*, yet upstream it has only
  `eigenvalues₀_antitone` and the characteristic-polynomial identities, while the rank
  count (`rank_eq_card_non_zero_eigs`) and positivity (`PosSemidef.eigenvalues_nonneg`)
  are stated only for `eigenvalues`. Any "top-`k` eigenvalues" statement needs the sorted
  indexing, so both gaps are prerequisites for the statistics, not conveniences.
- **Topology:** `IsCompact.exists_isMinOn` (extreme value), `IsCompact.tendsto_subseq`
  (sequential compactness), `IsMinOn`, and the hemicontinuity *definitions*
  (`UpperHemicontinuousAt` with its sequential criterion `of_sequences`,
  `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`) — but no Berge theorem.
- **Spectral theory of operators:** `LinearMap.IsSymmetric.eigenvalues` /
  `eigenvectorBasis` (decreasingly sorted, on a finite-dimensional inner-product space)
  and `Matrix.isSymmetric_toEuclideanLin_iff` — the bridge on which Part C's
  `sortedEigenvalues` sits.
- **Probability:** `ProbabilityTheory.variance` with `IndepFun.variance_sum` (the scalar
  engine under the sample-mean identity); `meas_ge_le_variance_div_sq` (centered
  Chebyshev — the *uncentered* form is missing); `MemLp`, the Bochner integral,
  `MeasureTheory.TendstoInMeasure`. The covariance API
  (`Mathlib/Probability/Moments/CovarianceBilin.lean`) has no trace identity and no
  sample-mean lemmas.
- **Approximation:** Stone–Weierstrass (`polynomialFunctions.topologicalClosure`),
  `Polynomial.aeval` on matrices with `continuous_aeval`, and the Borel-space
  constructions — the ingredients of Part C's measurability argument.

Everything below is absent upstream. Each Part lists objects, the API to develop,
milestones, and acceptance examples.

---

## Part A — Rank factorization and positive-semidefinite Gram factorization

**Topic T21 of the candidate design** — the multidimensional-scaling embedding step.

**Objects.** Factorizations `M = L * R` through `Fin r`, and Gram factorizations
`B = Aᴴ * A` with a prescribed number of rows.

**API to develop.**
- The **exact rank factorization** `exists_eq_mul_rank`: every `M : Matrix m n 𝕜` over a
  field factors with inner dimension exactly `Fin M.rank` (`L` lists a basis of the
  column space, `R` the coordinates of each column); the zero-padded form
  `exists_eq_mul_of_rank_le` for any `r ≥ M.rank`.
- The **entrywise spectral expansion** `isHermitian_entry_eq_sum_eigenvalues`
  (`B i j = Σ_k λ_k · U i k · conj (U j k)`) and from it the **square Gram
  factorization** `PosSemidef.exists_eq_conjTranspose_mul_self` (`A = √D · Uᴴ`), then the
  **rank-controlled factor** `PosSemidef.exists_conjTranspose_mul_self_of_rank_le`
  (compress through the rank factorization, absorb the leftover Gram factor by a second
  square factorization).

**Milestone A1 — the two characterizations.** Both are iffs, and that is the point: the
easy converse (`rank (L * R) ≤ r`; `Aᴴ * A` is PSD of rank `≤ d`) is what makes them
usable as characterizations rather than constructions.

```lean
variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R

-- over `[RCLike 𝕜]`: a PSD matrix of rank ≤ d is the Gram matrix of n points in 𝕜^d
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {n d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A
```

**Milestone A2 — uniqueness up to the obvious action.** This is what a reviewer asks
immediately after seeing an existence iff, and it is the difference between a
*factorization theorem* and an existence lemma.  Two statements, and the hypotheses
differ in a way that is easy to get wrong:

```lean
-- rank factorization at the exact rank: unique up to a change of basis of the
-- intermediate space.  `r = M.rank` is essential -- at `r > M.rank` the factors are
-- not related by any invertible `g`, since `L` may have a redundant column.
theorem exists_unique_mul_rankFactorization {r : ℕ} (hr : M.rank = r)
    {L L' : Matrix m (Fin r) 𝕜} {R R' : Matrix (Fin r) n 𝕜}
    (h : M = L * R) (h' : M = L' * R') :
    ∃ g : GL (Fin r) 𝕜, L' = L * g ∧ R' = (g⁻¹ : Matrix (Fin r) (Fin r) 𝕜) * R

-- Gram factorization: unique up to a left unitary, *at a fixed factor size*.  The
-- unitary is on the `d` side, not the `n` side, and no rank hypothesis is needed --
-- which is why this one is not a corollary of the theorem above.
theorem exists_unitary_mul_of_conjTranspose_mul_self_eq {n d : ℕ}
    {A A' : Matrix (Fin d) (Fin n) 𝕜} (h : Aᴴ * A = A'ᴴ * A') :
    ∃ U ∈ Matrix.unitaryGroup (Fin d) 𝕜, A' = U * A
```

**Why they are one milestone and not two.**  They are the two uniqueness statements of the
same Part and they share a proof idea — both say the factor is determined by its Gram data
up to the symmetry group of the intermediate space — but the groups differ (`GL` versus
`unitaryGroup`) because the second remembers an inner product and the first does not.
Stating them together is what stops a reader assuming the general-field statement carries
a unitary.

**The MDS consumer fixes the second one's shape.**  Classical multidimensional scaling
recovers points from a Gram matrix; the recovered configuration is meaningful only up to a
rigid motion, and `A' = U * A` is exactly that indeterminacy.  A statement quantified the
other way — a unitary on the `n` side — would be false and would look plausible.

**Acceptance examples.** The Gram matrix of `n` explicit points in `𝕜^d` has rank `≤ d`;
a diagonal PSD matrix factors through its number of nonzero entries; the easy direction
recovers `rank_mul_le`.

## Part B — Berge's maximum theorem over a fixed compact feasible set

**Topic T22 of the candidate design** — argmin stability under objective perturbation.

**Objects.** For jointly continuous `g : P → X → ℝ` and a fixed nonempty compact
`K ⊆ X`: the argmin correspondence `p ↦ {x ∈ K | IsMinOn (g p) K x}` and the value
function `p ↦ ⨅ x : K, g p x`.

**API to develop.**
- The **engine**, and the actual content of the Part:
  `exists_subseq_tendsto_isMinOn_of_approxMinOn` — a sequence of *approximate* minimizers
  in a compact set (`F (z k) ≤ F x + ε x k` for `x ∈ K`, with `ε x k → 0`) has a
  subsequence converging to a genuine minimizer on `K`. This is the recovery half of the
  fundamental theorem of Γ-convergence; the global-comparison variant is
  `exists_subseq_tendsto_forall_le_of_approxMin`.
- The **sequential uniform-convergence step** `tendsto_eval_sub_of_isCompact`: along
  `p k → p₀`, the evaluation difference `g (p k) (x k) − g p₀ (x k)` vanishes for points
  `x k` staying in `K` — proved by the subsequence criterion, in exactly the form Berge
  consumes.

**Milestone B1 — Berge, in three forms** (three consumers want three shapes):
`tendsto_subseq_isMinOn_of_isMinOn` (closed-graph, sequential),
`upperHemicontinuousAt_isMinOn` (Mathlib's own predicate), and the uniform `ε`–`δ`
modulus `exists_modulus_isMinOn` / `exists_modulus_isMinOn_family`, whose `δ` depends
only on `(p₀, ε)` and so avoids measurable selection of minimizers. The family form
measures closeness by a finite family of continuous invariants vanishing on the diagonal
rather than by the ambient metric — the case where minimizers are determined only up to a
symmetry group.

**Milestone B2 — the value function.** `continuous_iInf_of_isCompact`: the value function
is continuous (the squeeze between a fixed minimizer of `g p₀` and the moving minimizers).

```lean
theorem upperHemicontinuousAt_isMinOn
    (hK : IsCompact K) (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :    -- X first-countable and Hausdorff
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀

theorem continuous_iInf_of_isCompact
    (hK : IsCompact K) (hKne : K.Nonempty) (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x)
```

**Milestone B3 — the classical theorem: a varying constraint correspondence.** This is the
classical statement's actual generality and the first thing a reviewer who knows Berge will
ask for.  **The fixed-constraint case above is a special case of it, not a step toward
it** — the engine that proves the fixed case does not generalize by adding a hypothesis,
because with `K` varying the approximate-minimizer sequence need not stay in one compact
set.

**Objects the milestone must add.**  A correspondence `Γ : P → Set X` together with the
two hemicontinuity properties, stated in whichever form Mathlib's own predicates support
(`UpperHemicontinuousAt` exists; the lower half needs checking against the current library
before a shape is pinned):

- `Γ` is **nonempty- and compact-valued** — both essential, and for opposite reasons: the
  first makes the value function finite, the second is what makes an argmin exist at all;
- `Γ` is **upper hemicontinuous** — this is what bounds the argmin set from outside and
  gives the closed-graph half;
- `Γ` is **lower hemicontinuous** — this is what the value function's *upper*
  semicontinuity needs, and it is the half the fixed-constraint development never had to
  prove, since a constant correspondence is trivially lower hemicontinuous.

**Statement.**  For jointly continuous `g : P → X → ℝ` and such a `Γ`: the value function
`v p = ⨅ x ∈ Γ p, g p x` is **continuous**, and the argmin correspondence
`M p = {x ∈ Γ p | IsMinOn (g p) (Γ p) x}` is **upper hemicontinuous with nonempty compact
values**.

```lean
theorem continuous_value_of_hemicontinuous
    {g : P → X → ℝ} (hg : Continuous fun q : P × X => g q.1 q.2)
    {Γ : P → Set X} (hne : ∀ p, (Γ p).Nonempty) (hcpt : ∀ p, IsCompact (Γ p))
    (huhc : UpperHemicontinuous Γ) (hlhc : LowerHemicontinuous Γ) :
    Continuous fun p => ⨅ x : Γ p, g p x
```

**The decomposition is the substance, and it should be stated in the roadmap because it is
what makes the milestone reviewable**: continuity of `v` splits into *lower*
semicontinuity from upper hemicontinuity of `Γ` and *upper* semicontinuity from lower
hemicontinuity of `Γ`, and each half is provable on its own.  A roadmap that asks for
"Berge's theorem" as a single target hides that it is two independent lemmas with opposite
hypotheses — and hides that half of it is already available from Milestone B2.

**Scope, honestly.**  Only the lower-hemicontinuity half and the correspondence vocabulary
are genuinely new; if Mathlib has since acquired either, this milestone shrinks to a
connection layer, and checking that is the first step rather than a formality.

**Acceptance examples.** `g p x = ‖x − p‖²` on a compact `K`: the argmin correspondence
is the metric projection and the modulus form is nontrivial exactly where the projection
is set-valued; a symmetric objective where minimizers form an orbit, exercising the
invariant-family modulus.

## Part C — Matrix spectra and spectral measurability

**Topic T19 of the candidate design.** Everything else in the operator-theory tree is
about abstract operators; this Part is about matrices, and about matrices whose entries
are random.

**Objects.** Real symmetric matrices as Euclidean operators (`Matrix.toEuclideanLin`,
symmetry via `Matrix.isSymmetric_toEuclideanLin_iff`); the decreasingly sorted spectrum
`sortedEigenvalues` (through `LinearMap.IsSymmetric.eigenvalues`); the spectral
`h`-transform `specTransform h hB = Σ_k h(λ_k) u_k u_kᵀ`.

**API to develop.**
- **Norm comparisons** (gap 1): `sum_norm_le_sqrt_card_mul_norm`
  (`ℓ¹ ≤ √card · ℓ²` on `EuclideanSpace`) and `norm_toEuclideanLin_le_of_entry_le`
  (`∀ i j, |A i j| ≤ ε` gives `‖toEuclideanLin A x‖ ≤ n · ε · ‖x‖`). The factor `n` is
  what a statistician pays and must stay visible.

  **The `RCLike` forms of both are open, and the reason they are not automatic is worth
  stating.**  The real statements are proved; the general ones read

  ```lean
  theorem sum_norm_le_sqrt_card_mul_norm {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
      (x : EuclideanSpace 𝕜 n) :
      ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card n) * ‖x‖

  theorem norm_toEuclideanLin_le_of_entry_le {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
      {A : Matrix (Fin n) (Fin n) 𝕜} {ε : ℝ} (hε : 0 ≤ ε)
      (hentry : ∀ i j, ‖A i j‖ ≤ ε) (x : EuclideanSpace 𝕜 (Fin n)) :
      ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖
  ```

  Cauchy–Schwarz and the triangle inequality are field-generic, so **no new mathematics is
  involved**; what the port costs is that the real proofs use `|·|` and `Real`-specific
  order lemmas where the general ones need `‖·‖` and `RCLike.re`/`norm_sum_le`.  Two
  consequences follow and both are decisions rather than bookkeeping: the entrywise bound
  is a bound on `‖A i j‖`, not on a real absolute value, so **complex Hermitian matrices
  are covered by the same statement**; and the two constants — `√card` and `n` — are
  unchanged by the generalization, which is the fact a reviewer will want asserted, since a
  complexification argument would have cost a factor of two.

  **The eigenvalue statements downstream stay real for now.**  `sortedEigenvalues` is built
  on `LinearMap.IsSymmetric.eigenvalues`, and generalizing the *spectral* layer is a
  different and larger question than generalizing these two norm inequalities.  Doing the
  norm half alone is worthwhile because it is what the operator-norm deviation event
  (Milestone D2) consumes, and it removes a `ℝ`-only hypothesis from the entry point of
  the Part rather than from its interior.
- **Entrywise eigenvalue perturbation**: Weyl's inequality (consumed from the
  FiniteDimensionalOperators roadmap, `abs_eigenvalue_sub_eigenvalue_le`) composed with
  the comparison gives `abs_sortedEigenvalues_sub_le_of_entry_le` — entrywise `ε`-close
  symmetric matrices have sorted eigenvalues within `n · ε` — and the a priori bound
  `abs_sortedEigenvalues_le_of_entry_le`. This composite is the whole reason the pair
  exists: entrywise control in, spectral conclusions out.
- **The sorted-indexing theory** (gap 2), transported and not re-proved:
  `IsHermitian.rank_eq_card_non_zero_eigenvalues₀`, `PosSemidef.eigenvalues₀_nonneg`,
  and the **vanishing tail** `PosSemidef.eigenvalues₀_eq_zero_of_rank_le` (positive
  semidefiniteness is essential, not convenient: a rank-one Hermitian matrix with a
  negative eigenvalue sorts it *last*).
- **Concentration consumers**: `one_sub_measure_compl_le` (probability of a complement,
  no measurability needed) and the `tendstoInMeasure_of_tendsto_measure_rate_lt_edist` /
  `_rate_lt_dist` / `_dist_le_rate` family, converting "with high probability the error
  is at most `rate i`" into `TendstoInMeasure`.

**Milestone C1 — measurability of the spectral transform.** For fixed continuous `h`,
`specTransform h` is measurable in the matrix (entrywise σ-algebra), with **no measurable
selection of an eigenbasis** — `B ↦ u_k(B)` is discontinuous at eigenvalue crossings.
Route: `specTransform h B` is the entrywise limit of matrix polynomials `p(B)`
(Stone–Weierstrass on a spectral interval bounded via
`abs_sortedEigenvalues_le_of_entry_le`), glued over a countable entrywise-bound cover by
the SpectralTheory roadmap's `measurable_of_iUnion_restrict`. This is the statement that
makes the statistical track well-posed: without it, "the top-`k` eigenspace of the sample
covariance" carries no measurability and no probability statement about it means
anything.

```lean
theorem abs_sortedEigenvalues_sub_le_of_entry_le {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, |Ahat i j - A i j| ≤ ε) (k : Fin n) :
    |sortedEigenvalues hAhat k - sortedEigenvalues hA k| ≤ (n : ℝ) * ε

theorem measurable_specTransform {Ω : Type*} [MeasurableSpace Ω]
    (h : ℝ → ℝ) (hh : Continuous h)
    {Bm : Ω → Matrix (Fin n) (Fin n) ℝ} (hBmeas : Measurable Bm)
    (hsym : ∀ ω, (Bm ω).IsHermitian) :
    Measurable fun ω => specTransform h (hsym ω)
```

**Acceptance examples.** `specTransform id hB = B` (the spectral theorem, entrywise); for
a diagonal matrix the perturbation bound is checked against explicit eigenvalues; a
concentration bound with rate `1/√n` feeds the `TendstoInMeasure` conversion.

## Part D — Sample moments and matrix concentration

**Topic T20 of the candidate design** — the applied end of the toolkit.

**Objects.** The sample mean of random vectors; the uncentered empirical second-moment
matrix `sampleCovariance V ω = fun k l => n⁻¹ Σ_i V i ω k * V i ω l` (Hermitian by
`isHermitian_sampleCovariance`); the centered scatter operator
`centeredScatter 𝕜 z = Σ_i rankOne 𝕜 (z i − finiteMean 𝕜 z) (z i − finiteMean 𝕜 z)` on a
general inner-product space.

**API to develop.**
- **Uncentered Chebyshev** `meas_gt_le_ofReal_integral_sq_div_sq`: from `∫ Y² ≤ v`,
  `P {η < Y} ≤ v/η²`, with no centering, nonnegativity, or measurability of `Y` beyond
  integrability of `Y²` — the raw form concentration arguments apply to error norms.
- **Sample-mean mean-squared error**: the scalar identity
  `integral_sq_scaledSum_sub_of_pairwise_indep` and its vector form
  `integral_norm_sq_average_sub_eq_sum`
  (`∫ ‖r⁻¹ Σ X_k − μ‖² = r⁻² Σ_k ∫ ‖X_k − μ‖²`, pairwise independence and common mean
  only, coordinatewise over an orthonormal basis); the iid collapse
  `integral_norm_sq_average_sub_of_iid` and the `γ/r` decay
  `integral_norm_sq_average_sub_le_of_bound`.
- **Centered scatter**: the **exact add-one update** `centeredScatter_append`
  (`S(snoc z y) = S(z) + n/(n+1) • rankOne δ δ` with `δ = y − finiteMean z` — an
  identity, not an estimate, and exact accounting for the mean shift is what makes the
  scatter incrementally computable), with `finiteMean_append`,
  `sum_sub_finiteMean_eq_zero`, positivity (`centeredScatter_isPositive`), Löwner growth
  (`centeredScatter_le_append`), and the quadratic-form versions
  (`re_inner_centeredScatter_self`, `re_inner_centeredScatter_append`).
- **Matrix concentration**: the union bound `measure_exists_entry_gt_le`
  (`P {∃ k l, η < |Ŝ_{kl} − A_{kl}|} ≤ n² v/η²`), then through Part C's perturbation
  bound the **eigenvalue concentration**
  `measure_forall_abs_sortedEigenvalues_sub_le_ge` and its one-sided floor
  `measure_forall_sortedEigenvalues_ge_ge`; specialized to the empirical covariance via
  `integral_sq_sampleCovariance_entry_le` (per-entry mean-square `≤ v/n` from the scalar
  sample-mean identity) in `measure_forall_sampleCovariance_sortedEigenvalues_ge_ge`.

**Milestone D1 — eigenvalue concentration.**

```lean
theorem measure_forall_abs_sortedEigenvalues_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable fun ω => Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k, |sortedEigenvalues (hSherm ω) k - sortedEigenvalues hAherm k|
        ≤ (n : ℝ) * η} ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)
```

**Milestone D2 — the operator-norm deviation event.** The event the spectral-subspace
perturbation statistics consumes *directly*, and the last statement in the roadmap that is
not yet written down:

```lean
theorem measure_forall_norm_toEuclideanLin_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ k l, Measurable fun ω => Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ x, ‖Matrix.toEuclideanLin (Shat ω - A) x‖ ≤ (n : ℝ) * η * ‖x‖}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)
```

**It is not a corollary of Milestone D1, and the roadmap should say why.**  D1 concludes
about *eigenvalues*, and eigenvalue closeness does not bound an operator-norm difference —
two matrices can have identical spectra and differ by a rotation.  Both milestones descend
from the **same entrywise event** `{ω | ∀ k l, |Shat ω k l − A k l| ≤ η}`, D1 through
Weyl's inequality and D2 through Part C's `norm_toEuclideanLin_le_of_entry_le`; they are
siblings, not parent and child.  **Structuring the proof that way is part of the
milestone**: the entrywise event should be extracted as a named lemma with the Chebyshev
and union-bound cost paid once, and both conclusions read off it.  The probability `1 − n²
v/η²` is then literally the same number in both, rather than two coincidentally equal
bounds.

**No symmetry hypothesis appears**, deliberately — `Shat ω − A` needs none for an operator
norm bound, whereas D1 needs both matrices Hermitian to have eigenvalues at all.  Dropping
the hypothesis where it is not used is what lets this event be consumed by a
Davis–Kahan application that has already discharged symmetry elsewhere.

**The route is deliberately elementary, and the statement must say so.** Chebyshev plus a
union bound costs a factor `n` (entrywise-to-operator) and `n²` (union bound); a matrix
Bernstein / Tropp-style inequality would give `log n` dimension dependence, at the price
of the matrix Laplace-transform machinery Mathlib does not have. The trade — a weaker
constant from ingredients that exist, over a sharper constant requiring a substantial new
development — is right for a first pass, but the bound is **not sharp in the dimension**
and nothing downstream may treat the `n`-dependence as intrinsic. A matrix-Bernstein
upgrade is future work *on top of* this API, not a replacement for it.

**Acceptance examples.** iid coordinates with a fourth-moment bound give an explicit `v`
and the `v/n` entry rate; `η = c/(2d)` keeps a population eigenvalue floored at `c` above
`c/2` with high probability (the eigengap a downstream Davis–Kahan application needs);
the add-one scatter identity checked against a two-point family.

## Dependency ordering

**Parts A and B are independent leaves**: they need nothing beyond Mathlib — not each
other, not Parts C–D, and no other roadmap — and are submittable immediately and in
parallel, each as a single small PR (A: two files, one importing the other; B: the engine
and its corollaries).

**Parts C and D are a chain.** Part C consumes the **FiniteDimensionalOperators roadmap**
(Courant–Fischer and Weyl's inequality for symmetric operators, with the sorted
`LinearMap.IsSymmetric.eigenvalues` API) and the **SpectralTheory roadmap**'s
Borel-calculus layer (the countable restrict-cover gluing lemma
`measurable_of_iUnion_restrict` and the measurability toolkit around the functional
calculus). Part D consumes Part C and nothing else. Internal order: within Part C, norm
comparisons → eigenvalue perturbation → sorted-indexing theory → measurability; within
Part D, scalar moments → sample mean → matrix concentration → sample covariance, with the
centered scatter independent of the rest of D.

## References

- R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed. (2013) — spectral theorem, PSD
  Gram factorizations, Weyl's inequality (Theorem 4.3.1).
- R. Bhatia, *Matrix Analysis* (GTM 169, 1997) — eigenvalue perturbation
  (Corollary III.2.6).
- T. F. Cox, M. A. A. Cox, *Multidimensional Scaling*, 2nd ed. (2001), §2.2–2.3 —
  classical scaling: the PSD Gram embedding step.
- C. Berge, *Topological Spaces* (1963), and C. D. Aliprantis, K. C. Border, *Infinite
  Dimensional Analysis*, 3rd ed. (2006), Ch. 17 — the maximum theorem, hemicontinuity.
- G. Dal Maso, *An Introduction to Γ-Convergence* (1993) — recovery of minimizers from
  approximate minimizers.
- J. A. Tropp, *An Introduction to Matrix Concentration Inequalities* (Found. Trends ML,
  2015) — the sharper `log n` route deliberately not taken here.
- R. Vershynin, *High-Dimensional Probability* (2018) — sample covariance concentration
  and its uses.

## Provenance and decision record

*Secondary; a reviewer can skip this section. The mathematics above is the specification;
the source below is evidence of feasibility, not a prescription.*

A complete, fully proved staged implementation of all four Parts exists in the
Davis–Kahan/DKPS formalization repository (Kitware, Inc., Apache 2.0), under
`ForTauCeti/` in the final `TauCeti.*` / `TauCeti.Matrix.*` namespaces: Part A ↔
`ForTauCeti/LinearAlgebra/Matrix/{RankFactorization,PosDef}.lean`; Part B ↔
`ForTauCeti/Topology/{ApproxMinimizer,Berge}.lean`; Part C ↔
`ForTauCeti/Analysis/Matrix/{EntrywiseOpNorm,EntrywiseEigenvalue,Spectrum,SpectralFunctionMeasurable}.lean`
plus `ForTauCeti/MeasureTheory/Function/ConvergenceInMeasure.lean` and
`ForTauCeti/MeasureTheory/Measure/Typeclasses/Probability.lean`; Part D ↔
`ForTauCeti/Probability/Moments/{Variance,SampleMean,SampleCovariance,CenteredScatter,MatrixConcentration}.lean`.
Milestones A2, B3, C1's `RCLike` comparisons, and D2 are open (not staged) — **all four
were specified in full on 2026-07-31**, with statements and the reasons each is not a
corollary of its neighbour; before that they were named but not written down, which is the
one thing a roadmap may not do with its own open work. Decision
records carried over: Parts A/B lived in the retired `ForMathlib` staging tree until
2026-07-29 (lane FM-RETIRE, worked twice; the namespace reconciliation to `TauCeti.*` is
recorded in `ForTauCeti/Topology/Berge.lean`); several Part A/B statements are pinned as
data in `comparator/pending-*.json` and `Challenge/MathlibPending/**` (outside
`defaultTargets` — renames require `scripts/check_declaration_name_drift.py` and
`lake build Challenge`); the `[DecidableEq n]` instance on the three Part A rank theorems
is pinned by an immutable conformance statement and would be dropped upstream; the
Chebyshev-route dimension trade-off (Part D) was an explicit design decision, recorded so
the `n²` constant is never read as intrinsic; `CenteredScatter` was relocated beside the
other moment modules, replacing a bespoke `appendFin` with `Fin.snoc` and upgrading the
scatter to a `ContinuousLinearMap`. T21/T22 were rungs T and U of the internal
submission ladder — leaves nothing else imports, which is why they are cheap first
submissions.
