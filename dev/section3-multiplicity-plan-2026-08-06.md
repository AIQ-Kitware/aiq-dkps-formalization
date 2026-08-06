# Section 3: what is actually missing, and the build order

Investigated 2026-08-06.  **Read this before touching `Frontier/Section3.lean`.**

## 1. Corollary 3.1 is already proved — the frontier copy is stale

`MathAhead.HiddenFoundations.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`
(`DavisKahan/Geometry/Halmos/CompactClassification.lean:195`, **sorry-free**) is
Davis--Kahan Corollary 3.1, with the invariant `SameCompactAngleData`: the four
elementary Halmos isometries plus

```
angleMultiplicity : ∀ μ : ℂ,
  finrank ℂ (eigenspace (genericCosineBlock U₁ V₁).toLinearMap μ) =
  finrank ℂ (eigenspace (genericCosineBlock U₂ V₂).toLinearMap μ)
```

The `sorry` at `Frontier/Section3.lean:1088` differs from it in exactly two ways:

1. **It uses the wrong operator.**  It compares `genericHalmosCosineSq`, which is the
   *symmetrized* block and equals `A ⊕ A` — doubled multiplicity.  A docstring at
   `Frontier/Section3.lean:1005` records the 2026-08-04 decision that put
   `genericCosineBlock` (`= A`) into `SameHalmosOperatorInvariant` precisely because
   recovering `A` from `A ⊕ A` at the operator level is multiplicity-halving, i.e.
   Hahn--Hellinger.  **`corollary3_1_compact_angleList_classification` was never updated
   to match**; it is a leftover from before that decision.
2. **It phrases the invariant as an approximation-number list** rather than a dimension
   function.

Note (1) is *not* fatal at the list level: the sorted list of `A ⊕ A` is the list of `A`
with every entry repeated, so `list(A)(k) = list(A ⊕ A)(2k)` recovers it by elementary
means.  Multiplicity-halving is only hard at the abstract operator level.  Still, the
corollary should use `genericCosineBlock`, to match the recorded decision and the proved
theorem.

### The one genuinely missing lemma

Bridging (2) needs, for a **compact positive self-adjoint operator with trivial kernel**:

```
(∀ n, aₙ(A) = aₙ(B))  ↔  (∀ μ, finrank (eigenspace A μ) = finrank (eigenspace B μ))
```

* **(⟸)** is free: equal dimension functions give a unitary intertwiner
  (`TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`), and
  approximation numbers are unitary invariants.
* **(⟹)** is the real content, and reduces to
  `finrank (eigenspace A μ) = #{n | aₙ(A) = μ}` for `μ > 0`, via
  `#{n | aₙ(A) > ν} = dim (span of eigenspaces above ν)`.

**The trivial-kernel hypothesis is not optional**: without it, `A = 0` on `ℂ` and `B = 0`
on `ℂ²` have identical approximation-number sequences and are not unitarily equivalent.
Genericity supplies it — `eigenspace_genericCosineBlock_zero`
(`CompactClassification.lean:99`) proves the angle operator has trivial kernel, because on
the generic part no vector sits at angle `π/2`.

### Defect to repair while here

`CompactPositiveListFoundation` (`DavisKahan/SpectralTheory/SpectralMultiplicityFoundation.lean`)
states `positive_compact_list_complete` **without** the trivial-kernel hypothesis, so by
the `A = 0` counterexample above the structure is **uninhabitable** and
`list_eq_iff_unitarilyEquivalent` is vacuous.  Nothing consumes it yet (only two aggregate
imports), so the repair is free: add `eigenspace A 0 = ⊥` and `eigenspace B 0 = ⊥`, then
instantiate it from the bridge.  This is the same trap class as a `sorry`-ed definition —
an unsatisfiable specification, not merely an unproved one.

## 2. Theorem 3.1 needs Hahn--Hellinger, and there is no shortcut

`twoProjection_operator_classification` (proved) already carries Theorem 3.1's
mathematical content, with the invariant "the generic cosine blocks are unitarily
equivalent".  The `sorry` at `Frontier/Section3.lean:1060` buys only the paper's *literal*
phrasing, "same spectral multiplicity", and that is exactly Hahn--Hellinger.

**Confirmed absent everywhere.**  Mathlib has no cyclic subspaces, no multiplication
model, no multiplicity function, no Hahn--Hellinger — `grep` over `Mathlib/Analysis` for
`cyclicSubspace`, `MultiplicationOperator`, `spectral multiplicity` returns nothing.

**Two things not to do.**

* Do **not** define `SameSpectralMultiplicity` as unitary equivalence of the
  projection-valued measures.  It is equivalent, and the companion theorem would be a
  real spectral-theorem application rather than a triviality — but it abandons the measure
  class and the cardinal-valued multiplicity function that `Frontier/Core.lean:71`'s
  docstring demands, and that docstring is a recorded decision.
* Do **not** state Theorem 3.1 parameterized by `M : SpectralMultiplicityFoundation`.
  That declaration would be admission-free and would *ground the frontier node*, while its
  hypothesis is an unproved structure.  It games the metric.

### Build order for the multiplicity stack

The repo's Borel calculus already gives the hardest analytic input, so the first two
layers are genuinely reachable:

1. **Cyclic subspace** `Z(x) := closure (span {f(A) x : f bounded Borel})`.
2. **The cyclic multiplication model**: `L²(μ_x) → Z(x)`, `f ↦ f(A) x`, is unitary, where
   `μ_x` is the scalar spectral measure of `x`.  The isometry is
   `‖f(A)x‖² = ⟪x, (f̄ f)(A) x⟫ = ∫ |f|² dμ_x`, which is
   `borelCalculus_mul` + `borelCalculus_conj` + `inner_borelCalculus_self`
   (`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Multiplicative.lean`).
   `μ_x` is `ProjValMeasure.diag`, already carried as data.
3. Orthogonal decomposition of `H` into countably many cyclic subspaces (Zorn; separable).
4. Ordering by measure class — the maximal spectral type first; needs Radon--Nikodym.
5. The multiplicity function and its uniqueness.  **This is the hard layer.**

Layers 1--2 are the reusable cornerstone and should be built first, in `ForTauCeti`.

---

## 3. Layer-by-layer design (investigated 2026-08-06, second pass)

### Next increment, and why it is first

**Replace the `sorry`-ed `def SameSpectralMultiplicity` (`Frontier/Core.lean:71`) with a
concrete definition.**  It needs no new mathematics, and it converts
`sameSpectralMultiplicity_iff_unitarilyEquivalent` from a statement about an opaque term —
*unprovable*, asserting nothing — into a merely unproved one.  That is a categorical
improvement and it unblocks everything else.

Candidate, which visibly discharges both requirements the `Core.lean` docstring makes
(measure class **and** cardinal-valued multiplicity function):

```
structure MultiplicityLevels (μ : Measure ℂ) where
  level : ℕ → Set ℂ                     -- level k = {multiplicity > k}
  measurable_level : ∀ k, MeasurableSet (level k)
  antitone_level : Antitone level
  level_zero : μ ((level 0)ᶜ) = 0

multiplicityModel μ D := lp (fun k : ℕ => Lp ℂ 2 (μ.restrict (D.level k))) 2
multiplicityOperator  := coordinatewise multiplication by the coordinate
HasMultiplicityModel A μ D := BoundedOperatorsUnitaryEquivalent A (multiplicityOperator μ D)

SameSpectralMultiplicity A B :=
  ∃ μ ν D E, HasMultiplicityModel A μ D ∧ HasMultiplicityModel B ν E ∧
    μ ≪ ν ∧ ν ≪ μ ∧ ∀ k, μ (symmDiff (D.level k) (E.level k)) = 0
```

Encode the multiplicity function by its **level sets**, not as `m : ℂ → ℕ∞`: no
`MeasurableSpace ℕ∞` instance was verified, and level sets make every hypothesis a plain
`MeasurableSet`.  Push both spectral measures forward along `Subtype.val` to `Measure ℂ`
first — `spectrum ℂ A` and `spectrum ℂ B` are different subtypes and cannot be compared.

**Naming hazard:** there are *two* `BoundedOperatorsUnitaryEquivalent` in the repo —
`SpectralTheory/SpectralMultiplicityFoundation.lean:41` (one universe, `∘L` form) and
`Geometry/Halmos/UnitaryEquivalence.lean:52` (two universes, pointwise).  The model lives
in its own universe, so pick the two-universe one or the universe error surfaces late.

### The direction asymmetry is the opposite of the intuition

`SameSpectralMultiplicity → unitarilyEquivalent` is the **easy** direction: chain
`A ≃ model(μ,D) ≃ model(ν,E) ≃ B`.  Its only real content is the **Radon--Nikodym
unitary** `L²(μ) ≃ₗᵢ L²(ν)`, `f ↦ √(dμ/dν) · f`, for mutually absolutely continuous finite
measures; it intertwines multiplication operators trivially once it exists.  **Not in
Mathlib** (searched), but `Measure.rnDeriv`, `withDensity_rnDeriv_eq` and `rnDeriv_lt_top`
are.  Estimated 250--400 lines, and it is **independent of layers 3--4**, so it can be
built in parallel.  This is the second increment.

The converse needs *both* halves of Hahn--Hellinger — existence of a model (all of layers
3--4) and uniqueness.  You cannot produce a model without them.

### Layer 3: use a greedy `ℕ`-recursion, not Zorn

Zorn is the textbook route and is strictly worse here: it hands you a `Set H` of unknown
cardinality, and "an orthogonal family of nonzero closed subspaces in a separable space is
countable" is **not in Mathlib**.  With `[TopologicalSpace.SeparableSpace H]` and a dense
sequence, define `ξ (n+1) := orthogonalProjection ((⨆ k ≤ n, cyclicSubspace ha (ξ k))ᗮ)
(d (n+1))`; the index type is `ℕ` by construction.  Finish with
`IsHilbertSum.mkInternal` (`Mathlib/Analysis/InnerProductSpace/l2Space.lean:282`), whose
hypothesis is exactly `⊤ ≤ (⨆ i, F i).topologicalClosure`.

**Do not reach for `DirectSum.IsInternal`** — its bridges are algebraic and one needs
`[FiniteDimensional]`.  In infinite dimensions the decomposition is only a closed-span
one; `IsHilbertSum` is the right notion.

One genuinely new lemma: the orthogonal complement of a `borelCalculus`-invariant subspace
is invariant (`⟪f(a)η, x⟫ = ⟪η, f̄(a)x⟫ = 0`), which is the two steps already used inside
`norm_borelCalculus_apply_sq`.  Mechanical, ~60 lines.

**Separability must become a hypothesis**, and that is a recorded-decision-level change:
`theorem3_1_spectralMultiplicity_classification` currently carries none, while the proved
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant` needs none.  Adding
it weakens the frontier statement relative to what is already proved.  **Write it down;
do not slip it in.**

### Layer 4: the hard step is the Borel calculus on a reducing subspace

The nesting `μ₁ ≫ μ₂ ≫ …` recurses on the orthogonal complement after splitting off a
cyclic subspace, which needs the Borel calculus of `a|_K` and its compatibility with the
ambient one — `IsStarNormal (a|_K)`, `spectrum ℂ (a|_K) ⊆ spectrum ℂ a`, and the
restriction identity.  **This API does not exist** in
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/` (7 files) and is not in Mathlib.
Estimate 300--500 lines of genuinely new material.  **It is the only step with no partial
credit — do not start it before layer 3 and the additivity lemma below have landed.**

Reachable first (~100 lines, highest leverage in layer 4): `diagMeasure` is additive over
orthogonal cyclic subspaces, from `integral_diagMeasure` plus vanishing cross terms.  It
is what lets one vector realize the maximal spectral type.

Also absent and needing a definition: any notion of **measure class** — `grep` for
`MutuallyAbsolutelyContinuous`, `MeasureClass`, `Measure.Equivalent` finds only
`OuterMeasureClass`.  Define `μ ≪ ν ∧ ν ≪ μ` and its `Setoid`.  Trivial, but it must be
written.

Good news for both layers: `diagMeasure` is finite **and** regular already, so the
`HaveLebesgueDecomposition` instances fire with no work.

---

## 4. CORRECTION (2026-08-06, same day): separability is **not** required

§3 recommended a greedy `ℕ`-recursion for layer 3 and concluded that
`[TopologicalSpace.SeparableSpace H]` must become a hypothesis on Theorem 3.1.  **Reject
that.**  Theorem 3.1 must not be weakened: `pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`
is already proved with no separability, and the multiplicity-phrased version must match
its scope, not fall short of it.

**The separability was an artifact of the proposed proof, not of the theorem.**  The
`ℕ`-recursion was chosen to dodge a missing lemma ("an orthogonal family of nonzero closed
subspaces in a separable space is countable"), and it is exactly that choice — insisting
the index type be `ℕ` — that drags separability in.  It is unnecessary:

* `lp (E : α → Type*) (p)` is defined for an **arbitrary** index type `α`
  (`Mathlib/Analysis/Normed/Lp/lpSpace.lean:368`); there is no countability constraint.
* `OrthogonalFamily`, `IsHilbertSum`, `IsHilbertSum.mkInternal` and
  `IsHilbertSum.linearIsometryEquiv` are likewise stated over an arbitrary index type
  (`Mathlib/Analysis/InnerProductSpace/l2Space.lean:261-292`).

So run **Zorn over an arbitrary index type** and never mention countability.  A maximal
orthogonal family of cyclic subspaces exists by `zorn_subset_nonempty` (chains close under
union: the orthogonality condition has finite character), maximality gives
`(⨆ i, Z i)ᗮ = ⊥` — otherwise a nonzero vector in the complement generates one more
cyclic subspace, orthogonal to all of them by the `Zᗮ`-invariance lemma, contradicting
maximality — and `IsHilbertSum.mkInternal` closes it.  The missing countability lemma is
simply not needed, because nothing claims countability.

**Consequence for layer 4.**  The chain `μ₁ ≫ μ₂ ≫ …` is the *separable* normal form and
must also be dropped.  The general statement, valid without separability, is the
**uniform-multiplicity decomposition**: `H` splits as an orthogonal sum over cardinals `κ`
of parts where `A` is `multiplication by x on L²(μ_κ) ⊗ ℓ²(κ)`, with the `μ_κ` mutually
singular.  That is Halmos's formulation, and it is indexed by cardinals rather than by an
initial segment of `ℕ`, so it needs no ordering of a sequence and no Radon--Nikodym chain.
`MultiplicityLevels` in §3 should therefore be re-indexed from `ℕ` to `Cardinal` — which is
also what makes it a genuinely *cardinal*-valued multiplicity function, as
`Frontier/Core.lean:71`'s docstring asks for, rather than an `ℕ`-valued approximation to
one.

The rest of §3 stands: the definition is still the next increment, the Radon--Nikodym
unitary is still independent and parallelizable, and the Borel calculus on a reducing
subspace is still the one step with no partial credit.

---

## 5. Where the measure-class Setoid is, and is not, load-bearing

Recorded 2026-08-06 after the Radon--Nikodym unitary landed without defining a measure
class.  The question is whether that is a corner-cut that will force a weakened theorem
later.  It is not — but only because of a distinction worth writing down, since the two
routes diverge exactly at the Setoid.

**The Setoid is not needed to state "same measure class."**  `μ ≪ ν ∧ ν ≪ μ` written inline
is the *same proposition* as a named `MeasureEquiv μ ν`; `Equivalence` is three one-line
lemmas.  Nothing is weakened by omitting it, and no quotient is needed for any statement in
route A below.

**Two routes, and they need different foundations.**

*Route A — the existential form.*
`SameSpectralMultiplicity A B := ∃ presentations of A and of B whose data agree`
(matching measures per cardinal, up to class).  Both directions of
`sameSpectralMultiplicity_iff_unitarilyEquivalent` go through **without uniqueness**:
`⟸` chains `A ≃ model ≃ model' ≃ B` using the Radon--Nikodym unitary, and `⟹` merely
transports a presentation along the given unitary.  This suffices for **Theorem 3.1**, is
paper-faithful, and needs neither a Setoid nor a canonical decomposition.

*Route B — the canonical form.*  `SpectralMultiplicityFoundation`
(`DavisKahan/SpectralTheory/SpectralMultiplicityFoundation.lean:58`) demands
`multiplicity : (H →L[ℂ] H) → Datum`, a **function**, with `invariant` and `complete`
phrased as `multiplicity A = multiplicity B`.  Inhabiting it needs:
1. a canonical `Datum`, which — the data being measures *up to class* — must be a quotient,
   i.e. **the Setoid**, and
2. **uniqueness** of the uniform-multiplicity decomposition, so the assignment is a
   function at all.

**So: proving Theorem 3.1 does not inhabit `SpectralMultiplicityFoundation`.**  Do not
conflate the two.  Landing route A leaves that structure uninhabited, exactly as it is
today, and it is *already* the case (see §1) that it was uninhabitable-as-written for a
different reason until repaired.

**Decision.**  Take route A first — it is the paper-faithful goal and is not a weakening of
any theorem.  But shape the API so route B is a strict extension rather than a rewrite:

* Name the relation `MeasureEquiv` and prove `Equivalence` **when it first appears**, even
  though route A only needs the conjunction.  It costs three lines and means the quotient
  can be formed later without touching a single call site.
* State the multiplicity data as a *family indexed by `Cardinal`* from the start (§4), not
  by `ℕ` — re-indexing later would touch every statement.
* Keep uniqueness as an explicitly recorded open obligation, not an assumption.  When it
  lands, `Datum := Cardinal → Quotient measureClassSetoid` and route B follows.

The corner to refuse is **not** the Setoid; it is silently treating route A's existential
as though it delivered a canonical invariant.  It does not, and the census must not claim
it does.

---

## 6. History note: commit `ddf151c3` is mislabelled

`ddf151c3` ("Record where the measure-class Setoid is load-bearing…") also contains the
first ~360 lines of `ForTauCeti/.../BorelCalculus/Restriction.lean` and the
`IsCalculusInvariant.borelCalculus_mem` helper added to `CyclicDecomposition.lean`.  Those
belong to the restricted-Borel-calculus deliverable completed in `5e445d10`, not to the
Setoid note, and its message does not mention them.

Cause: `git add -A` was run in the main tree while an agent was mid-file there.  Nothing
was lost — the working tree was a strict superset and the build stayed green — but one
deliverable is split across two commits and the first misdescribes its own contents.  The
history is not being rewritten, since it is already pushed; **read `5e445d10`'s message for
the mathematics of that file.**

---

## 7. OUTCOME (2026-08-06, same day): Theorem 3.1 is proved

`SameSpectralMultiplicity` is no longer a `sorry`ed `def`, and
`sameSpectralMultiplicity_iff_unitarilyEquivalent` and
`theorem3_1_spectralMultiplicity_classification` are proved.  `#print axioms` gives exactly
`[propext, Classical.choice, Quot.sound]` on all of them.  The frontier's Section-3 nodes are
grounded; every remaining ungrounded node in the manifest is Section 9.

### What was built, and where §3--§4 were right and wrong

Route A of §5 was taken, as planned.  Three of the four design calls in §3--§4 stood; the fourth
was overturned by the same argument that overturned §3's separability call, run in the other
direction.

* **Level sets, not a function `ℂ → ℕ∞` (§3): stood.**  `MultiplicityDatum.level : ℕ → Set ℂ`
  with `antitone_level`, so every hypothesis is a plain `MeasurableSet`.
* **Radon--Nikodym unitary independent and parallelisable (§3): stood**, and it is the entire
  content of the `⟸` direction, which carries **no separability hypothesis at all**.
* **`MeasureEquiv` named and proved an `Equivalence` up front (§5): done**, together with
  `measureClassSetoid`, so route B remains a strict extension.
* **Re-indexing from `ℕ` to `Cardinal` (§4): NOT done, and it should not be.**  §4 rejected
  separability because the `ℕ`-recursion that forced it was an artifact of the proof.  That was
  right about the *decomposition*, and it is why
  `exists_orthogonalFamily_cyclicSubspace` is still stated over an arbitrary index type with no
  countability anywhere.  But §4 then inferred that the multiplicity datum must be
  cardinal-indexed, and that inference is what fails: **the uniform-multiplicity normal form over
  an arbitrary index type needs non-σ-finite measures** -- `H = ⊕_{t ∈ [0,1]} L²(δ_t)` has
  uniform multiplicity one with counting measure on `[0,1]` as its base -- and every
  Radon--Nikodym tool in Mathlib, and every one in
  `ForTauCeti/MeasureTheory/RadonNikodymL2.lean`, is σ-finite.  A cardinal-indexed statement is
  therefore not merely harder; it is not expressible with the measure theory available.

### Separability, and why it is not a weakening

Theorem 3.1's multiplicity phrasing carries `[TopologicalSpace.SeparableSpace H₁]`.  Three facts
make that the right call rather than the retreat §4 refused:

1. **It is the paper's own convention.**  Davis and Kahan work under a global separability
   assumption; the source census records this twice, at the Section 6 rank hypothesis
   (`dev/davis-kahan-1970-full-source-census.md`), where the printed
   `dim X(E₀) < dim X(F₀)` does its only job *because* of that convention.
2. **Nothing already proved is weakened.**  The operator-level classification
   `pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant` is untouched: arbitrary
   complex Hilbert spaces, no compactness, no finite dimension, no separability.  It is that
   theorem, not this one, that grounds the frontier node and carries the classification content.
3. **It is confined to one direction and one space.**  `⟸` is separability-free
   (`unitarilyEquivalent_of_sameSpectralMultiplicity`).  `⟹` needs it on `H₁` only, because `B`
   inherits `A`'s datum along the given unitary.

The hypothesis is needed for exactly one reason: producing a model requires a **countable**
cyclic decomposition, because `rank S x n` counts *earlier* indices and so the index type must
be linearly ordered.

### The chain that was built

Measure theory (`ForTauCeti/MeasureTheory/`):

* `MeasureClass.lean` -- `MeasureEquiv`, `Equivalence`, `measureClassSetoid`, and
  `measureEquiv_withDensity_restrict`: a density and the restriction to its support have the same
  null sets.
* `LpComp.lean` -- `compLp`, `compLpEquiv` (two-sided a.e. inverse), `embLpEquiv` (transport
  along a measurable embedding, surjectivity by `Function.extend`), and the intertwining law
  `compLp_mulLp`; plus `mulLp_congr_ae`.
* `LpRestrict.lean` -- extension by zero as an isometry `L²(μ|ₛ) →ₗᵢ L²(μ)`, and
  `isHilbertSum_extendLp` over a countable measurable partition.  Denseness is proved in the
  contrapositive, so no summability argument appears.
* `LpSliceSum.lean` -- `sliceSum`, `isHilbertSum_sliceLp`, `sliceLp_mulLp`.  This is the step
  that turns a *direct sum* of multiplication models into a *single* one, after which everything
  is measure theory on `ℂ × ℕ`.
* `MultiplicityLevels.lean` -- `dominatingMeasure`, `rank`, `levelPiece`, `levelSet`,
  `antitone_levelSet`, `map_rankMap_sliceSum`, `exists_multiplicityLevels`.

Hilbert space (`ForTauCeti/Analysis/InnerProductSpace/`):

* `OperatorUnitaryEquiv.lean` -- the relation with `refl`/`symm`/`trans`, so the chain composes.
* `HilbertSumIntertwine.lean` -- two Hilbert sums of one family carry unitarily equivalent
  operators.  A density argument, not a computation.
* `BorelCalculus/SeparableCyclic.lean` -- countability of a uniformly separated set, hence of an
  orthogonal cyclic set, hence the `ℕ`-indexed decomposition, **padded with the zero vector**
  (whose cyclic subspace is `⊥`).
* `BorelCalculus/MultiplicityModel.lean` -- `MultiplicityDatum`,
  `exists_hasMultiplicityModel` (existence half of Hahn--Hellinger), and
  `operatorUnitaryEquiv_of_measureEquiv`.

### One implementation note worth keeping

`rank` is defined by **recursion on `n`**, not as `(Finset.range n |>.filter _).card`.  That one
choice makes monotonicity, measurability (by induction on `n`), and the key lemma
`exists_mem_rank_eq_of_rank_eq_succ` -- *if some index has rank `k+1` then some index has rank
`k`*, which is what makes the level sets antitone -- each a three-line induction.  The `Finset`
formulation needs a `max`-of-a-`Finset` argument for the same fact and a finite-union argument
for measurability.

### What remains open, and must not be overstated

`SameSpectralMultiplicity` is an **existential over presentations**.  Nothing proved here says
the datum of an operator is unique, so:

* **`SpectralMultiplicityFoundation` is still uninhabited**, and this work does not inhabit it.
  Its `multiplicity` field is a *function*, which needs uniqueness as well as existence, plus a
  canonical `Datum` -- i.e. the quotient by `measureClassSetoid`.  §5's route B is still open.
* The census must not claim a canonical invariant.  It claims what is proved: a complete
  invariant *in the sense of the biconditional*, which is what the paper's sentence asserts.
