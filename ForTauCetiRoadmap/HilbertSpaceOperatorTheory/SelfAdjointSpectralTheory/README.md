# Roadmap: spectral theory of self-adjoint operators — the Borel functional calculus, Stone's theorem, and unbounded operators on LinearPMap

The spectral theorem for unbounded self-adjoint operators is the single most
consequential absence in Mathlib's operator theory.  Mathlib has the *static*
stack — `ContinuousLinearMap` with adjoints and operator norms, the continuous
functional calculus (`cfcHom`) of a normal element, `spectrum`/`resolvent` for
Banach-algebra elements, `Measure` with Riesz–Markov–Kakutani, and unbounded
operators as `LinearPMap` with `adjoint`, `IsSelfAdjoint`, and closedness — but
none of the layer that makes quantum mechanics, spectral perturbation theory,
or evolution equations expressible: no Borel functional calculus, no
projection-valued measures, no resolvent theory for a partially defined
operator, no spectral measure of an unbounded self-adjoint operator, and no
Stone's theorem connecting self-adjoint operators to one-parameter unitary
groups.

This roadmap builds that layer as one body of mathematics.  Its five parts are
the five faces of a single subject: a one-parameter unitary group has a
self-adjoint generator (Stone, forward); a bounded normal operator has a Borel
calculus and a projection-valued measure; a partially defined operator has a
graph-and-domain calculus and, when self-adjoint, a real spectrum with
quantitative resolvent bounds; and the Cayley transform welds these into the
spectral measure of an unbounded self-adjoint operator, with Stone's theorem
in both directions as the dynamical payoff.

The goal is to **build the reusable theory of these objects**, not to race to
the named theorems.  The bar for "done": a researcher in mathematical physics
or spectral perturbation theory finds unbounded self-adjoint operators, their
resolvents, their spectral projections, and their unitary groups defined at
their natural generality and equipped with the standard API, so that the
spectral theorem and Stone's theorem are consequences of a developed theory
rather than isolated endpoints.  A PR that proves a headline theorem but
leaves the surrounding object without its basic API is not yet what we want.

Suggested homes:

```text
TauCeti/Analysis/InnerProductSpace/OneParameterUnitaryGroup/
TauCeti/Analysis/InnerProductSpace/BorelCalculus/
TauCeti/Analysis/InnerProductSpace/ProjValMeasure/
TauCeti/Analysis/InnerProductSpace/LinearPMap/
TauCeti/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean
TauCeti/MeasureTheory/   (the generic measurability and Helly-selection layer)
```

`Suggested.lean` gives prototype signatures.  The markdown specification is
definitive; the prototypes are representative, never an exhaustive checklist,
and not prescriptive about proof architecture.

## Generality bar (decide these up front; do not silently specialize)

### The representation decision: an unbounded operator IS a `LinearPMap`

This is the premise every part inherits, and the first thing a reviewer should
hold the code to.

1. Mathlib's `LinearPMap` (`H →ₗ.[ℂ] H`) is the foundational object.  There is
   no second bundled `ClosedOperator`-style foundation.
2. Closedness, dense domain, symmetry
   ([`LinearPMap.IsFormalAdjoint`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/LinearPMap.html)),
   and self-adjointness (Mathlib's `IsSelfAdjoint A`, i.e. `A.adjoint = A`) are
   **hypotheses on a raw partial map — properties, never structure fields** of
   a parallel operator type.  A theorem that needs three properties carries
   three hypotheses; the benefit is that no consumer ever unwraps a bundle,
   and Mathlib's `LinearPMap` API (`domain`, `graph`, `adjoint`, `le_def`)
   applies directly.
3. A bundle may be added only as a derived convenience carrying a `LinearPMap`
   and proofs; it may not own a parallel domain/action representation.  Any
   compatibility wrapper for existing bundled code is temporary and lives
   strictly downstream of the canonical layer.
4. Bounded operators enter through the existing full-domain construction
   (`T.toLinearMap.toPMap ⊤`), and their self-adjointness transports
   (`isSelfAdjoint_toPMap_top`).

The representation is fixed by interoperability, not taste: Tau Ceti's
C₀-semigroup generator already is a `LinearPMap`, and the OneParameterSemigroups
roadmap pins the same convention ("generators are unbounded, model as
`LinearPMap`"), so a second foundation would need an adapter at every boundary.

### Self-adjointness is proved by von Neumann's criterion, with density derived

The route to self-adjointness is: symmetry, plus **surjectivity of `A ± i`**,
with density of the domain **derived** from symmetry and surjectivity of
`A + i` rather than assumed.  Assuming density up front would make Stone's
theorem apply to fewer groups than claimed; deriving it replaces the
mollification argument of the textbook proof by three lines of inner-product
algebra.  A reviewer should check that no consumer of the criterion smuggles a
density hypothesis back in.

### A `LinearPMap` needs its own resolvent set

Mathlib's `spectrum R a` is `¬IsUnit (algebraMap R A z - a)`, defined for an
element of an algebra.  A `LinearPMap` is not an algebra element — `A - z` is
only defined on the domain — so the roadmap defines `resolventSet A` directly:
the `z` for which `A - z` has a **two-sided bounded inverse** (a left inverse
on the domain, and a right inverse on the whole space whose values land back
in the domain).  Both halves are load-bearing: for an unbounded operator,
injectivity on the domain and surjectivity onto the space are independent, and
a one-sided definition would admit "inverses" that leave the domain.  In the
bounded (`domain = ⊤`) case this agrees with Mathlib's notion, and the bridge
is a stated target rather than an implicit identification.

### PVMs live on `ℝ`, carry their diagonal measures as data, and relabel explicitly

`ProjValMeasure H` is a measure on the Borel sets of `ℝ` bundling the
projection field *and* the scalar diagonal measures `diag ξ`, welded by
`inner_proj`.  Countable additivity is therefore never stated as an axiom — it
already lives inside `Measure ℝ`; idempotence, self-adjointness, positivity,
and finite additivity are theorems.  The alternative — projections as the only
data, additivity as a field — would put a summability side-condition on every
consumer.  The spectrum of a normal operator lives in `ℂ`, so the PVM of a
normal operator is indexed along an explicit measurable relabelling
`κ : spectrum ℂ a → ℝ`: the real part for a bounded self-adjoint operator, the
inverse Cayley map for the unbounded theory.  `κ` is a parameter, not a
special case.

### Semibounds and lower bounds are hypotheses the consumer supplies

`SemiboundedBelow A c` and `SemiboundedAbove A c` are predicates on a partial
map and a real constant, never a subtype.  Where a lower bound
`c‖x‖ ≤ ‖A x - z • x‖` is free — off the real axis, from `|Im z|` — the
theorem proves it; at a real point there is no free bound, so the real-point
resolvent lemma **takes the bound as a hypothesis** and reruns the same
closed-range argument.  Not a weaker theorem: a factored one.  The caller with
a spectral gap or a semibound must not have to reprove closed range.

### Statements live at their natural generality

Facts about C⋆-algebra elements (the norm/spectrum interval characterization,
the gap inverse) are stated for C⋆-algebras, not for Hilbert-space operators.
The measurability lemmas behind the calculus (measurability of `ω ↦ cfc f (a ω)`,
compact-infimum measurability, Helly selection) are stated in `MeasureTheory`
for their own hypotheses, with no operator theory in sight.

### Rosenblum-adjacent material is excluded

The domain-aware Sylvester *equation* (a transport statement: `A X - X B = C`
with domain bookkeeping) and the intertwining chain up to the *continuous*
functional calculus belong here, because they are statements about the objects
this roadmap defines.  Solvability theorems of Rosenblum type, spectral-gap
Sylvester estimates, and their sin-Θ consequences are **excluded**: they belong
to the perturbation roadmap, which consumes this one.  The intertwining chain
deliberately stops before the Borel calculus so that Part D stays independent
of Part B.

## What Mathlib already has (consume, and connect to)

- **`LinearPMap`** with `domain`, `graph`, `adjoint`, `IsFormalAdjoint`,
  `IsSelfAdjoint` (with `isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A`),
  `IsSelfAdjoint.dense_domain`, `IsSelfAdjoint.isClosed`, and closure/core
  material — the canonical carrier of Parts C, D, E.
- **`ContinuousLinearMap`** with operator norms, adjoints, `IsSelfAdjoint`,
  `unitary`, and the exponential `exp` with `hasDerivAt_exp_smul_const` — the
  bounded side of Parts A and B.
- **The continuous functional calculus**: `cfcHom` / `cfc` of an `IsStarNormal`
  element, its multiplicativity, positivity, and norm control — the input
  Part B extends.
- **`spectrum` and `resolvent` for algebra elements**, including
  `spectrum.isOpen_resolventSet` — the bounded theory Part D's notions must
  bridge to, never duplicate.
- **Measure theory**: `Measure`, `IsFiniteMeasure`, regularity, Riesz–Markov–
  Kakutani for positive functionals, `StieltjesFunction`, dominated
  convergence, `Lp` — the machinery under the diagonal measures.
- **Topology/analysis**: `Submodule.topologicalClosure`, orthogonal
  projections and `HasOrthogonalProjection`, Neumann series, `Tendsto` filters
  (`𝓝[≠] 0` for difference quotients).

Everything below — the dynamical, projection-valued, and unbounded-spectral
layer — is absent upstream and is built here.

---

## Part A — One-parameter unitary groups and Stone's theorem

**Topic T13 of the candidate design** — independently submittable.

**Objects.** `OneParameterUnitaryGroup H`: a map `U : ℝ → (H →L[ℂ] H)` on a
complex Hilbert space, unitary (`⟪U t ψ, U t φ⟫ = ⟪ψ, φ⟫`), a group
homomorphism (`U (s+t) = U s ∘ U t`, `U 0 = id`), strongly continuous.  Its
**generator**: the `LinearPMap` whose domain is *exactly* the set of vectors
where the difference quotient `t ↦ (U t ψ - ψ)/(it)` converges, and whose
value is the limit.  This domain choice is the design decision worth
reviewing: the generator is genuinely unbounded, nothing assumes a core or a
dense domain in advance, and a smaller convenient domain would make the
self-adjointness statement weaker than what Part E consumes.

**API to develop.**
- Unitarity basics: `U(-t) = U(t)⋆`, norm preservation, `‖U t‖ = 1` on a
  nontrivial space; the time-reversed group.
- The difference quotient: additivity and `ℂ`-homogeneity in the vector (what
  makes the generator linear), the defining `Tendsto` characterization of the
  domain, and the domain's invariance under the group with
  `A (U s ψ) = U s (A ψ)`.
- **Symmetry without density**: the generator is formally self-adjoint,
  proved pointwise from `U t⋆ = U (-t)` — this half needs no density.
- **The commutant preserves the generator**: a bounded operator commuting with
  every `U t` maps the domain into itself and commutes with the generator
  there.  This is what lets a symmetry of an underlying problem descend to the
  generator; its consumer is the perturbation roadmap.
- **The semigroup bridge**: restricting to `t ≥ 0` and forgetting the complex
  structure exhibits the group as a strongly continuous *contraction* semigroup
  over the underlying real Banach space, with semigroup generator `i·A` on the
  same domain.  This is the interoperability clause of the representation
  decision made concrete, and it must track the C₀-semigroup API of the
  OneParameterSemigroups roadmap as that lands (see Dependency ordering).
- **Skew-adjoint exponentials**: for bounded self-adjoint `S`, the flow
  `expTime (I • S) t = exp (t • (I • S))` is such a group, norm-preserving,
  with derivative `expTime B t * B` — the source of concrete examples — and
  the **Duhamel estimate** for *commuting* bounded self-adjoint `Sₘ, Sₙ`:
  `‖exp(it Sₘ)ψ − exp(it Sₙ)ψ‖ ≤ |t|·‖(i Sₘ − i Sₙ)ψ‖`.  The commutation
  hypothesis is genuine, and it is all the Yosida scheme of Part E needs, since
  resolvents of one operator commute among themselves.

**Milestone A1 — von Neumann's criterion.** A symmetric operator with `A + i`
and `A - i` surjective is self-adjoint — with the density of the domain
**derived** from symmetry and surjectivity of `A + i`, not assumed.

**Milestone A2 — Stone's theorem, forward direction.** The generator of a
one-parameter unitary group is self-adjoint.  The proof is the criterion:
symmetry (easy half), surjectivity of `A ± i` via the semigroup resolvent
(the actual work), density derived.

```lean
structure OneParameterUnitaryGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  U : ℝ → (H →L[ℂ] H)
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  identity : U 0 = ContinuousLinearMap.id ℂ H
  strong_continuous : ∀ ψ : H, Continuous fun t : ℝ => U t ψ

noncomputable def generator (U : OneParameterUnitaryGroup H) : H →ₗ.[ℂ] H

theorem isSelfAdjoint_generator (U : OneParameterUnitaryGroup H) :
    IsSelfAdjoint (generator U)
```

**Acceptance examples.** For bounded self-adjoint `S`, the flow
`t ↦ exp (i t S)` is a one-parameter unitary group whose generator is `S`
viewed as a total partial map; the difference-quotient domain is all of `H`
exactly when the group is norm-continuous.

## Part B — The Borel functional calculus and projection-valued measures

**Topic T14 of the candidate design** — independently submittable.

Mathlib has the continuous functional calculus of a normal element and no
Borel one; it has measures and Riesz–Markov–Kakutani and no spectral measures.
This part supplies the step between: for a normal `a : H →L[ℂ] H`, a bounded
Borel symbol on `spectrum ℂ a` acts as a bounded operator, the assignment is a
`*`-homomorphism extending `cfcHom`, and indicator symbols yield a
projection-valued measure.

**Objects.** The **diagonal measure** `diagMeasure ha ξ`: the finite regular
Borel measure on `spectrum ℂ a` produced by Riesz–Markov–Kakutani from the
positive functional `f ↦ ⟪ξ, cfcHom ha f ξ⟫`, with
`∫ f ∂(diagMeasure ha ξ) = ⟪ξ, cfcHom ha f ξ⟫` for continuous `f`.  The
**polarized pairing** `pair ha f ψ ξ`, defined for any bounded Borel symbol by
the quarter-sum of diagonal integrals at `ξ + iᵏ • ψ`.  The admissibility
predicate `IsBddMeasurable f` (measurable, with a uniform bound).  The
operator `borelCalculus ha hf : H →L[ℂ] H` whose matrix elements are the
pairing.  The structure `ProjValMeasure H` (projection field over Borel sets
of `ℝ`, diagonal measures as data, welded by `inner_proj`; multiplicativity
and normalization as fields; everything else theorems).

**API to develop.**
- The transport principle, isolated in one place: every identity is checked
  for a continuous symbol — where it is a fact about `cfcHom`, hence free —
  and moved to the Borel symbol by `ε`-approximation in the `L¹` of the finite
  sum of diagonal measures occurring in the statement.  An identity mentioning
  finitely many vectors mentions finitely many diagonal measures, so one
  finite measure controls it.
- The calculus: agreement with `cfcHom` on continuous symbols; linearity;
  conjugation (`borelCalculus (conj f) = (borelCalculus f)⋆`); commutation
  with `a` and among values of the calculus; the norm bound
  `‖borelCalculus ha hf ξ‖ ≤ M‖ξ‖` for a symbol bound `M`; invariance under
  a.e. modification with respect to every diagonal measure.
- **Multiplicativity** — the one step needing the transport twice, in a fixed
  order: the approximant of `f` is chosen first, and the tolerance for the
  approximant of `g` depends on it.  There is no uniform bound over
  approximants; a reviewer should see this stated rather than discover it.
- Indicators to projections: `specProj`, idempotent and self-adjoint, with
  intersection-to-composition; the diagonal masses `specDiag`; the assembled
  `toProjValMeasure ha hκ` along a measurable relabelling `κ`; for bounded
  self-adjoint `T`, the relabelling is the real part, and half-line
  projections vanish exactly where the quadratic form is confined.
- The `ProjValMeasure` theory: idempotence, self-adjointness, monotone and
  finite additivity, `‖proj B ξ‖ ≤ ‖ξ‖`, extensionality in either field, and
  the countable splitting `∑' k, ‖proj (B k) ξ‖ₑ² = ‖ξ‖ₑ²` along a partition.
- The generic measure-theoretic layer, stated in `MeasureTheory` with no
  operator content: measurability of `ω ↦ cfc f (B ω)` for fixed continuous
  `f` (no measurable eigenbasis selection), measurability of compact infima
  of Carathéodory functions, and Helly selection with the Stieltjes measure
  of the monotone limit.

**Milestone B1 — the homomorphism.** The calculus is a linear, multiplicative,
star-preserving extension of the continuous calculus:

```lean
noncomputable def borelCalculus (ha : IsStarNormal a)
    {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) : H →L[ℂ] H

theorem borelCalculus_mul (ha : IsStarNormal a) (hf : IsBddMeasurable f)
    (hg : IsBddMeasurable g) :
    borelCalculus ha (hf.mul hg) = borelCalculus ha hf * borelCalculus ha hg
```

**Milestone B2 — the projection-valued measure.** `toProjValMeasure ha hκ :
ProjValMeasure H`, with its projections the indicator calculus and its
diagonals the pushed-forward diagonal measures.

**Milestone B3 — uniqueness and the bounded spectral theorem.** The calculus
is the unique extension of `cfcHom` whose matrix elements are integrals
against the diagonal measures; and the headline a reader opens the topic for:
a bounded self-adjoint operator is the integral of the identity against its
PVM.  Both are stated targets (the staged development constructs the calculus
and the PVM; the packaged uniqueness statement and the integral form are the
remaining mathematics).

**Acceptance examples.** On a multiplication operator, `borelCalculus` is
multiplication by the (bounded Borel) symbol; the PVM of a bounded
self-adjoint operator assigns to `[c, ∞)` the spectral projection that
half-line form bounds detect.

## Part C — Closed operators on LinearPMap: graphs, constructions, form bounds

**Topic T15a of the candidate design** — needs the FiniteDimensionalOperators
roadmap's spectral-subspace layer, and nothing else.

The vocabulary layer of the unbounded theory: everything Parts D and E state
about a partial map is phrased in the notions defined here.  This part is
where the representation decision of the generality bar becomes code.

**Objects and API to develop.**
- Domain relations as predicates: `SameDomain`, `MapsDomainTo`, `Extends`;
  domain-subtype simp lemmas so consumers never unfold.
- Reducing subspaces: `InvariantSubspace`, `ReducesSubspace`, the reduced
  restriction of a partial map to a reducing subspace with its density,
  closed-graph, symmetry, and self-adjointness inheritance.
- Transport constructions, each with density and closed-graph transport:
  pullback along a continuous linear equivalence, unitary conjugation
  (`unitaryConj` along `H ≃ₗᵢ[𝕜] H'`, preserving self-adjointness), and the
  direct sum of two partial maps.
- **The graph norm** `graphNorm A x = √(‖x‖² + ‖A x‖²)` on the domain subtype,
  with its elementary estimates — deliberately *not* a second topology on the
  domain: **graph cores** (`IsGraphCore`) are stated sequentially, recording
  exactly the two convergences a closed-graph argument consumes, and
  closedness in sequential form (`LinearPMap.IsClosed.mem_domain_of_tendsto`)
  is what carries an identity from a core to the whole domain.
- **Relative boundedness** `RelativelyBounded A V a b`
  (`‖V x‖ ≤ a‖x‖ + b‖A x‖`) with its closure laws (zero, monotonicity, sum,
  scalar, negation, restriction of a bounded map).
- **Perturbations**: `perturb A V` for a domain-defined `V` (the same domain,
  by construction — where Kato–Rellich arguments start), and
  `boundedPerturbation A T` for bounded `T`.
- Shifted-inverse data (`LeftShiftedInverseBound`, `TwoSidedShiftedInverseBound`)
  and the elementary real resolvent predicates `realResolventSet`,
  `realSpectrum`, `SpectralSetsSeparated` — the hypotheses shapes Part D's
  quantitative statements consume.
- The domain-aware **Sylvester equation** `SylvesterEquation A B X C`
  (`A X - X B = C` with domain transport as a field), its module structure
  (zero, add, neg, smul), the bounded case as a full-domain instance, and
  `HasBoundedEverywhereInverse` — transport statements only; no spectral
  content, per the generality bar.
- **Quadratic-form bounds**: `LowerFormBoundOn`/`UpperFormBoundOn` for a
  bounded operator on a subspace, and the bridge from a spectral inclusion of
  a restriction to those bounds over `ℂ` — this is where the
  FiniteDimensionalOperators spectral-subspace layer is consumed.

**Milestone C1 — bounded Kato–Rellich.** A bounded self-adjoint perturbation
of a self-adjoint partial map is self-adjoint on the same domain — direct,
with no relative-bound machinery, because a bounded perturbation does not move
the adjoint domain:

```lean
def perturb (A : H →ₗ.[𝕜] H) (V : A.domain →ₗ[𝕜] H) : H →ₗ.[𝕜] H

theorem isSelfAdjoint_perturb_bounded {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (perturb A (boundedPerturbation A T))
```

**Milestone C2 — the closed-graph characterization, and Kato–Rellich.** Two
stated targets completing the layer: the single iff *`A` is closed iff its
graph is closed iff every graph-convergent sequence has its limit in the
domain with the expected image* (the pieces exist; the packaged statement is
what a reader checks first), and the Kato–Rellich theorem proper — a
symmetric relatively bounded perturbation with bound `b < 1` of a self-adjoint
operator is self-adjoint — for which `perturb`, `RelativelyBounded`, and
Milestone A1's criterion are exactly the ingredients.

**Acceptance examples.** A bounded self-adjoint operator as a total partial
map is self-adjoint in the `LinearPMap` sense; the graph norm of a bounded
map is equivalent to the ambient norm; `⊤` is a graph core.

## Part D — Resolvents of self-adjoint LinearPMap operators, and semiboundedness

**Topic T15b of the candidate design** — independently submittable; the
cheapest way into the unbounded theory.

**Objects.** `resolventSet A` and `spectrum A` for `A : E →ₗ.[𝕜] E`, per the
generality bar; the named `resolvent A hz : E →L[𝕜] E`; the **Cayley
transform** of a self-adjoint operator.

```lean
def resolventSet (A : E →ₗ.[𝕜] E) : Set 𝕜 :=
  { z | ∃ R : E →L[𝕜] E,
      (∀ ψ : A.domain, R (A ψ - z • (ψ : E)) = (ψ : E)) ∧
      (∀ φ : E, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) }
```

**API to develop.**
- The resolvent is named, not just asserted: uniqueness (`resolvent_unique`,
  which lets any construction of an inverse identify itself as *the*
  resolvent), the left- and right-inverse laws, membership of values in the
  domain, the **first resolvent identity**
  `R w - R z = (w - z) • (R w ∘ R z)`, commutation of resolvents, and
  resolvent spectral mapping in the consuming direction (`μ ≠ 0` and
  `z + μ⁻¹ ∈ resolventSet A` exclude `μ` from the spectrum of the bounded
  `R z`).
- **Openness of the resolvent set** by Neumann-series perturbation through
  uniqueness; closedness and hence **measurability of the (real) spectrum** —
  proved for the sake of Part E, which must feed the spectrum to a PVM.
- **Real spectrum with the quantitative bound**: for self-adjoint `A` and
  `Im z ≠ 0`, the lower bound `‖(A - z)x‖ ≥ |Im z|·‖x‖` (the cross term in
  the expanded square is purely imaginary), then closed range, then dense
  range; so `z ∈ resolventSet A`, `spectrum A ⊆ ℝ`, and
  `‖R(z)‖ ≤ |Im z|⁻¹`.  Adjoints: `R(z)⋆ = R(z̄)`, and `R(z)` self-adjoint at
  real resolvent points.
- **The real-point case as a hypothesis**: at real `z` there is no free lower
  bound, so the same three steps run from an assumed
  `c‖x‖ ≤ ‖A x - z • x‖` — the factored form semibounded operators and
  spectral gaps plug into.  A two-sided shifted inverse with norm `≤ (r - s)⁻¹`
  exists across a spectral gap of width `r` around shift `s`.
- **The Cayley transform**: `cayley hA = 1 - 2i·R(-i)` (the manifestly bounded
  form of `(A - i)(A + i)⁻¹`), norm-preserving, surjective, unitary, hence
  `IsStarNormal` — the bounded unitary that hands Part E to Part B.
- **The C⋆-algebra gap inverse**, at C⋆ generality: a self-adjoint element has
  `‖a‖ ≤ r` iff its spectrum lies in `[-r, r]`; spectrum avoiding `(-r, r)`
  makes `a` a unit with `‖a⁻¹‖ ≤ r⁻¹`.
- **The intertwining chain**: a bounded `X` with `X ∘ A ⊆ B ∘ X` (stated
  domain-aware) intertwines the resolvents, the Cayley transforms, and the
  continuous functional calculus of the two operators.  The chain stops before
  the Borel calculus so this part stays independent of Part B; the disjoint-
  spectra vanishing theorem it feeds belongs to the perturbation roadmap.

**Milestone D1 — real spectrum, quantitatively.**

```lean
theorem mem_resolventSet_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A

theorem norm_resolvent_le_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A (mem_resolventSet_of_im_ne_zero hA hz)‖ ≤ |z.im|⁻¹
```

**Milestone D2 — the textbook characterization, and analyticity.** Two stated
targets: the single iff identifying `z ∈ resolventSet A` with *`A - z`
injective with closed dense range and bounded inverse* (currently spread
across the proofs), and analyticity of `z ↦ resolvent A hz` on the resolvent
set, the natural next statement after the first resolvent identity.

**Acceptance examples.** For bounded self-adjoint `T` as a total partial map,
`resolventSet` agrees with the complement of Mathlib's `spectrum ℂ T` and the
resolvent matches the Neumann series; a multiplication operator's spectrum is
the essential range of its symbol on a concrete example.

## Part E — The spectral measure of an unbounded self-adjoint operator, Stone uniqueness, and Yosida

**Topic T15c of the candidate design** — needs Parts A, B, and D (see
Dependency ordering).  The deepest part, and the reason the others exist.

**Objects.** For self-adjoint `A : H →ₗ.[ℂ] H`: the spectral measure
`spectralPVM hA : ProjValMeasure H`, obtained by relabelling the Borel
calculus of the Cayley transform along the inverse Cayley map
`w ↦ i(1+w)/(1-w)`; the spectral projections `specProjection hA B hB`; the
spectral subspace `specRange` and the reduction `specRestrict hA B hB`; the
Yosida approximants; and the unitary group `genToGroup hA` built from them.

**API to develop.**
- **The construction, honestly**: the relabelling blows up at `w = 1`, which
  can lie in the spectrum of the Cayley transform, so the construction is
  faithful only because every diagonal measure gives `{1}` zero mass — the
  symbol `(1 - w)·1_{{1}}(w)` vanishes identically while `1 - U = 2i·R(-i)`
  is injective.  A specification that omitted this would hide the one place
  the construction could fail.
- **The resolvent formula**, the property that characterizes the measure:
  `⟪ξ, R(z) ξ⟫ = ∫ (s - z)⁻¹ d(diag ξ)` for `z` off the real axis; spectral
  projections commute with the resolvent and preserve the domain.
- **Support**: a Borel set of resolvent points carries the zero projection —
  stated as a null statement, not via a defined `support` with an inclusion.
- **Reduction**: `specRestrict hA B hB` is again **self-adjoint** (symmetry is
  inherited; the surjectivities of `A ± i` come from the resolvent, which
  preserves the range), and a spectral gap of `B` around `λ` puts `λ` in the
  resolvent set of the restriction.
- **Form bounds from spectral support**: vanishing of `specProjection` on
  `(-∞, c)` (resp. `(c, ∞)`) yields `c‖x‖² ≤ Re⟪A x, x⟫` (resp. `≤`) on the
  domain — semiboundedness read off the measure; and on a spectral range with
  `B ⊆ [β, α]`, the quadratic form is confined to `[β, α]`.
- **The Yosida scheme, with named approximants**: `yosidaApprox hA n
  = n²·R(in) - in` and its symmetrized and mirrored forms, the contractions
  `n·R(±in)`, strong convergence `yosidaApprox x → A x` on the domain; the
  exponentials `expApprox hA n t = exp(it·(sym approximant))`, unitary, Cauchy
  uniformly on compact time intervals via Part A's Duhamel estimate (the
  approximants commute, which is why Duhamel's commutation hypothesis
  suffices); the strong limit `expLimit`, and `genToGroup hA :
  OneParameterUnitaryGroup H` — **Stone's theorem, construction half**.  The
  approximants are public and named because the convergence statements are
  about them, not about a limit appearing from nowhere.
- **Maximality, proved once**: self-adjoint `A ≤ B` forces `A = B`.  This is
  why identifying two self-adjoint operators never proves both inclusions.
- **Stone uniqueness** as the payoff of maximality: the generator of
  `genToGroup hA` is `A`.  Spectral projections commute with the group
  (commutation with the approximants survives the strong limit); interval
  cutoffs `specProjection hA [-τ, τ]` tend strongly to the identity.
- **The block-argument shapes** consumed by spectral perturbation theory: the
  grid `gridCell ε k = [kε, (k+1)ε)` with disjointness, covering, and the
  norm-splitting `∑' k, ‖E(cell k) ξ‖ₑ² = ‖ξ‖ₑ²`; the **cut operator** turning
  the pointwise bound `‖A y - c y‖ ≤ r‖y‖` on a spectral range into an
  operator statement; the **gap inverse** `gapInverse hA hδ` inverting `A`
  with norm `≤ δ⁻¹` on vectors whose diagonal measure avoids `(-δ, δ)`; and
  the reassembly lemma — a family that splits vector norms turns per-block
  lower bounds into a global one, stated with nothing about where the blocks
  come from.

**Milestone E1 — the spectral measure and its formula.**

```lean
noncomputable def spectralPVM (hA : IsSelfAdjoint A) : ProjValMeasure H

theorem spectralPVM_resolvent_formula {z : ℂ} (hz : z.im ≠ 0)
    (hzr : z ∈ resolventSet A) (ξ : H) :
    ⟪ξ, resolvent A hzr ξ⟫_ℂ = ∫ s, ((s : ℂ) - z)⁻¹ ∂((spectralPVM hA).diag ξ)
```

**Milestone E2 — Stone's theorem, uniqueness half.**

```lean
theorem generator_genToGroup (hA : IsSelfAdjoint A) :
    generator (genToGroup hA) = A
```

**Milestone E3 — the packaged statements.** Three stated targets completing
the theory: the spectral theorem as one declaration (*`A` is the integral of
the identity against its spectral measure*, the statement a reader opens the
topic for); Stone's theorem as the packaged bijection between self-adjoint
operators and strongly continuous one-parameter unitary groups (both halves
exist above); and uniqueness of the spectral measure (a `ProjValMeasure`
satisfying the resolvent formula is `spectralPVM hA`), the characterization a
reviewer will ask for.

**Acceptance examples.** For bounded self-adjoint `T` as a total partial map,
`spectralPVM` agrees with Part B's PVM under the real-part relabelling and
`genToGroup` is `t ↦ exp(itT)`; a multiplication operator's spectral
projections are multiplication by indicators.

---

## Dependency ordering

**Internal.** Parts A (T13), B (T14), and D (T15b) are mutually independent
and each is **independently submittable**; any of the three is a reasonable
first PR series.  Part C (T15a) is independent of A, B, D but consumes the
FiniteDimensionalOperators roadmap (below).  Part E (T15c) is the confluence
and **needs exactly A + B + D**: the Cayley transform and resolvent bounds
from D, the Borel calculus and `ProjValMeasure` from B, and the unitary-group
vocabulary, von Neumann criterion, and Duhamel estimate from A.  Part E does
not import Part C's constructions — the shared carrier of C, D, E is
Mathlib's `LinearPMap` itself, which is the representation decision working
as intended.  Within Part E, the Yosida/maximality material precedes the
construction; the grid/cut/block shapes depend on the construction only
through the cut operator and can land last or first.

**External.** The **FiniteDimensionalOperators** roadmap (the consolidated
finite-dimensional operator theory): Part C's spectral-order bridge consumes
its spectral-subspace layer.  Nothing else in this roadmap depends on it.

**Adjacent in-motion work.** The Tau Ceti **OneParameterSemigroups** roadmap
is the neighbouring active development: its generality bar already pins
"generators are unbounded, model as `LinearPMap`" — the same representation
decision — and it names Stone's theorem on Hilbert space as its C₀-group
stretch goal, which is exactly Parts A and E here.  Part A's semigroup bridge
identifies a unitary group with a strongly continuous contraction semigroup
and must be built against that roadmap's `StronglyContinuousSemigroup` and
generator API, not a private duplicate; conversely, this roadmap discharges
that roadmap's stretch goal, and the two should cite each other in PRs so
reviewers see one theory, not two.

**Downstream.** The perturbation roadmap (Sylvester equations, Rosenblum, and
the sin-Θ theorems) consumes Parts A, D, and E; the exclusions in the
generality bar mark the boundary.

## References

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional
  Analysis* (rev. ed. 1980) — VII (the spectral theorem, bounded and
  unbounded), VIII.3–4 (Stone's theorem, the Cayley transform, von Neumann's
  criterion).
- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space* (GTM 265,
  2012) — the modern unbounded theory: graph norms, cores, resolvents,
  semibounded operators, the spectral measure via the Cayley transform.
- W. Rudin, *Functional Analysis* (2nd ed. 1991), Ch. 12–13 — the Borel
  functional calculus and projection-valued measures for normal operators.
- T. Kato, *Perturbation Theory for Linear Operators* (2nd ed. 1976) —
  relative boundedness, Kato–Rellich, resolvent perturbation.
- J. Weidmann, *Linear Operators in Hilbert Spaces* (GTM 68, 1980) — closed
  operators, form bounds, spectral representation.
- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution
  Equations* (GTM 194, 2000) — the semigroup side of Stone's theorem and the
  Yosida approximation.

## Provenance and decision record

*This section is secondary: it records where the staged material came from and
which decisions were taken when.  A reviewer of the mathematics above can skip
it.*

The forty modules covering the five topics were authored in place in the
Davis–Kahan/DKPS formalization repository (Kitware, Inc.), are staged
sorry-free under `ForTauCeti/`, and still require Tau Ceti review and
migration.  Per-topic module lists come from
`scripts/check_tauceti_roadmap_topics.py --topic T13|T14|T15a|T15b|T15c`
(5 + 10 + 6 + 7 + 12 modules).

- **U1 (the representation decision).** A bundled `ClosedOperator` foundation
  existed in the Davis–Kahan corpus and was demoted; `LinearPMap` was chosen
  as the canonical carrier for interoperability with Tau Ceti's semigroup
  generator.  The measured hand-off is recorded in
  `dev/tauceti/u1-linearpmap-migration.md`, the decision in `AGENTS.md`.  Two
  bundled semibounded wrappers were deleted as dead code on 2026-07-28 — the
  evidence that the predicate form is what consumers use.
- **T15-SPLIT (2026-07-29/30).** The original 25-module, 6,700-line T15 was
  divided into T15a/T15b/T15c along the three dependency chains an audit
  found; the pre-split roadmap was kept only for the full U1 statement, now
  absorbed into the generality bar above.
- **T13 independence.** `IntertwiningUnitary` was misassigned to T13 and was
  the sole source of a `T13 needs T02` edge (measured 2026-07-30: zero
  occurrences of the group/generator vocabulary; only import is polar
  decomposition).  Reassigning it made T13 independent and shortened the
  `T13, T15b → T15c` chain.
- **Route decision (Part E).** The Cayley/Borel-calculus construction of
  `spectralPVM` was chosen over the Spectra library's Herglotz/Poisson route;
  the comparison is recorded in `dev/tauceti/spectra-removal-plan.md`, and the
  displaced target was `Spectra.QuantumMechanics.SpectralTheory.spectralPVM`.
  `SeparatedIntertwiner` (Part D) came from Spectra-removal lane SR-E; nothing
  staged imports Spectra.  `OneParameterUnitaryGroup/Basic` was copied and
  re-homed from the Spectra Formalization Project (Apache 2.0, Adam
  Bornemann), with per-file provenance headers.
- **Submission ladder.** T14, T15a, T15b, T15c are rungs K, L, M, N of
  `dev/tauceti/submission-ladder.md`; T16 (Sylvester/Rosenblum) and T17
  (Davis–Kahan sin-Θ) are the downstream consumers.
- **Reviewable PR slices**, carried over from the per-topic roadmaps: Part B
  as (1) the three `MeasureTheory` modules, (2) the calculus through
  multiplicativity, (3) the PVM; Part C as (1) the domain infrastructure
  alone — it is the file everything leans on, and reviewing it with anything
  attached is what makes a PR unreviewable — then (2) graph cores and
  constructions, (3) the Sylvester equation with the form bounds; Part D as
  (1) definition/named resolvent/openness — a coherent contribution on its
  own — then (2) real spectrum, (3) the C⋆ gap inverse and intertwiners;
  Part E as (1) Yosida and maximality, (2) the construction and resolvent
  formula, (3) the property modules, (4) the grid/cut/block shapes.
- This consolidated roadmap replaces the five per-topic documents (and the
  pre-split unbounded-operators document) written 2026-07-29/30 under lane
  ROADMAP-WRITE; their mathematical content is merged above without loss
  intended.
