# Roadmap: operator ideals — approximation numbers, symmetric ideals, and Hilbert–Schmidt structure

Singular values do not stop at finite dimension.  For a bounded operator between normed
spaces their natural continuation is the sequence of **approximation numbers**

```text
aₙ(T) = inf { ‖T - R‖ : rank R ≤ n },
```

the operator-norm distances to the ranks.  On finite-dimensional Hilbert spaces these *are*
the singular values (Eckart–Young); in infinite dimensions they are the prototype
**s-numbers** (Pietsch), and the gauges of the sequence `n ↦ aₙ(T)` — Ky Fan partial sums,
`ℓᵖ` sums, the supremum — carve the bounded operators into the classical **symmetric
operator ideals**: the finite-rank-approximable operators, the Schatten classes, trace
class, Hilbert–Schmidt.  Mathlib has the static functional-analysis stack —
`ContinuousLinearMap`, operator norms and adjoints, `LinearMap.rank`, finite-dimensional
`LinearMap.singularValues`, the continuous functional calculus, `IsCompactOperator`, the
`lp` spaces — but **none of the s-number layer**: no approximation numbers, no object over
which a theorem can be stated once for "an arbitrary symmetric ideal norm", no Schatten,
trace-class, or Hilbert–Schmidt theory (checked 2026-07-28: no file under
`Mathlib/Analysis/` matches either name), and nothing rectangular.

The goal is to **build the reusable theory of these objects**, not to race to a handful of
named identities.  The bar for "done": a researcher in operator or perturbation theory
finds the approximation numbers with their complete elementary calculus (Part A), a
symmetric-ideal interface whose laws hold unconditionally and whose standard instances —
operator norm, Ky Fan, Hilbert–Schmidt, trace class, Schatten `p` — are constructed rather
than postulated (Part B), and a Hilbert–Schmidt space that arrives with inner product and
completeness already proved because it *is* Mathlib's `lp` (Part C).  A PR that proves a
headline identity but leaves the surrounding object without its basic API is not yet what
we want.

Suggested homes: `TauCeti/Analysis/OperatorIdeal/ApproximationNumber/`,
`TauCeti/Analysis/OperatorIdeal/Family/`, `TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/`.

`Suggested.lean` gives prototype signatures.  This markdown is definitive; the prototypes
are representative, neither exhaustive nor prescriptive about proof architecture.

## Generality bar (decide these up front; do not silently specialize)

- **Zero-based indexing.**  `aₙ(T) = dist(T, {R : rank R ≤ n})`, so `a₀(T) = ‖T‖` and the
  finite-dimensional identification is index-for-index against Mathlib's zero-based
  singular values.  The one-based literature convention is the documented translation
  `sₙ(T) = aₙ₋₁(T)`; Tau Ceti maintains no duplicate one-based API.
- **Real-valued approximation numbers, extended-real ideal gauges.**
  `approximationNumber T n : ℝ` with nonnegativity a theorem, matching Mathlib's `norm`,
  `dist`, and singular values.  Ideal gauges are `ℝ≥0∞`-valued and genuinely `∞` off their
  ideal.  Two different objects, not a conflict: a real number attached to one operator
  versus a gauge whose finiteness *defines* a class.
- **Rectangular, with independent universes.**  Source and target are distinct spaces in
  independent universes throughout the base layer; rank comparisons use `LinearMap.rank`
  with explicit `Cardinal.lift` lemmas where universes differ.  Square operators are
  specializations, never the primitive interface.
- **Scalar generality is a ladder, stated explicitly.**  The norm-and-rank layer is over a
  `NontriviallyNormedField 𝕜` on seminormed spaces; adjoint invariance and Eckart–Young
  over `[RCLike 𝕜]`; the min–max converse, the Ky Fan triangle inequality, and anything
  routed through the operator modulus over `ℂ`, where the Hilbert-space continuous
  functional calculus is registered.  A real theorem is never claimed merely by writing
  `[RCLike 𝕜]`; it needs a grounded real argument or the complexification transport of
  Milestone B4.
- **The approximable/compact boundary.**  `aₙ(T) → 0` characterizes finite-rank
  approximability on any normed pair, and approximable implies compact over a `ProperSpace`
  scalar; the converse is asserted **only when the target is a Hilbert space** — it is
  false for general Banach spaces without an approximation-property hypothesis, and none is
  smuggled in.  The hypothesis sits on the target rather than on the pair because that is
  where the approximation property lives; the domain stays an arbitrary normed space.
- **One `ℝ≥0∞` gauge as the sole datum of an ideal family.**  A family is presented by a
  single total gauge, the ideal recovered as its finiteness domain — never by a membership
  predicate plus an independent real gauge.  Only this presentation has an extensionality
  theorem (free data leaves the gauge unconstrained off the ideal); it is the classical
  symmetric-norming-function presentation (Gohberg–Krein, Calkin); every law holds
  unconditionally at non-members; and four laws suffice — subadditivity, absolute
  homogeneity, domination of the operator norm, the two-sided composition bound — with
  closure of the ideal under module operations a consequence, not an axiom.
- **Hilbert spaces for the family layer, forced by the examples.**  The four laws are
  norm-only and meaningful over Banach spaces, but of the motivating gauges only the
  operator norm survives outside Hilbert space: Ky Fan subadditivity runs through singular
  values and majorization, and `a_{m+n}(S+T) ≤ aₘ(S) + aₙ(T)` does not recover it (at
  `k = 2` it yields only `a₀(S) + 2a₀(T) + a₁(S)`).  No proof in the interface uses the
  inner product, so re-widening is mechanical should a Banach instance appear.
- **Two structures for the universe split.**  The rectangular family keeps source and
  target universes independent; the adjoint exchanges source and target, so the symmetric
  family is a second structure extending the diagonal instantiation, not an extra field.
- **Dominance is a property, not data**: Ky Fan dominance is a class over the symmetric
  family, so a family carries it as a fact about the family it already is.
- **Hilbert–Schmidt is `ℓ²` of columns, not a tensor product.**  The two models are
  isomorphic; they are not equally cheap.  The tensor route must construct the Hilbert
  tensor product and its basis-independence theory; the `ℓ²` route gets inner product and
  completeness from Mathlib's `lp` and leaves only the column bijection to prove.  The
  Hilbert basis is an explicit **parameter** of every statement — nothing asserts
  basis-independence of the representation, because nothing needs it; basis-independence of
  the underlying *energy* is a theorem of Part B.  The model is indexed by the operator's
  domain: `T : F →L[𝕜] E` corresponds to `lp (fun _ : ι => E) 2` with `ι` indexing a basis
  of `F`.
- **Normal forms.**  The approximation number is the normal form of the field-generic
  theory; the identification with singular values is a named theorem, not a global
  `@[simp]` rewrite.  Do not introduce private wrappers around existing Mathlib notions to
  restate a single hypothesis.

## What Mathlib already has (consume, and connect to)

- **Operators:** `ContinuousLinearMap`, the operator norm, composition, and
  [`ContinuousLinearMap.adjoint`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Adjoint.html)
  as a `LinearIsometryEquiv`; `LinearMap.rank`, `Module.finrank`, and `Cardinal` arithmetic
  for cross-universe rank bounds.
- **Finite-dimensional spectral theory:**
  [`LinearMap.singularValues`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/SingularValues.html)
  (zero-based), self-adjoint eigenbases, orthogonal projections / `Submodule.starProjection`;
  [`CFC.sqrt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.html)
  behind the operator modulus consumed from the FiniteDimensionalOperators roadmap.
- **Compact operators:**
  [`IsCompactOperator`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/Compact/Basic.html)
  with norm-limit closure (`isCompactOperator_of_tendsto`) and
  `isCompactOperator_of_locallyCompactSpace_dom`.  ⚠ Mathlib has **no
  finite-rank-implies-compact lemma**; providing it is a Part A target.
- **Hilbert bases and `ℓ²`:** `HilbertBasis`, `exists_hilbertBasis`, Parseval via
  `HilbertBasis.hasSum_inner_mul_inner`; `lp` with `lp.instInnerProductSpace` at `p = 2`,
  completeness for `1 ≤ p`, and `Memℓp`.
- **`ℝ≥0∞` machinery:** `ENNReal.tsum_comm` — the unconditional Fubini exchange that is the
  whole content of adjoint invariance for the Hilbert–Schmidt energy — and
  `ENNReal.Lp_add_le` (finite Minkowski; its `tsum` form at `p = 2` is a Part B target).
- **Work in motion:** Mathlib PR
  [#32126](https://github.com/leanprover-community/mathlib4/pull/32126) drafts a zero-based
  `ContinuousLinearMap.singularValue : ℕ → ℝ≥0` for normed spaces; see also the
  [Zulip thread](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Singular.20Value.20Decomposition.html)
  on singular values.  This roadmap deliberately pins `approximationNumber : ℕ → ℝ`,
  aligned with real-valued norms and infima, exposing nonnegativity separately.  If the PR
  lands, an interoperability layer becomes a milestone of the migration; Tau Ceti does not
  maintain two public APIs in the meantime.

## Part A — approximation numbers and Hilbert-space singular values

**Topic T09 of the candidate design.**  A complete staged implementation of this part
exists and needs Tau Ceti review and migration; acceptance examples (5)–(6) are the
genuinely open remainder, Milestone A3 having landed.

**Objects.**  `ContinuousLinearMap.approximationNumber T n : ℝ`, the infimum of `‖T - R‖`
over bounded `R` with `R.rank ≤ n`, on seminormed spaces over a `NontriviallyNormedField`;
the relation `HasSameApproximationNumbers` between operators on possibly different space
pairs (reflexive, symmetric, transitive — the vehicle for transporting ideal membership);
the Ky Fan gauge `kyFanGauge T k = ∑_{n<k} aₙ(T)`.

**API to develop.**

- The defining infimum exposed once (`approximationNumber_eq_iInf`), then the workhorses:
  the upper bound against every admissible approximant, the universal lower-bound iff
  (`le_approximationNumber_iff`), attainment given a best approximant, an `ε`-near
  approximant always exists; `a₀(T) = ‖T‖`, antitonicity, `0 ≤ aₙ(T) ≤ ‖T‖`, `aₙ(0) = 0`.
- The exact zero-based additive law `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`
  (`approximationNumber_add_le`; no truncated subtraction anywhere), with the Lipschitz
  bound `|aₙ(S) − aₙ(T)| ≤ ‖S − T‖` and norm-continuity of `T ↦ aₙ(T)`.
- The two-sided ideal laws `aₙ(A ∘ T ∘ B) ≤ ‖A‖ aₙ(T) ‖B‖` and `aₙ(c • T) = ‖c‖ aₙ(T)`;
  any stronger rank-splitting product inequality is a separate target, never implied by the
  word "multiplicativity".
- **Rank and compactness:** `aₙ(T) = 0` when `rank T ≤ n`, with the finite-dimensional
  converse as an iff; `aₙ(T) → 0` iff `T` is a norm limit of finite-rank operators with
  `n`-th term of rank at most `n`
  (`tendsto_approximationNumber_atTop_iff_exists_finiteRank_approx` — an explicit sequence;
  a named `ApproximableOperator` predicate is justified only by multiple consumers); finite
  rank implies compact over a proper field (`isCompactOperator_of_rank_lt_aleph0`, the
  lemma Mathlib lacks), hence approximable implies compact
  (`isCompactOperator_of_tendsto_approximationNumber`); and, once the *target* is an inner
  product space, the converse
  (`tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator`), which closes the
  boundary as the equivalence `isCompactOperator_iff_tendsto_approximationNumber`.
- **Hilbert layer:** adjoint invariance `aₙ(T⋆) = aₙ(T)` (`approximationNumber_adjoint`,
  via rank invariance under the adjoint and the adjoint isometry); over `ℂ` the sequence
  identity `aₙ(|T|) = aₙ(T)` (`modulus_hasSameApproximationNumbers`, from the pointwise
  identity `‖|T|x‖ = ‖Tx‖`; the modulus itself belongs to the FiniteDimensionalOperators
  roadmap); the unconditional lower bound `c ≤ aₙ(T)` from a `c`-coercive subspace of rank
  `> n` (`le_approximationNumber_of_lt_rank`), with unit-vector and
  linearly-independent-family forms.
- **Min–max, both halves.**  The orthogonal-tail equality on a complete source
  (`approximationNumber_eq_sInf_norm_comp_starProjection_orthogonal`), its collapse to `0`
  once `n` reaches the source dimension, and the sup formulation on the closed unit
  **ball** of `Vᗮ` (the sphere is empty at `V = ⊤`); over `ℂ` the converse localization:
  every strict lower bound of `aₙ(T)` is beaten on a subspace spanned by `n + 1`
  independent vectors, making `aₙ(T)` the least upper bound of its finite restrictions
  (`approximationNumber_isLUB_finiteRestrictions`).
- **Ky Fan gauges:** `kyFanGauge T 1 = ‖T‖`, the ideal laws, adjoint invariance, and the
  two-sided comparison `‖T‖ ≤ kyFanGauge T k ≤ k‖T‖`.

**Milestone A1 — Eckart–Young.**  On finite-dimensional inner-product spaces over
`[RCLike 𝕜]`, `aₙ(T) = σₙ(T)` index for index (`approximationNumber_eq_singularValues`),
covering rectangular maps and the range `n ≥ finrank 𝕜 E` where both sides vanish; Weyl's
sharp inequality `|σₙ(T) − σₙ(S)| ≤ ‖T − S‖` falls out by transport.

**Milestone A2 — the Ky Fan triangle inequality over `ℂ`.**
`kyFanGauge (S + T) k ≤ kyFanGauge S k + kyFanGauge T k` (`kyFanGauge_add_le`), false
termwise, proved by bootstrapping: the finite-dimensional case is the Ky Fan norm
inequality of the MajorizationAndAngles roadmap transported along Milestone A1; a
finite-dimensional source with arbitrary codomain follows by range compression; the general
case localizes along the min–max converse.  This is the single inequality every symmetric
ideal in Part B stands on.

**Milestone A3 — compact implies approximable on Hilbert spaces** (done): a compact
operator into a Hilbert space has `aₙ(T) → 0`
(`tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator`), completing the
boundary whose other three edges are in the API above; the four close as one equivalence,
`isCompactOperator_iff_tendsto_approximationNumber`, on a complete Hilbert target.

**Two hypotheses the milestone predicted are not needed, and the statements record it.**
The domain need not be a Hilbert space — only the *target* carries an inner product, since
what the proof uses is an orthogonal projection onto a finite-dimensional subspace of the
codomain, which is where the approximation property lives and therefore where the
counterexamples to the general-Banach statement bite.  Completeness of the target is not
needed either for the forward implication: a finite-dimensional subspace is complete on
its own.  Nor is the spectral theorem for compact self-adjoint operators applied to `T⋆T`,
which this milestone named as the route; the finite-`ε`-net argument (cover the image of
the unit ball, project onto the span of the net, and use that the orthogonal projection is
the nearest point) proves the stronger statement through a far smaller prerequisite.

```lean
noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖

theorem approximationNumber_add_le (T S : E →L[𝕜] F) (m n : ℕ) :
    approximationNumber (T + S) (m + n) ≤
      approximationNumber T m + approximationNumber S n

theorem approximationNumber_eq_singularValues  -- finite-dimensional, [RCLike 𝕜]
    (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n = T.toLinearMap.singularValues n
```

**Acceptance examples** (theorem-level tests, proved from the public API with the defining
infimum never unfolded): (1) zero and identity — `aₙ(id)` is `1` below the dimension, `0`
at or past it; (2) a rank-`r` orthogonal projection has exactly `r` approximation numbers
equal to `1`; (3) a rectangular diagonal map has approximation numbers its entries sorted
decreasingly, unequal dimensions included; (4) an explicit rank-`r` map has `aₙ = 0` for
`n ≥ r`; (5) on a small diagonal matrix the orthogonal-tail infimum selects the span of the
largest singular directions and returns the next singular value; (6) a diagonal compact
operator with coefficients tending to zero has `aₙ → 0`.  (5) is open.

**(6) is proved** — `TauCeti.tendsto_approximationNumber_diagOpLp`
(`ApproximationNumber/DiagonalSequence.lean`), for multiplication by a bounded sequence on
`lp (fun _ : ℕ => 𝕜) 2`.  **The route this paragraph predicted is not the route it took, and
the difference is the point of the example.**  The prediction was that (6) "needs that the
diagonal operator is compact, after which A3 supplies `aₙ → 0` directly".  It does not: the
`N`-th truncation has rank at most `N` and `‖T - T_N‖` is bounded by the tail of the
coefficients, which gives `aₙ → 0` with no compactness anywhere — and compactness then falls
out as a corollary (`TauCeti.isCompactOperator_diagOpLp`, through *approximable ⇒ compact*).
Going through A3 would have proved the statement without touching the reason it is true,
since the approximation numbers of a diagonal operator *are* its tail suprema.  Only the
upper bound is proved; the matching lower bound needs the coefficients ordered, which the
example does not assume.

## Part B — symmetric operator ideals and Schatten norms

**Topic T10 of the candidate design.**  The interface and four instances are staged and
building; the symmetric-gauge construction, the dominance principle, general Schatten `p`,
and the transport milestones are open.

**Objects.**  `TauCeti.OperatorIdealFamily 𝕜`: a single field
`gauge : (E →L[𝕜] F) → ℝ≥0∞` quantified over all Hilbert pairs in two independent
universes, with four laws (`gauge_add_le`, `gauge_smul`, `enorm_le_gauge`,
`gauge_comp_le`); `TauCeti.SymmetricOperatorIdealFamily 𝕜`, its diagonal extension by
`gauge_adjoint`.  Derived: the ideal `carrier : Submodule 𝕜 (E →L[𝕜] F)` of finite gauge;
`Elem`, the carrier as a type synonym carrying the **ideal** norm (the bare subtype
inherits the operator norm, which is the wrong instance); `IsComplete`, completeness of
`Elem` as a typeclass, never a hand-rolled Cauchy criterion.

**API to develop.**

- The unconditional consequences of the four laws: `gauge 0 = 0`, definiteness from
  `enorm_le_gauge`, negation invariance, finite-sum subadditivity, one-sided and
  contraction composition bounds, extensionality, closure of the carrier under module
  operations and outer composition; `Elem`'s normed-space structure with
  `‖A‖ = (gauge A.val).toReal` (lossless on members) and the contractive embedding
  `‖A.val‖ ≤ ‖A‖`.
- The instances, each with its gauge identified definitionally: the **operator norm**
  (`operatorNormFamily`; carrier `⊤`, `Elem` linearly isometric to `E →L[𝕜] F`,
  completeness inherited); the **Ky Fan families** over `ℂ` (`kyFanIdealFamily k`, gauge
  `ENNReal.ofReal (kyFanGauge · k)`; carrier `⊤`, complete via the two-sided comparison
  with the operator norm); the **Hilbert–Schmidt family** below; **trace class**
  (`traceClassIdealFamily`, gauge the nuclear norm
  `nuclearENorm T = ∑' n, ENNReal.ofReal (aₙ(T))`, whose triangle inequality is the Ky Fan
  inequality in the limit via `nuclearENorm_eq_iSup_kyFanGauge`, and whose membership
  predicate `IsTraceClass` is summability of the `aₙ`).
- The **Hilbert–Schmidt energy** `hilbertSchmidtEnergy T b = ∑' i, ‖T (b i)‖ₑ ^ 2` in
  `ℝ≥0∞` (no summability side conditions anywhere): Parseval in `ℝ≥0∞`, the rectangular
  adjoint swap by unconditional Fubini, hence **basis independence**
  (`hilbertSchmidtEnergy_indep`); the norm `hilbertSchmidtENorm` (its square root) with
  Minkowski at `p = 2` extended to `tsum`, domination of the operator norm, adjoint
  invariance, the two-sided ideal bound, the predicate `IsHilbertSchmidt`; the family
  `hilbertSchmidtIdealFamily`, built from orthonormal expansions and sharing no machinery
  with the approximation-number instances — the evidence that the interface is not shaped
  around one example.
- `IsKyFanDominant`, the dominance class
  (`(∀ k, kyFanGauge A k ≤ kyFanGauge B k) → gauge A ≤ gauge B`), with its
  membership-transport corollary and direct instances for the operator-norm, Ky Fan, and
  trace-class families.
- Finite-dimensional **Schatten norms** `schattenNorm p` for real `p ≥ 1` on the
  singular-value vector of length `min (finrank 𝕜 E) (finrank 𝕜 F)`, as rectangular
  unitarily invariant norms: triangle inequality from Ky Fan subadditivity plus `ℓᵖ`-gauge
  monotonicity under weak majorization (both consumed from the MajorizationAndAngles
  roadmap), definiteness, adjoint invariance, ideal inequalities, and the endpoint
  identifications `S₁ =` nuclear, `S₂ =` Frobenius, `S∞ =` operator norm.

**Milestone B1 — symmetric norming functions and the Calkin correspondence.**  A symmetric
gauge `Φ` on finitely supported `ℝ≥0` sequences (monotone, symmetric, normalized), its
extension to infinite sequences, and the induced family `S_Φ` with gauge `Φ ∘ a` read in
`ℝ≥0∞` — a `SymmetricOperatorIdealFamily` by construction.

**Milestone B2 — the Ky Fan dominance principle.**  Every family arising from a symmetric
gauge is `IsKyFanDominant`: termwise Ky Fan domination implies `Φ`-domination for every
symmetric gauge `Φ`.  This is the weak-majorization transfer of the MajorizationAndAngles
roadmap applied to singular-value sequences, and it delivers the triangle inequality for
every `‖·‖_Φ` at once.

**Milestone B3 — Schatten `p` in infinite dimensions, and reconciliation.**
`Φ_p(a) = (∑ aₙ^p)^{1/p}` through Milestone B1 gives the Schatten-`p` families for all
`p ≥ 1`; and the identity `∑' n, ENNReal.ofReal (aₙ(T)) ^ 2 = hilbertSchmidtEnergy T b`
reconciles the singular-value and orthonormal-expansion definitions at `p = 2`, which were
deliberately built by different routes.

**Milestone B4 — block sums and scalar transport.**  The gauge of an orthogonal
block-diagonal sum in terms of the summands; invariance under real ⇆ complex
complexification, so the real-scalar ideal theory (including the Ky Fan triangle inequality
over `ℝ`) is a transported instance rather than a re-proof.

```lean
structure OperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ≥0∞
  gauge_add_le   : ∀ ⦃…⦄ (A B : E →L[𝕜] F), gauge (A + B) ≤ gauge A + gauge B
  gauge_smul     : ∀ ⦃…⦄ (c : 𝕜) (A : E →L[𝕜] F), gauge (c • A) = ‖c‖ₑ * gauge A
  enorm_le_gauge : ∀ ⦃…⦄ (A : E →L[𝕜] F), ‖A‖ₑ ≤ gauge A
  gauge_comp_le  : ∀ ⦃…⦄ (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E),
      gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ
```

**Acceptance examples.**  The four instances instantiate the interface with their gauges
identified definitionally (`gauge_operatorNormFamily`, `gauge_kyFanIdealFamily`,
`hilbertSchmidtIdealFamily_gauge`, `gauge_traceClassIdealFamily`); the operator-norm and Ky
Fan carriers are provably `⊤` while the trace-class carrier is not — exhibiting a bounded
non-trace-class operator (an infinite orthonormal family suffices) is part of this
milestone's acceptance.

## Part C — Hilbert–Schmidt operators as an `ℓ²` space of columns

**Topic T11 of the candidate design.**  Staged and building; the work here is
review-shaped, and the design decision is the substance.

**Objects.**  For a Hilbert basis `b` of `F`: `columns b T = fun i => T (b i)` for
`T : F →L[𝕜] E`, and `ofLp b f : F →L[𝕜] E` for `f : lp (fun _ : ι => E) 2`, defined by
the absolutely convergent series `x ↦ ∑' i, (b.repr x i) • f i` (Cauchy–Schwarz against
the basis coefficients).

**API to develop.**

- Membership: `Memℓp (columns b T) 2 ↔ hilbertSchmidtEnergy T b ≠ ⊤` (`memLp_columns_iff`)
  — stated against Part B's energy so the model connects to the ideal theory instead of
  redefining "Hilbert–Schmidt"; the summability form `memLp_columns_iff_summable`.
- The bijection: the round trips `ofLp_columns` and `columns_ofLp`, injectivity
  (`ofLp_injective`), the unique-representative characterization
  (`existsUnique_ofLp_iff_summable`).
- The representation map is linear (`ofLp_add`, `ofLp_sub`, `ofLp_smul`, proved from the
  round trips) and bounded (`norm_ofLp_le : ‖ofLp b f‖ ≤ ‖f‖`).
- The `ℓ²` norm **is** the Hilbert–Schmidt norm:
  `‖f‖ ^ 2 = ∑' i, ‖ofLp b f (b i)‖ ^ 2` (`norm_sq_eq_tsum_norm_column_sq`), with the
  `ℝ≥0∞` comparison `energy_ofLp`.

So `lp (fun _ : ι => E) 2` *is* the Hilbert–Schmidt space, and it arrives with Mathlib's
inner product and completeness already proved.

**Milestone C1 — isometric conjugation.**  `Z ↦ U ∘ Z ∘ V` preserves the Hilbert–Schmidt
norm when `U` is norm-preserving and `V` has norm-preserving adjoint (`norm_conj_eq`, via
`hilbertSchmidtEnergy_isometry_comp` and its adjoint-transported right-hand twin).  The
left case is termwise trivial — composing with an isometry changes no column norm — and
the right case is the same statement about the adjoint; no basis-independence argument
appears, which in the tensor model is precisely the part that costs.  This is what makes
the Sylvester flow `Z ↦ U_A t ∘ Z ∘ (U_B t)⋆` a unitary group on the Hilbert–Schmidt
space, the hypothesis under which a downstream roadmap applies Stone's theorem.

**Milestone C2 — Pythagoras along an orthogonal family.**  A family splitting every
vector's norm (`∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2`) splits the energy on either side
(`tsum_energy_isometryFamily_comp`, `tsum_energy_comp_isometryFamily`) and jointly
(`tsum_tsum_energy_blocks`).  No countability, projection, or operator-topology
summability hypothesis: the pointwise norm split is all, and `ℝ≥0∞` keeps it
side-condition-free.

```lean
theorem ofLp_columns (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E)
    (hT : Memℓp (columns b T) 2) :
    ofLp b ⟨columns b T, hT⟩ = T

theorem columns_ofLp (b : HilbertBasis ι 𝕜 F)
    (f : lp (fun _ : ι => E) 2) : columns b (ofLp b f) = f
```

**Acceptance examples** (what a reviewer verifies): the right-hand side of
`memLp_columns_iff` is Part B's basis-independent energy, so nothing here is circular; the
basis is a parameter of every statement, and no statement asserts basis-independence of
the representation; `ofLp` is continuous with `‖ofLp b f‖ ≤ ‖f‖`, so the space is never
presented without its bounded representation map.

## Dependency ordering

Part A comes first and consumes two external roadmaps: the **FiniteDimensionalOperators
roadmap** (the CFC positive square root and operator modulus, the finite-dimensional
singular-value library and Courant–Fischer behind Milestone A1 and the modulus sequence
identity) and the **MajorizationAndAngles roadmap** (the finite-dimensional Ky Fan norm
inequality that seeds Milestone A2).  Part B consumes Part A — every ideal gauge here is a
functional of the `a`-sequence — plus the MajorizationAndAngles majorization engine (weak
majorization, symmetric gauges, the Hardy–Littlewood–Pólya transfer) for Milestones B2–B3
and the Schatten layer.  Part C consumes Part B for the energy and the ideal framing, and
otherwise only Mathlib's `lp` and `HilbertBasis`.  Within Part A, acceptance examples
(5)–(6) can land after the min–max layer; within Part B, the interface
and its four instances are dependency-closed on Part A and can ship first, with B1–B4
following in order.

## References

- A. Pietsch, *Operator Ideals*, North-Holland, 1980; *Eigenvalues and s-Numbers*,
  Cambridge Studies in Advanced Mathematics 13, 1987.
- I. C. Gohberg and M. G. Kreĭn, *Introduction to the Theory of Linear Nonselfadjoint
  Operators in Hilbert Space*, AMS Translations of Mathematical Monographs 18, 1969.
- J. W. Calkin, "Two-sided ideals and congruences in the ring of bounded operators in
  Hilbert space," *Ann. of Math.* 42 (1941), 839–873.
- B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS, 2005; M. Reed and
  B. Simon, *Methods of Modern Mathematical Physics I* — the Hilbert–Schmidt class as `ℓ²`
  of columns.
- R. Bhatia, *Matrix Analysis*, GTM 169, Springer, 1997 — Ky Fan inequalities and
  majorization.
- C. Eckart and G. Young, "The approximation of one matrix by another of lower rank,"
  *Psychometrika* 1 (1936), 211–218; L. Mirsky, "Symmetric gauge functions and unitarily
  invariant norms," *Quart. J. Math.* 11 (1960), 50–59.
- R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge, 2013, Thm. 4.2.6.
- M. Ullrich, "Inequalities between s-numbers," *Adv. Oper. Theory* 9 (2024), art. 75.

## Provenance and decision record

*This section records where the staged material came from and how decisions were made; it
is not part of the mathematical specification, and a reader may skip it.*

A staged implementation of nearly all of the above exists in the Davis–Kahan/DKPS
[formalization repository](https://github.com/AIQ-Kitware/aiq-dkps-formalization) under
`ForTauCeti/` (namespaces `TauCeti.*` / `ContinuousLinearMap.*`), Apache-2.0, Copyright
Kitware, Inc., with per-module provenance headers.  Part A's elementary layer was adapted
in part from Mathlib PR #32126 and developed further for Davis–Kahan perturbation theory;
migration must preserve provenance, authorship, and licensing while allowing Tau Ceti
review to improve the public API.

Part A lane record (2026-07-30): `AN-A4-RANK` done, including the finite-dimensional
converse iff; `AN-A4-COMPACT` — the characterization and *approximable ⇒ compact* landed
unconditionally (the finite-rank-compact lemma turned out to be a three-line corestriction
argument needing only `[ProperSpace 𝕜]`, not the predicted instance-plumbing), while
*compact ⇒ approximable* landed on 2026-07-30 as well (Milestone A3), by the finite-`ε`-net
argument rather than the predicted spectral theorem for `T⋆T`, and for an arbitrary normed
domain rather than a Hilbert pair; `AN-B4-MINMAX`
done, with the predicted witness `V := (ker R)ᗮ` and the ball-not-sphere sup formulation;
`AN-ACCEPT` — examples (1), (2), (4) and the diagonal example (3) are proved with the
defining infimum never unfolded; (6) landed 2026-07-30 by direct truncation rather than
through compactness, which it proves instead of assuming; (5) remains.  The Ky Fan gauge and its triangle
inequality, claimed by the old symmetric-ideals roadmap as its own scope, are staged among
the approximation-number modules; this consolidation dissolves that boundary question.

Part B decision record: the single-gauge presentation replaces the Davis–Kahan record
`RectangularSymmetricIdealFamily` (membership plus a total real gauge as independent
fields, one universe, hand-rolled completeness, fourteen fields), which is derivable from
the canonical family with deliberately no inverse and has been retired.  The Ky Fan family
originally carried a capability-class hypothesis for its triangle inequality; it was
discharged on 2026-07-28 when the min–max upper bound stopped depending on the donor's
projection-valued measures, and the `ℂ` instance is now unconditional (real scalars wait on
Milestone B4).  Two corrections against earlier drafts stand recorded: Mathlib has neither
`Schatten` nor a Hilbert–Schmidt theory (an early draft claimed it did), and `p = 2` was
built by the direct orthonormal route rather than through symmetric gauges — deliberately,
since it needs no spectral theory, at the price of the reconciliation obligation in
Milestone B3.

Part C decision record: the donor development (Spectra) realizes the space as a Hilbert
tensor product built from scratch, with a measured closure of 21,581 lines; this model is
four modules on top of Mathlib's `lp`.  The claim that nothing is lost was tested, not
asserted: lane `HS-PORT` (2026-07-30) rewrote a 250-line tensor-model consumer against this
model, and every tensor-model identifier had a one-line counterpart.  Writing the old
roadmap surfaced that three elementary `ofLp` lemmas (`ofLp_sub`, `ofLp_zero`,
`norm_ofLp_le`) had been stated in the downstream Sylvester topic; they were moved here
(and made scalar-generic) so this part is submittable on its own.

This roadmap consolidates the former one-topic roadmaps `ApproximationNumbers` (T09),
`SymmetricOperatorIdeals` (T10), and `HilbertSchmidtOperators` (T11).
