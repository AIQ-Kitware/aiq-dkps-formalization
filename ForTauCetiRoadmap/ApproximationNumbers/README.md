# Roadmap: approximation numbers and Hilbert-space singular values

Approximation numbers measure how well a bounded linear operator can be
approximated in operator norm by operators of bounded rank.  For
`T : E →L[𝕜] F`, the zero-based approximation number is

```text
aₙ(T) = inf { ‖T - R‖ : rank R ≤ n }.
```

They are defined on general normed spaces, while on finite-dimensional Hilbert
spaces they coincide with the usual zero-based singular values.  This roadmap
builds the complete reusable API connecting those two viewpoints: 

* the field-generic approximation-number theory,
* its behavior under addition and composition,
* its relation to finite rank and compact approximation,
* adjoint invariance,
* its identification with singular values in finite dimensions (Eckart--Young),
* and finite- and infinite-dimensional min--max principles.


Suggested homes:

```text
TauCeti/Analysis/OperatorIdeal/ApproximationNumber/
TauCeti/Analysis/InnerProductSpace/OperatorModulus.lean
TauCeti/Analysis/InnerProductSpace/CourantFischer.lean
```

`Suggested.lean` gives prototype signatures.  The markdown specification is
definitive; the prototypes are neither exhaustive nor prescriptive about proof
architecture.

## Generality and pinned conventions

### Zero-based indexing

The primitive is indexed from zero:

```text
aₙ(T) = dist(T, {R : rank R ≤ n}).
```

Thus `a₀(T) = ‖T‖`, and the finite-dimensional identification is exactly
`aₙ(T) = σₙ(T)` with Mathlib's zero-based singular-value sequence.  The
one-based convention common in parts of the operator-ideal literature is
obtained by the documented translation `sₙ(T) = aₙ₋₁(T)` for `n ≥ 1`; Tau Ceti
does not maintain a duplicate one-based API.

### Real-valued approximation numbers

`approximationNumber T n : ℝ`, accompanied by
`approximationNumber_nonneg`.  This follows Mathlib's primary conventions for
`norm`, `dist`, and finite-dimensional singular values and avoids a parallel
`ℝ≥0` API.  Later operator-ideal gauges may legitimately be `ℝ≥0∞`-valued;
that is a different object, whose value may be infinite off the ideal.

### Rectangular operators and independent universes

The source and target are distinct spaces and may lie in independent universes.
The definition and all field-generic laws are stated for
`T : E →L[𝕜] F`.  Rank comparisons use `LinearMap.rank` and explicit
`Cardinal.lift` lemmas where universes differ.  Square operators are
specializations, not the primitive interface.

### Scalar generality

The approximation-number layer is stated over a
`NontriviallyNormedField 𝕜` and seminormed `𝕜`-spaces whenever the proof uses
only norm and rank.

Adjoint invariance and finite-dimensional singular-value results are stated
over `[RCLike 𝕜]`.  The reusable CFC construction of the operator modulus is
initially complex, because the relevant continuous functional calculus for
Hilbert-space operators is currently registered over `ℂ`.  A real theorem must
not be claimed merely by writing `[RCLike 𝕜]`; it requires a grounded real CFC
or a separately specified complexification argument.

### Namespace and normal forms

The public primitive is
`ContinuousLinearMap.approximationNumber T n : ℝ`, enabling dot notation such
as `T.approximationNumber n`.  The real codomain matches Mathlib's norms,
infima, and finite-dimensional singular values; nonnegativity is recorded by a
theorem rather than in the type.

The approximation number, not a finite-dimensional singular-value expression,
is the normal form for the field-generic theory.  Consequently the
finite-dimensional identification is a named theorem rather than a global
`@[simp]` rule.

## Existing foundations

Mathlib supplies `ContinuousLinearMap`, operator norms, composition and
adjoints; `LinearMap.rank`, `Module.rank`, and `Module.finrank`; real infima;
finite-dimensional `LinearMap.singularValues`, self-adjoint eigenvalues and
eigenvector bases; orthogonal projections; complex `CFC.sqrt`; and
`IsCompactOperator` with its composition and norm-limit closure API.

A sorry-free staged implementation under `ForTauCeti/` already contains the
A1--A3 inequalities and laws, B1--B3, B5, the complex min--max converse and
finite-restriction localization, and equality of the approximation-number
sequences of `T` and `T.modulus`.
These results still require Tau Ceti review and migration.

Do not introduce private wrappers around existing Mathlib or staged notions
merely to restate a single hypothesis.

## Related Work

As of 2026-07-28, Mathlib PR
[#32126](https://github.com/leanprover-community/mathlib4/pull/32126) is an open
draft developing a zero-based `ContinuousLinearMap.singularValue` for general
normed spaces, valued in `ℝ≥0`, together with elementary approximation-number
laws and finite-dimensional singular-value identification.

This roadmap deliberately chooses
`ContinuousLinearMap.approximationNumber : ℕ → ℝ`.  PR #32126 represents an
alternative choice: `ContinuousLinearMap.singularValue : ℕ → ℝ≥0`.  The Tau
Ceti choice keeps the API aligned with real-valued norms, infima, and Mathlib's
finite-dimensional singular values, while exposing nonnegativity separately.

If the Mathlib proposal lands, a later migration or interoperability layer can
be considered.  It is not a prerequisite for this roadmap, and Tau Ceti does
not maintain both public APIs in the meantime.

See also the
[public Mathlib discussion of singular values and approximation numbers](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Singular.20Value.20Decomposition.html).

## What remains to land

The staged results above must be reviewed and migrated.  The genuinely missing
mathematics is narrower:

- the finite-rank cutoff theorem and the approximable/compact boundary in A4;
- the finite-dimensional orthogonal-tail infimum formula in B4;
- theorem-level acceptance examples.

**Each is now a lane** (`jon (yardrat)`, 2026-07-30), so the remaining mathematics
of the first roadmap is claimable rather than described:

| lane | what it proves | depends on |
|---|---|---|
| ~~`AN-A4-RANK`~~ | **DONE 2026-07-30** — `approximationNumber_eq_zero_of_rank_le` (any normed pair), `…_of_rank_le_of_le`, and `approximationNumber_eq_zero_iff_finrank_range_le` (the converse, finite-dimensional) | — |
| `AN-A4-COMPACT` | **characterisation DONE 2026-07-30**; *approximable ⇒ compact* proved modulo a `finite rank ⇒ compact` lemma Mathlib lacks; *compact ⇒ approximable* on Hilbert spaces still open | `AN-A4-RANK` |
| ~~`AN-B4-MINMAX`~~ | **DONE 2026-07-30** — the exact orthogonal-tail equality `approximationNumber_eq_sInf_norm_comp_starProjection_orthogonal`, from the `≤` half `approximationNumber_le_norm_comp_starProjection_orthogonal` and the `≥` half `exists_finrank_le_norm_comp_starProjection_orthogonal_le` / `le_approximationNumber_of_forall_norm_comp_starProjection_orthogonal`. The witness is the one this table predicted, `V := (ker R)ᗮ`. All four of §B4's stated conditions are met | — |
| `AN-ACCEPT` | the six acceptance examples above, as theorems about the API. **(1), (2) and (4) DONE 2026-07-30** in `ApproximationNumber/Examples.lean` — the zero operator needed nothing (`approximationNumber_zero`), the identity is `1` below the dimension and `0` at or past it, and the rank cutoff has its `finrank` form | (3) the diagonal map's singular values; (5) `AN-B4-MINMAX`; (6) `AN-A4-COMPACT` |

Verified against the tree when the lanes were written: none of A4's four
statements and none of B4's equality exists, while every inequality and support
lemma they build on does — the lane rows name them individually. `dev/LANES.md`
carries the rows.

The complex-Hilbert min--max converse and finite-dimensional localization are
already staged and are specified below as B6.

---

## Part A -- approximation numbers on normed spaces

### A1 -- definition and intrinsic characterization

Define `ContinuousLinearMap.approximationNumber T n : ℝ` as the infimum of
`‖T - R‖` over bounded maps `R` with `R.rank ≤ n`.

Build the complete basic API:

- the exposed `_eq_iInf` characterization;
- `aₙ(T) ≤ ‖T - R‖` for every admissible `R`;
- the universal lower-bound characterization;
- equality when a best rank-`≤ n` approximant is supplied;
- `a₀(T) = ‖T‖`;
- antitonicity in `n`;
- `0 ≤ aₙ(T) ≤ ‖T‖`;
- `aₙ(0) = 0`;
- existence of an admissible approximant within every positive `ε` of the
  infimum.

The definition body should not be a simplifier normal form.  Downstream proofs
should normally use the upper- and lower-bound characterizations.

### A2 -- addition and perturbation continuity

Prove the exact zero-based additive inequality

```text
aₘ₊ₙ(S + T) ≤ aₘ(S) + aₙ(T).
```

Derive:

- `aₙ(S + T) ≤ aₙ(S) + ‖T‖`;
- `|aₙ(S) - aₙ(T)| ≤ ‖S - T‖`;
- continuity of `T ↦ aₙ(T)` in operator norm.

The index `m + n` is part of the pinned zero-based convention; no truncated
subtraction should appear.

### A3 -- ideal inequalities and homogeneity

For composable bounded maps, prove:

```text
aₙ(T ∘ B)       ≤ aₙ(T) ‖B‖,
aₙ(A ∘ T)       ≤ ‖A‖ aₙ(T),
aₙ(A ∘ T ∘ B)   ≤ ‖A‖ aₙ(T) ‖B‖,
aₙ(c • T)        = ‖c‖ aₙ(T).
```

These are the elementary two-sided ideal laws needed by every later operator
ideal.  Any stronger rank-splitting product inequality must be stated and
proved as a separate target rather than hidden behind the phrase
"multiplicativity."

### A4 -- rank, approximability, and compactness

Prove:

- ~~`aₙ(T) = 0` whenever `rank T ≤ n`~~ — **DONE 2026-07-30, lane AN-A4-RANK, and as
  an iff.** `ContinuousLinearMap.approximationNumber_eq_zero_of_rank_le` holds over
  any normed pair (`R := T` is admissible in the defining infimum), with
  `…_of_rank_le_of_le` for a consumer holding a finite rank bound `r ≤ n`; and
  `ContinuousLinearMap.approximationNumber_eq_zero_iff_finrank_range_le` is the
  converse on finite-dimensional inner product spaces, through `aₙ(T) = σₙ(T)` and
  Mathlib's `singularValues_pos_iff_lt_finrank_range`. The characterisation this
  section asks for is therefore in place;
- ~~`aₙ(T) → 0` exactly when `T` is a norm limit of finite-rank operators~~ —
  **DONE 2026-07-30, lane AN-A4-COMPACT.**
  `ContinuousLinearMap.tendsto_approximationNumber_atTop_iff_exists_finiteRank_approx`,
  stated as an explicit sequence with the `n`-th term of rank at most `n`, so no
  `ApproximableOperator` predicate was introduced — as this section asks;
- every such approximable operator is compact — **half done**:
  `ContinuousLinearMap.isCompactOperator_of_tendsto_approximationNumber` proves it
  *given* that finite-rank operators are compact, which it takes as a hypothesis
  because **Mathlib has no `finite rank ⇒ compact operator` lemma**. That lemma is
  general (the witness is the closure of `R '' ball 0 1`, compact as a closed
  bounded subset of the finite-dimensional, hence proper, `range R`) and belongs
  upstream rather than inside an operator-ideal module; the theorem's docstring
  gives its proof sketch and the lane records it as the remaining piece;
- on Hilbert spaces, every compact operator is approximable, hence
  `aₙ(T) → 0`.

The final implication is not asserted for arbitrary Banach spaces: compact
operators need not be norm limits of finite-rank operators without an
approximation-property hypothesis.  If Tau Ceti introduces a named
`ApproximableOperator` predicate, it should be justified by multiple consumers;
otherwise state the sequence-of-finite-rank characterization directly.

---

## Part B -- Hilbert-space singular-value theory

### B1 -- adjoint invariance

For real and complex Hilbert spaces, prove

```text
aₙ(T⋆) = aₙ(T).
```

The proof should use rank invariance under adjoint and the isometry of the
adjoint operation.  This theorem may be a simplifier because it removes an
adjoint from the approximation-number expression.

### B2 -- the rectangular modulus over complex Hilbert spaces

For `T : E →L[ℂ] F`, define

```text
|T| = (T⋆ T)^(1/2) : E →L[ℂ] E.
```

Develop the reusable object API, including:

- nonnegativity and self-adjointness;
- `|T| |T| = T⋆T`;
- uniqueness as the nonnegative square root;
- `‖|T|x‖ = ‖Tx‖`;
- `ker |T| = ker T`;
- `‖|T|‖ = ‖T‖`;
- the natural pre- and post-composition norm identities;
- commutation of moduli when the Gram operators commute.

This part does **not** claim a polar decomposition.  It does include the
heterogeneous sequence identity

```text
aₙ(|T|) = aₙ(T)
```

for complex Hilbert spaces, obtained from the pointwise norm identity and the
min--max theory rather than from a partial isometry.

### B3 -- finite-dimensional Eckart--Young

For finite-dimensional real or complex inner-product spaces, use Mathlib's
zero-based singular values and prove

```text
aₙ(T) = T.toLinearMap.singularValues n
```

The lower inequality must state that every rank-`≤ n` approximant has error at
least the `n`th singular value.  The upper inequality constructs the truncated
singular approximation.  The theorem must cover rectangular maps and the range
`n ≥ finrank 𝕜 E`, where both sides vanish.

### B4 -- finite-dimensional min--max formula

Prove an exact intrinsic equality, for example in the equivalent orthogonal-tail
form

```text
aₙ(T) = inf { ‖T ∘ P_(V⊥)‖ : finrank V ≤ n }.
```

The final theorem must specify:

- the subspace lies in the source;
- the dimension condition is `finrank V ≤ n` under zero-based indexing;
- the infimum behavior when `n` is at least the source dimension;
- its equivalence with the unit-vector formulation
  `inf_V sup_{x∈V⊥, ‖x‖=1} ‖Tx‖`.

Coordinate-span lemmas and eigenbasis calculations are support lemmas, not a
substitute for this equality.

**The equality is proved** (lane `AN-B4-MINMAX`, 2026-07-30), in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean`:

```text
aₙ(T) = sInf { ‖T ∘L (Vᗮ).starProjection‖ : FiniteDimensional 𝕜 V, finrank 𝕜 V ≤ n }
```

as `ContinuousLinearMap.approximationNumber_eq_sInf_norm_comp_starProjection_orthogonal`,
over a complete source.  The `≤` half is
`approximationNumber_le_norm_comp_starProjection_orthogonal`; the `≥` half went
through the witness this section predicted, `V := (ker R)ᗮ` for an admissible `R`
of rank at most `n`, and is available separately as
`exists_finrank_le_norm_comp_starProjection_orthogonal_le` (the witness) and
`le_approximationNumber_of_forall_norm_comp_starProjection_orthogonal` (the
usable lower-bound form).  Two supporting lemmas came out of it and are worth
naming: `rank_orthogonal_ker_le_of_rank_le`, which is the rank bound argued
through `Cardinal.lift` because source and target live in independent universes,
and `norm_comp_starProjection_ker_le_norm_sub`.

**All four stated conditions are met.**  The subspace lies in the source and the
dimension condition is `finrank 𝕜 V ≤ n` under zero-based indexing, both visible
in the statement.  The infimum's behaviour once `n` reaches the source dimension
is `approximationNumber_eq_zero_of_finrank_source_le`: `V = ⊤` becomes
admissible, `⊤ᗮ = ⊥`, the tail is the zero operator, and the infimum collapses to
`0` — read off the tail formula rather than off the rank characterisation, which
is what makes it a statement about the formula.  The equivalence with the sup
formulation is
`norm_comp_starProjection_orthogonal_eq_sSup_unitClosedBall`, via the bridge
`norm_comp_starProjection_orthogonal_eq_norm_comp_subtypeL`; it is stated on the
closed unit **ball** of `Vᗮ` rather than its unit **sphere**, deliberately,
because on `V = ⊤` the sphere of `Vᗮ = ⊥` is empty and its supremum is not the
tail, while the ball form holds for every `V`.

Completeness of the source is used exactly once, to give `ker R` an orthogonal
projection; the two sup-formulation lemmas and the dimension collapse need none.

### B5 -- unconditional infinite-dimensional lower bound

For arbitrary Hilbert spaces, prove:

```text
if rank V > n and c ‖x‖ ≤ ‖Tx‖ for every x ∈ V,
then c ≤ aₙ(T).
```

Also provide the finite-dimensional unit-vector and linearly-independent-family
forms used by applications.

### B6 -- converse and finite-dimensional localization

For complex Hilbert spaces, prove that every strict lower bound for `aₙ(T)` is
realized by a strictly larger uniform lower bound on a subspace generated by
`n + 1` linearly independent vectors.  Deduce that `aₙ(T)` is the least upper
bound of the `n`th approximation numbers of its restrictions to subspaces
generated by `n + 1` vectors.

---

## Acceptance examples

The development is accepted only when its abstractions compute correctly on
concrete operators.

1. ~~**Zero and identity:** all approximation numbers of zero vanish; for the
   identity on an `r`-dimensional Hilbert space, the first `r` approximation
   numbers are one and the rest are zero.~~ **DONE** — `approximationNumber_zero`
   (already present), `approximationNumber_id` and
   `approximationNumber_id_of_finrank_le`.
2. ~~**Orthogonal projection:** a rank-`r` orthogonal projection has exactly `r`
   nonzero approximation numbers, all equal to one.~~ **DONE** —
   `approximationNumber_starProjection` (`= 1` below the dimension) and
   `approximationNumber_starProjection_of_finrank_le` (`= 0` at or past it).
3. **Rectangular diagonal map:** a coordinate map with prescribed nonnegative
   diagonal entries has approximation numbers equal to those entries sorted in
   decreasing order, including unequal source and target dimensions.
4. ~~**Rank cutoff:** an explicit rank-`r` map satisfies `aₙ(T) = 0` for `n ≥ r`.~~
   **DONE** — `approximationNumber_eq_zero_of_finrank_range_le`.
5. **Min--max:** on a small diagonal matrix, the orthogonal-tail infimum selects
   the span of the largest singular directions and returns the next singular
   value.
6. **Compact Hilbert operator:** a diagonal compact operator with coefficients
   tending to zero has approximation numbers tending to zero.

These examples are theorem-level tests of the API, not merely `#eval` checks.

**Three are in place** (`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Examples.lean`,
lane `AN-ACCEPT`, 2026-07-30), and each is proved from the public API with the
defining infimum never unfolded — which is the property that makes an acceptance
example worth having: the lower bound for the identity comes from
`le_approximationNumber_of_finrank_lt` on the whole space, the upper from
`approximationNumber_le_norm` with Mathlib's `norm_id`, and the vanishing from the
rank characterisation. The file names the three that remain and the lane each waits
on.

## Ordering and PR slices

1. Review and migrate the staged elementary, Hilbert-space, and min--max layers
   in dependency order.
2. Add A4 and B4 as separate mathematical PRs.
3. Add the acceptance examples after the public API settles.

Each PR should be dependency-closed and should not mix downstream
Davis--Kahan migration with new Tau Ceti mathematics.

## References

- A. Pietsch, [*Operator Ideals*](https://www.sciencedirect.com/bookseries/north-holland-mathematical-library/vol/20/suppl/C), North-Holland Mathematical Library 20, North-Holland, 1980.

- A. Pietsch, [*Eigenvalues and s-Numbers*](https://openlibrary.org/books/OL2708279M/Eigenvalues_and_s-numbers), Cambridge Studies in Advanced Mathematics 13, Cambridge University Press, 1987.

- I. C. Gohberg and M. G. Kreĭn, [*Introduction to the Theory of Linear Nonselfadjoint Operators in Hilbert Space*](https://bookstore.ams.org/MMONO/18), Translations of Mathematical Monographs 18, American Mathematical Society, 1969.

- R. Bhatia, [*Matrix Analysis*](https://doi.org/10.1007/978-1-4612-0653-8), Graduate Texts in Mathematics 169, Springer, 1997.

- C. Eckart and G. Young, ["The Approximation of One Matrix by Another of Lower Rank"](https://doi.org/10.1007/BF02288367), *Psychometrika* 1(3) (1936), 211--218.

- L. Mirsky, ["Symmetric Gauge Functions and Unitarily Invariant Norms"](https://doi.org/10.1093/qmath/11.1.50), *Quarterly Journal of Mathematics* 11(1) (1960), 50--59.

- M. Ullrich, ["Inequalities between s-Numbers"](https://doi.org/10.1007/s43036-024-00386-x),
  *Advances in Operator Theory* 9 (2024), article 75.

- R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition,
  Cambridge University Press, 2013, Theorem 4.2.6.


## Mathlib References

- **Adjoints:** [`ContinuousLinearMap.adjoint`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Adjoint.html).

- **Finite-dimensional singular values:** [`LinearMap.singularValues`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/SingularValues.html).

- **Positive square roots:** [`CFC.sqrt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.html).

- **Compact operators:** [`IsCompactOperator`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/Compact/Basic.html).

- **Rank:** [`LinearMap.rank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/LinearMap.html).

## Provenance and coordination

A sorry-free staged implementation of most of Parts A and B exists in the
Davis--Kahan [formalization repository](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
under `ForTauCeti/`.  It was adapted in part from Mathlib PR #32126 and developed
further for Davis--Kahan perturbation theory.  Migration must preserve
provenance, authorship, and licensing while allowing Tau Ceti review to improve
the public API.
