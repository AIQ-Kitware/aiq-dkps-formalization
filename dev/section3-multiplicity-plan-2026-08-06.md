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
