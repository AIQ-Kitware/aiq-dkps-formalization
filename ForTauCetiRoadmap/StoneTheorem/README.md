# Roadmap: one-parameter unitary groups and Stone's theorem

**Topic T13 of the candidate design.** Five modules, **and independent** — it can
be submitted without waiting on any other topic. That independence is new; see
*A spurious dependency this document removed* below.

T15c (the spectral measure of an unbounded self-adjoint operator) and T16
(Sylvester equations and Rosenblum) both consume it.

## The theorem this topic exists for

The generator of a strongly continuous one-parameter unitary group is
self-adjoint:

```lean
theorem isSelfAdjoint_generator (U : OneParameterUnitaryGroup H) :
    IsSelfAdjoint (generator U)
```

This is the **forward** direction of Stone's theorem. The converse — that every
self-adjoint operator generates such a group — is *not* in this topic, and does
not need to be: its consumers go the forward way. T16 has a concrete flow
`W t Z = U_A t ∘ Z ∘ (U_B t)⋆` and wants to know its generator is self-adjoint
so that the spectral theory applies.

## Statement of the objects

```lean
structure OneParameterUnitaryGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  U : ℝ → (H →L[ℂ] H)
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  ...

noncomputable def generator (U : OneParameterUnitaryGroup (H := H)) : H →ₗ.[ℂ] H
```

**The generator is a `LinearPMap`, and its domain is exactly the set of vectors
where the difference quotient converges.** That is the design decision worth
reviewing: the generator is genuinely unbounded, and defining it on a smaller
convenient domain would make the self-adjointness statement weaker than what
T15c and T16 need. Nothing here assumes a core or a dense domain in advance —
density is *derived*, as part of the proof.

## How self-adjointness is proved

The route is visible in the one-line proof of `isSelfAdjoint_generator`:

```lean
  isSelfAdjoint_of_surjective_addSub _ (generator_isFormalAdjoint U)
    (dense_domain_of_surjective_add_I _ (generator_isFormalAdjoint U)
      (exists_generator_add_I U))
```

Three ingredients, in the order they matter:

1. `generator_isFormalAdjoint` — symmetry, which is the easy half;
2. `exists_generator_add_I` — surjectivity of `generator + i`, the actual work;
3. density of the domain, **derived from** (1) and (2) rather than assumed.

This is the basic criterion — a symmetric operator with `A ± i` surjective is
self-adjoint — and stating it that way is what keeps the topic small. A reviewer
should check that step 3 really is derived, because assuming density would make
the theorem apply to fewer groups than claimed.

## The modules

| Module | Role |
|---|---|
| `OneParameterUnitaryGroup/Basic` | The structure, the generator as a `LinearPMap`, and the domain where the difference quotient converges. |
| `OneParameterUnitaryGroup/Stone` | Stone's theorem, forward direction. |
| `OneParameterUnitaryGroup/Commutant` | A bounded operator commuting with every `U t` preserves the generator's domain and commutes with the generator. |
| `OneParameterUnitaryGroup/SemigroupBridge` | Identifies the group with a strongly continuous semigroup. **Internal to the topic** — its only consumer is `Stone.lean`, which uses it to import semigroup results into the self-adjointness proof. |
| `SkewAdjointExponential` | For bounded skew-adjoint `B`, `t ↦ exp (t • B)` is such a group — the source of concrete examples, and the **Duhamel estimate** `‖exp (t • Bₘ) ψ − exp (t • Bₙ) ψ‖ ≤ |t| ‖(Bₘ − Bₙ) ψ‖`. |

`Commutant` looks like a convenience lemma and is not: it is what lets a
symmetry of the underlying problem descend to the generator. Its one consumer is
`HilbertSchmidtBlock` in **T16** — a two-sided block on the Hilbert–Schmidt
space commutes with the Sylvester flow, and `Commutant` is what turns that into
a statement about the flow's generator. Checked, having first guessed T15c.

The Duhamel estimate in `SkewAdjointExponential` is what makes the *Yosida*
approximation converge — bounded skew-adjoint operators approximating an
unbounded one give groups that converge strongly, and the estimate is the
uniformity that argument needs.

## A spurious dependency this document removed

Writing this roadmap found that T13 was assigned a module that does not belong
to it, and that the misassignment was inventing a dependency edge.

`IntertwiningUnitary` — Davis's canonical unitary between two complete
orthogonal families of projections, `U Pⱼ = (P'ⱼ Pⱼ P'ⱼ)^{-1/2} P'ⱼ Pⱼ` — was
listed under T13. Measured 2026-07-30:

* it contains **zero** occurrences of `OneParameterUnitaryGroup`, `Stone` or
  `generator`;
* its only `ForTauCeti` import is `PolarDecomposition`, which is **T02**;
* it is finite-dimensional, where the rest of T13 is not;
* its only consumer anywhere is `DavisKahan/Sources/Davis1963/RotationBound.lean`.

It is a polar-decomposition construction that happens to produce a unitary, and
"unitary" is the whole of what it had in common with this topic.

**The cost was not cosmetic.** `check_tauceti_roadmap_topics.py --needs`
reported `T13 needs T02`, and that edge came *entirely* from this one module —
none of the other five touches T02 at all. Reassigning it to T02 (whose
`PolarDecomposition` it already imports, so no new edge is created there) makes
**T13 independent**: Stone's theorem can now be submitted without waiting on
polar decomposition, and the `T13, T15b → T15c` chain shortens accordingly.

The partition remains total, disjoint and acyclic, checked after the change.

## Prerequisites

None. The independent topics are now **T01, T12, T13, T14, T15b, T21 and T22** —
seven of twenty-four, and this change added one of them.
