# Roadmap: Sylvester equations and the Rosenblum theorem

**Topic T16 of the candidate design.** Eighteen modules — the largest topic, and
the hinge of the dependency graph. It consumes T04, T07, T11, T12, T13, T15b and
T15c, and T17 (the Davis–Kahan sin-Θ theorems) consumes it. If the roadmap is
submitted in order, this is the topic where the earlier ones start paying.

## The theorem this topic exists for

An operator intertwining two self-adjoint operators with disjoint spectra is
zero:

```lean
theorem eq_zero_of_intertwines_of_disjoint_spectrum
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y))
    (hdisj : Disjoint (spectrum A) (spectrum B)) :
    X = 0
```

`A` and `B` are unbounded (`LinearPMap`), which is the case that matters and the
reason the topic is large. The quantitative companion — a bound on `‖X‖` when
the spectra are separated by `δ` rather than merely disjoint — is what T17
actually consumes.

## The two design decisions worth reviewing

### 1. Rosenblum is proved *without* a Borel functional calculus

The textbook route upgrades continuous-symbol intertwining to Borel symbols,
then takes `E_A(S) = 0` and `E_B(S) = 1` for a Borel set separating the spectra.
That upgrade is a monotone-class argument through the diagonal measures, and it
is the expensive part of the standard proof.

This development avoids it, and the reason is precise enough to state:

> The obstruction to a *continuous* separator is a single point. Both Cayley
> spectra contain `1` as soon as both operators are unbounded, so no continuous
> symbol can be `0` on one and `1` on the other. But `1` is a null point for
> every diagonal measure, so a *sequence* of continuous symbols vanishing near
> `1` and separating elsewhere is enough.

Concretely: `separator` exists by Urysohn (both real spectra are closed and
disjoint), `cayleySymbol n` pulls it back along the inverse Cayley map, and the
limit is taken against the diagonal measures where `{1}` is null.

**A reviewer should check this claim rather than the proof**, because it is the
topic's main economy: if `1` were not null for the diagonal measures, the
argument would be wrong rather than merely different.

### 2. The Sylvester operator is reached through Stone's theorem, not through a calculus

The chain is worth stating because it is why T11, T12 and T13 are prerequisites
of this topic and not of each other:

1. **`Sylvester/Group`** — the flow `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` is a
   one-parameter group of *unitaries* on the Hilbert–Schmidt space. Unitarity is
   `HilbertSchmidtConjugation` from **T11**, unchanged; this module supplies the
   analytic half, strong continuity.

2. **`Sylvester/Generator`** — Stone's theorem (**T13**) hands back a
   self-adjoint generator; this module identifies it as `Z ↦ A Z − Z B`
   (`generator_sylvesterGroup_apply`).

3. **`Sylvester/SpectralGap`** — separated spectra force a lower bound on that
   generator at *every* vector of the Hilbert–Schmidt space, by cutting the line
   into cells of width `ε` and estimating on each.

4. **T12** supplies the sharp constant. The Haagerup–Zsidó kernel has `L¹` mass
   exactly `π / 2`, and substituting a separated pair of self-adjoint operators
   into its Fourier representation of `1/x` turns that mass into the constant in
   the Sylvester bound. A kernel with the right transform and a worse mass gives
   a weaker theorem here — which is why T12 is a roadmap topic rather than a
   lemma.

   `Sylvester/Internal/ReciprocalMultiplier` is where the two meet, and it
   records the sharpness from the other side: **any real certificate has
   coefficient mass at least `5 / 3`, which exceeds `π / 2`.** So the complex
   kernel is not a convenience — a real construction cannot reach the constant.

The strong-continuity estimate in step 1 is the one place with genuine analytic
content, and its module says why:

> Strong continuity of a *bounded* operator flow would be immediate; it is
> Hilbert–Schmidt convergence that has content, because the columns must go to
> zero **together**.

It is carried out in `ℝ≥0∞` deliberately, so the `ε`-split of the energy sum
needs no finiteness side conditions.

## The modules

| Group | Modules | Role |
|---|---|---|
| Finite-dimensional core | `Sylvester/{Basic, Interval, SpectralDistance}` | The Sylvester operator, spectral-separation predicates, injectivity, and the canonical finite-dimensional solution. |
| Quantitative bounds | `Sylvester/Bound`, `CoerciveUnit` | `‖X‖ ≤ ‖Y‖ / (2δ)` for coercive `A`, `B`, and the operator-level Lax–Milgram lemma that makes a coercive operator a unit. |
| Hilbert–Schmidt layer | `HilbertSchmidtBlock`, `Sylvester/{Operator, BlockIdentity, BlockEstimate}` | Two-sided blocks on the Hilbert–Schmidt space; the block identity and its estimate. |
| The flow | `Sylvester/{Group, Generator, SpectralGap}` | Unitarity, strong continuity, generator identification, and the spectral gap. |
| Reciprocal multiplier | `Sylvester/Internal/ReciprocalMultiplier{, .OrbitAction, .Fourier, .DoubledPhase}`, `Sylvester/Internal/SpectralBounds` | Internal: the multiplier realising `1/x` against the T12 kernel. |
| The theorem | `Rosenblum` | The intertwiner vanishes. |

`Sylvester/Bound` is the largest single module (712 lines) and the most
reusable: it is stated for `𝕜 = ℝ, ℂ` and bounds both `A X + X B = Y` and
`A X − X B = Y`, which is what lets T17 use one estimate for both orientations.

## What a reviewer should check

1. **That `1` is null for every diagonal measure** — see decision 1 above. This
   is the load-bearing fact, and it is what replaces the monotone-class argument.

2. **That the generator identification is an identification, not a definition.**
   Stone's theorem produces *a* self-adjoint generator; `Sylvester/Generator`
   proves it equals `Z ↦ A Z − Z B`. If that were definitional the topic would
   prove nothing about Sylvester equations.

3. **That the constant is `π / 2` and comes from T12**, not from an unspecified
   `C`. The sharpness is the point of importing that topic.

4. **`Sylvester/Internal/**` is internal by name and should stay so** — those
   four modules exist to construct the reciprocal multiplier and are not part of
   the topic's public surface.

## Prerequisites

T04 (orthogonal projections and spectral subspaces), T07 (rectangular unitarily
invariant norms), T11 (the Hilbert–Schmidt space — specifically
`HilbertSchmidtConjugation`), T12 (the Haagerup–Zsidó kernel, for the sharp
constant), T13 (Stone's theorem), T15b and T15c (resolvents and the spectral
measure of an unbounded self-adjoint operator).

That is seven prerequisites, more than any other topic — and they are **not**
mutually independent, which is worth stating because it is the first thing one
assumes: `T07` needs `T04`, and `T15c` needs both `T13` and `T15b`. Only `T12`
and `T15b` are independent outright.

So the parallelism the DAG offers here is real but narrower than the count
suggests: `T12` can be submitted at any time, and the `T04 → T07` and
`T13, T15b → T15c` chains can proceed alongside each other, but neither chain
can be collapsed. Checked with `scripts/check_tauceti_roadmap_topics.py --needs`
rather than assumed.
