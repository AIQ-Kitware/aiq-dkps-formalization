# Roadmap: polar decomposition and partial isometries

**Topic T02 of the candidate design.** Six modules. Depends on T01 (positive
square root, operator modulus, functional calculus). T03, T05, T08 and T13
consume it.

## The theorems this topic exists for

Every operator factors as an isometric part times its modulus. That statement
appears **twice**, in two genuinely different forms, and the first thing a
reviewer will ask is why:

```lean
-- finite-dimensional, RCLike scalars, endomorphism, genuine unitary
theorem exists_polar_decomposition_unitary (A : E →ₗ[𝕜] E) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ abs A
```

```lean
-- complete, ℂ only, rectangular, partial isometry
noncomputable def polarPartial (M : E →L[ℂ] F) : E →L[ℂ] F
-- with polarInitial M the closure of the range of the modulus,
-- polarPartial isometric on it and zero on its complement
```

## Why both, and why neither subsumes the other

This is the question to answer before a reviewer asks it. The two decompositions
differ on **three** axes, not one, and each direction of generalisation loses
something:

| | `PolarDecomposition` | `PolarPartialIsometry` |
|---|---|---|
| scalars | `[RCLike 𝕜]` — **ℝ and ℂ** | **ℂ only** |
| dimension | `[FiniteDimensional]` | `[CompleteSpace]` — infinite allowed |
| shape | `E →ₗ[𝕜] E`, endomorphism | `E →L[ℂ] F`, **rectangular** |
| isometric factor | genuine **unitary** `E ≃ₗᵢ[𝕜] E` | **partial** isometry |

So the general one is not a strict generalisation: it cannot be instantiated at
`𝕜 = ℝ`, and it yields a partial isometry where the finite-dimensional statement
yields a unitary. Conversely the finite-dimensional one cannot reach a
rectangular operator or an infinite-dimensional space.

**The obstruction is upstream of this topic, in T01.** The two moduli have
complementary limitations:

* `LinearMap.IsPositive.sqrt` (`PositiveSqrt`) is `RCLike`-generic but built
  from the spectral theorem, hence finite-dimensional;
* `ContinuousLinearMap.modulus` (`OperatorModulus`) is `CFC.sqrt (T⋆ ∘L T)`,
  which is infinite-dimensional but registered only for `𝕜 = ℂ`, because the
  C⋆-algebra instances on `E →L[𝕜] E` exist only there.

There is no modulus that is both, so there is no single polar decomposition that
is both. Confirmed independently by the `MODULUS-DEDUP` lane (2026-07-30), which
examined merging the two moduli and declined: *different shape and different
field*. The two polar files are the same decision one level up.

`PolarDecomposition` and `PolarPartialIsometry` do not import each other. Their
only shared dependency is `PartialIsometry`, which is where the common notion
lives.

## Statement of the objects

```lean
-- a partial isometry in a star-monoid: `u * star u * u = u`
-- equivalently `star u * u` is a projection
```

`PartialIsometry` states the notion algebraically rather than geometrically, so
that it applies to both settings above without a dimension or scalar hypothesis.
The geometric characterisation — `u` restricts to an isometry on `(ker u)ᗮ` and
vanishes on `ker u` — is a theorem there, not the definition.

That choice is what lets the rest of the topic share one vocabulary across the
finite/infinite and ℝ/ℂ split described above.

## The modules

| Module | Role |
|---|---|
| `PartialIsometry` | The star-monoid notion and its geometric characterisation. The shared vocabulary. |
| `PolarDecomposition` | Finite-dimensional, `RCLike`: `A = U ∣A∣` with `U` unitary; `U = A ∣A∣⁻¹` when `A` is invertible. |
| `PolarIsometry` | The **bounded-below** case: when `∣M∣` is invertible the polar factor is an isometry outright, with no partiality. The intermediate rung. |
| `PolarPartialIsometry` | The general bounded case over `ℂ`, with `polarInitial` — the initial space — proved equal to `(ker M)ᗮ`. |
| `NearIsometry` | Quantitative variant: if the quadratic form of `M` is uniformly `δ`-close to the identity (`δ < 1`), then `M = W ∘ S` with `W` a genuine isometry equivalence and `S` a square root of the Gram operator. |
| `IntertwiningUnitary` | Davis's canonical unitary between two complete orthogonal families of projections. |

`PolarIsometry` is worth keeping separate from `PolarPartialIsometry` even
though the latter is more general: bounded-below is the hypothesis the
Davis–Kahan estimates actually have, and under it the conclusion is stronger
(an isometry, not a partial one). Collapsing the two would force every consumer
to re-derive that strengthening.

`NearIsometry` is the one module that is not about exact factorisation. It is
the finite-dimensional real statement that a *nearly* isometric map is a genuine
isometry composed with something near the identity, which is what a perturbation
argument needs and what the exact decompositions cannot give.

## A module that arrived here from T13

`IntertwiningUnitary` was listed under T13 (Stone's theorem) until 2026-07-30.
It does not belong there: it has zero occurrences of `OneParameterUnitaryGroup`,
`Stone` or `generator`, it is finite-dimensional where T13 is not, and its only
`ForTauCeti` import is `PolarDecomposition` — this topic. "Unitary" was the
whole of what it had in common with Stone's theorem.

It is a polar construction:
`U Pⱼ = (P'ⱼ Pⱼ P'ⱼ)^{-1/2} P'ⱼ Pⱼ = P'ⱼ (Pⱼ P'ⱼ Pⱼ)^{-1/2} Pⱼ`, with
`U Pⱼ = P'ⱼ U` — the modulus-inverse-times-operator shape of this topic, applied
to a pair of projection families. Its only consumer is
`DavisKahan/Sources/Davis1963/RotationBound.lean`.

The reassignment removed a dependency edge that existed only because of it:
**T13 was reported as needing T02 solely through this module**, and is now
independent.

## What a reviewer should check

1. **That the two polar decompositions are not redundant** — the table above,
   and specifically that the general one is ℂ-only. If it were `RCLike` the
   finite-dimensional file would be deletable.

2. **That `PartialIsometry` is stated algebraically**, so the shared vocabulary
   really is shared and not two notions with one name.

3. **That `polarInitial M = (ker M)ᗮ`** is proved rather than taken as the
   definition of the initial space — it is the content of the general
   decomposition.

## Prerequisites

T01, for both moduli. Nothing else.
