# Roadmap: principal angles, aligned bases, and finite frames

**Topic T06 of the candidate design.** Three modules, 1,284 lines, of which 837
are `PrincipalAngles`. Depends on T03, T04, T05. Consumed by T07, T08 and T17.

## The definitional choice this topic makes

The cosines of the principal angles are defined as **singular values of an
overlap operator**, not by the usual recursive variational construction:

```lean
noncomputable def cosPrincipalAngles {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  (overlapOp hu hv).singularValues
```

where `overlapOp hu hv` is the operator with matrix `⟪uᵢ, vⱼ⟫`. That choice is
what makes the basic facts cheap — nonnegativity, `≤ 1`, decreasing order and
symmetry in `u, v` are all inherited from singular values, the last because
`overlapOp` and its adjoint swap the two families — and it is why this topic
depends on T03.

The variational definition would make the same four facts into four separate
inductive arguments. A reviewer comparing against a textbook should expect the
recursion to be *absent*, not hidden.

## The thing to know before submitting this topic alone

**`cosPrincipalAngles` is indexed by orthonormal *families*, not by subspaces.**
Its arguments are `hu : Orthonormal 𝕜 u` and `hv : Orthonormal 𝕜 v`, so as
stated it is an invariant of the chosen families. The name says "principal
angles", which is a property of the two *subspaces*.

Those agree, and the theorem saying so exists — but it is **in T08, not here**:

```lean
-- ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean  (topic T08)
theorem principalCosines_span_eq_cosPrincipalAngles {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    principalCosines (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) =
      cosPrincipalAngles hu hv
```

T08 defines `principalCosines U V` for *submodules*, as the singular values of
`P_V P_U`, and proves the two notions coincide. So the statement that makes this
topic's central definition well-named is one topic downstream of it.

That is invisible while both ship together and matters if T06 is submitted
first: read alone, this topic defines a family invariant and calls it an angle
between subspaces. The four facts it proves (`nonneg`, `le_one`, `antitone`,
`comm`) are all true of the family invariant and none of them is the
independence statement.

**This is a placement question, not a soundness one** — nothing here is wrong,
and T08's theorem is a real proof rather than a definitional convenience. But a
reviewer of T06 alone should be told that the invariance lives next door, and
the roadmap is the place to tell them.

## The three modules

| Module | Role |
|---|---|
| `FiniteFrame` | For a finite family `v : ι → E`: the analysis map `x ↦ (⟪vᵢ, x⟫)ᵢ`, the synthesis map `c ↦ ∑ cᵢ • vᵢ`, and the two adjoint products — the frame operator on `E` and the Gram operator on coefficient space. |
| `AlignedBasis` | The isometry `familyIsometry hv : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E`, `eⱼ ↦ vⱼ`. Its adjoint recovers coordinates, so `(familyIsometry hu)⋆ ∘ (familyIsometry hv)` **is** the overlap operator. |
| `PrincipalAngles` | The angles themselves, plus `sinThetaSq` and the Frobenius identity below. |

The order is a construction, not a filing convention: `FiniteFrame` gives the
analysis/synthesis pair, `AlignedBasis` packages an orthonormal family as an
isometry from coordinate space, and the overlap operator is then literally a
composite of two of those — which is why `overlapOp`'s adjoint is the swap, and
hence why `cosPrincipalAngles_comm` is immediate.

## The identity T17 uses

```lean
theorem sinThetaSq_eq_sub_overlap ... :
    sinThetaSq hu hv = (d : ℝ) - ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2
```

with `sinThetaSq hu hv = ∑ k, (1 - cos²)`. This is `‖sin Θ‖²_F = d − overlap`:
the squared Frobenius sine is `d` minus the total overlap mass. It converts a
statement about angles into a statement about inner products, which is the form
the perturbation estimates are proved in.

## What a reviewer should check

1. **That the recursion is absent** — the angles are singular values, and the
   four basic facts are inherited rather than re-proved. If any of them has an
   inductive proof, the definitional choice is not paying.

2. **That `overlapOp` really is the composite of the two aligned isometries**,
   since `cosPrincipalAngles_comm` rests on `overlapOp_adjoint` being the swap.

3. **The family-vs-subspace point above**, if reviewing T06 in isolation.

## Prerequisites

T03 (singular values), T04 (projections and spans), T05 (for the norms the
downstream estimates are stated in).
