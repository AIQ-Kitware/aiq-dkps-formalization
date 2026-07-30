# Roadmap: rectangular unitarily invariant norms

**Topic T07 of the candidate design.** Six modules. Depends on T03, T04, T05,
T06. Consumed by T08, T09, T16 and T17.

## The theorem this topic exists for

Every *"for every unitarily invariant norm"* statement in the development rests
on this pair:

```lean
theorem mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le  -- Ky Fan ⇒ orbit hull
theorem apply_le_of_mem_convexHull_twoSidedUnitaryOrbit     -- orbit hull ⇒ every norm
theorem apply_le_of_kyFanSum_le                             -- the composite
```

A map whose Ky Fan sums are dominated by another's lies in the convex hull of
that other's two-sided unitary orbit, and therefore has the smaller value under
**every** rectangular unitarily invariant norm.

That is the whole economy of the topic. The Davis–Kahan estimates are proved
*once*, as a Ky Fan domination, and `apply_le_of_kyFanSum_le` turns that single
proof into a statement about the operator norm, the Frobenius norm, every Ky Fan
norm, the nuclear norm, and any norm a reader supplies. Without it each theorem
would be proved per norm, or stated only for one.

## The structure is deliberately minimal

```lean
structure RectangularUnitarilyInvariantNorm (𝕜 E F : Type*) ... where
  toFun     : (E →ₗ[𝕜] F) → ℝ
  add_le'   : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul'     : ∀ (a : 𝕜) A, toFun (a • A) = ‖a‖ * toFun A
  invariant': ∀ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) A,
                toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A
```

Three laws — subadditive, absolutely homogeneous, invariant under isometries on
**both** sides. Note what is *not* there: no positivity, no definiteness, no
normalisation. Anything derivable is derived, so a consumer supplying a norm has
three obligations rather than six.

The two-sidedness is the "rectangular" part: `E` and `F` are independent spaces
with independent isometry groups, which is what lets the theory apply to
non-square maps at all.

## Where T05's separation pays off

`Majorization.lean` says outright that **the majorization step is not proved
there**:

> The two-sided unitary orbit's convex hull pulls back along a diagonal lift to a
> `FiniteVector.IsSymmetricConvex` set of coordinate vectors — coordinate swaps
> and single-coordinate sign changes are two-sided unitary actions — so the
> Hardy–Littlewood–Pólya transfer descent
> `FiniteVector.IsSymmetricConvex.mem_of_prefixSum_le` applies directly. What
> remains here is the operator-theoretic half: the lift, the extension of
> coordinate unitaries to the ambient spaces, and the transport of equal
> singular-value data by the rectangular SVD.

This is the payoff of the decision documented in **T05**, where the combinatorial
engine `Analysis/Convex/Majorization` is kept free of any Hilbert space. Because
it is free of them, T07 can *pull back to it* rather than re-derive a transfer
argument in the operator setting. The two halves meet at exactly one place — the
diagonal lift — and each half is reviewable without the other.

A reviewer should check that this is really the division claimed: that
`Majorization.lean` contains no combinatorial induction, only the lift, the
extension of coordinate unitaries, and the SVD transport.

## The four-way split is submission-driven

`RectangularUnitarilyInvariantNorm.lean` is a **32-line aggregate** that imports
four modules and nothing else. Its own docstring gives the reason: the theory is
split *"so that each stays under Tau Ceti's file-length ceiling; importing this
name gives the whole theory, exactly as before the split."*

| Module | Lines | Content |
|---|---|---|
| `Basic` | 462 | The structure, Ky Fan sums, the two-sided unitary orbit with finiteness certificates, transport along an isometry. |
| `BlockSum` | 412 | Block-diagonal sums, their singular values and Ky Fan sums, and the majorization statements that transfer. |
| `Instances` | 575 | The concrete norms — operator, Frobenius, Ky Fan, nuclear — plus adjoint transport, composition bounds, zero extension, and the bridges to and from square `UnitarilyInvariantNorm`. |
| `Majorization` | 539 | The engine above. |

This is the one topic whose file boundaries are set by a **submission
constraint** rather than by subject. Worth stating plainly so a reviewer does
not look for a mathematical reason the theory is in four pieces, and so the
aggregate is understood as a compatibility entry point rather than a fifth idea.

`TwoDimensionalSingularValues` sits outside that split: it supplies planar
sharpness models — the reductions comparing a Gram operator with a real diagonal
operator, and the symmetric off-diagonal and one-sided rank-one corollaries.
Those are what sharpness claims elsewhere are witnessed by, and they are
two-dimensional because that is where a sharpness witness lives.

## What a reviewer should check

1. **That the structure has exactly three laws**, and that positivity and
   definiteness are derived rather than assumed — a consumer's obligation count
   is the practical measure of whether the abstraction is worth having.
2. **That `Majorization.lean` contains no combinatorics**, per the division
   above; if it does, T05's separation is not buying what it claims.
3. **That the split is only a split** — the aggregate should import four modules
   and add nothing.

All three hold as of 2026-07-30: the aggregate is 4 imports and **0**
declarations; `Majorization.lean` contains **0** occurrences of `induction`,
confirming the combinatorics really is in T05; and `nonneg` is a `theorem` in
`Basic.lean`, not a structure field. They are listed as checks rather than as
facts because they are the properties that would silently stop holding — an
extra declaration in the aggregate, or one induction sneaking into
`Majorization`, would not break any build.

## Prerequisites

T03 (singular values), T04 (projections), T05 (the majorization engine and the
square UI norms it bridges to), T06 (principal angles, for the geometry the
estimates are stated in).
