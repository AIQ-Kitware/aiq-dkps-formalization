# 096000 — Approximation numbers and singular-value sequences

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `052000` singular-value min–max, `053000` Eckart–Young, `095000` compactness. **Next:** `097000` Ky Fan dominance in Hilbert space.

<!-- BEGIN SPOKEN LECTURE -->

# The price of losing dimensions

Imagine compressing an operator into a map with only a limited number of independent output directions. How accurately can you reproduce its behavior on every unit input?

For a finite matrix, the Eckart–Young theorem answered that question: keep its largest singular directions and discard the rest. In an infinite-dimensional Hilbert space, we can define the same approximation problem without assuming an infinite singular-value decomposition exists.

The approximation numbers are the optimal errors of that rank-constrained problem. We will derive their basic properties and then see why compactness turns them into a genuine singular-value sequence.

## A definition that always makes sense

Let T be a bounded operator from E to F. Define a sub one of T to be the norm of T. For every positive integer k, define a sub k of T to be the infimum of the operator norms of T minus R, taken over operators R having rank strictly less than k.

So a sub one uses rank zero competitors: only the zero map is allowed, and the error is the norm of T. For a sub two, rank-one maps are permitted. For a sub three, rank at most two, and so on.

To avoid an off-by-one error, number approximation values consistently: the first is the best rank-zero approximation error, the second uses rank at most one, and so forth. A different zero-based index convention describes the same sequence after shifting indices.

Because each new rank limit admits all competitors from the previous stage, the sequence is nonincreasing. Because norms are nonnegative, every approximation number is nonnegative. And since the zero map is always an admissible competitor, no approximation number exceeds the norm of T.

Already this gives us a bounded, nonincreasing sequence for every bounded operator, compact or not.

## The diagonal calculation

Consider a diagonal operator on ell two with coefficients four, two, one, one half, one quarter, and so on. Its largest singular directions are the coordinate axes.

If we retain the first k minus one coordinates, the remaining diagonal tail has norm equal to the k-th coefficient. Thus a k is at most that coefficient.

For the reverse inequality, take any competitor R of rank less than k. On the k-dimensional span of the first k basis vectors, R must have a nonzero kernel vector. Normalize that vector to unit length.

On this span, the original diagonal operator has norm at least the k-th coefficient times the norm of every vector. Our chosen vector is killed by R, so the error T minus R on that vector has norm at least the k-th coefficient. This holds for every competitor R.

Thus a k is exactly the k-th diagonal coefficient.

The proof is the infinite-dimensional version of the dimension-intersection argument behind Courant–Fischer and Eckart–Young. It uses only a finite-dimensional subspace at each rank.

## A minimax characterization

The same argument suggests another description: a sub k of T equals the infimum, over all subspaces M of dimension strictly less than k, of the norm of T restricted to the orthogonal complement of M.

For the easy direction, choose the orthogonal projection P onto M. The operator T P has rank less than k, and the error T minus T P is T followed by projection onto the complement. Its norm is exactly the norm of T restricted to that complement.

For the converse, take any rank-less-than-k map R. Its kernel has codimension at most k minus one. Therefore we can find a subspace of that small codimension on which R vanishes. On that subspace, T minus R equals T, so the approximation error is at least the corresponding restriction norm.

This is one way to understand the min–max principle without invoking an eigenbasis.

There is a mild technical point: one can choose the orthogonal complement of the kernel, which has dimension no larger than the rank of R, and then use the kernel itself as the remaining large subspace. Hilbert-space orthogonal decomposition makes this formulation precise.

## Why compactness is equivalent to decay

A bounded operator is compact precisely when it is a norm limit of finite-rank maps, in the Hilbert-space setting considered here.

If T is compact, then for every epsilon there is a finite-rank R within epsilon of T. Let its rank be r. For every k greater than r, R is an admissible competitor, so a sub k of T is smaller than epsilon. Thus the approximation numbers tend to zero.

Conversely, suppose a sub k tends to zero. By the definition of an infimum, for each desired positive error we can choose a sufficiently large k and a rank-less-than-k operator R whose distance to T is below that error. Therefore T is a norm limit of finite-rank maps and is compact.

So the decay of approximation numbers is exactly the compactness criterion, not just a consequence of it.

For the identity on infinite-dimensional ell two, every a sub k equals one. A finite-rank R has a nonzero unit vector in its kernel, and the identity minus R acts as the identity on that vector. The zero competitor gives the matching upper bound.

This supplies a numerical signature for noncompactness.

## Connecting approximation numbers to eigenvalues

Suppose now that T is compact. Its Gram operator, T adjoint T, is positive and compact. The positive square root, called the modulus of T, is also compact. The compact self-adjoint spectral theorem provides orthonormal singular directions with nonzero singular values decreasing to zero, repeated according to multiplicity.

Truncating to the first k minus one singular directions gives a rank-less-than-k approximation with error equal to the k-th singular value. A dimension argument gives the reverse inequality. Hence our approximation number a sub k agrees with the k-th singular value.

This statement includes multiplicity: if a singular value occurs three times, it occupies three consecutive positions. It also includes zeros after the rank when T has finite rank.

For general bounded noncompact operators, the approximation sequence is still defined, but it may not be the enumeration of eigenvalues of the modulus. The identity illustrates this: its modulus has eigenvalue one of infinite multiplicity, and the approximation numbers stay one. Multiplication operators may have continuous spectral values and no suitable discrete singular-vector list at all.

## Two stability estimates

First, approximation numbers are stable under operator-norm perturbation. For any fixed rank bound and any competitor R, the triangle inequality gives the distance from S to R at most the distance from T to R plus the norm of S minus T. Taking infima proves a sub k of S is at most a sub k of T plus the perturbation norm. Exchanging S and T yields the absolute difference bound.

Second, bounded maps on either side cannot increase an approximation number by more than their operator norms. If R approximates T with small rank, then A R B approximates A T B; its rank is no greater, and its error is bounded by the product of the three operator norms. Taking infima gives the ideal estimate.

This will allow singular-value estimates to survive orthogonal projections, coordinate embeddings, and partial-isometry transport.

## From approximation numbers to Ky Fan gauges

A single approximation number measures the best rank-constrained error. A sum of the first several approximation numbers measures accumulated size in leading directions.

Those sums are the infinite-dimensional Ky Fan gauges.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For k at least one, define a_k(T) as the infimum of operator norm of T minus R over rank R less than k. The Lean `singularValue n` is zero-indexed; a_{n+1}(T) corresponds to `T.singularValue n`. The a_k are decreasing and nonnegative; T is compact if and only if a_k(T) tends to zero. The Hilbert-space min–max description is inf over subspaces of dimension less than k of the norm of T restricted to their orthogonal complements. For a compact operator these are the singular values of its modulus, counted with multiplicity.

### Actual Lean source declarations

`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean` — `approximationNumber_le_of_spectral_band` (declaration header, proof omitted):

```lean
theorem approximationNumber_le_of_spectral_band [CompleteSpace F₁]
    {T : E₁ →L[𝕜] F₁} {P : E₁ →L[𝕜] E₁} {r : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hidem : IsIdempotentElem P) (hsa : IsSelfAdjoint P)
    (hrank : P.rank ≤ (r : Cardinal))
    (hband : ∀ x : E₁, ‖T (x - P x)‖ ≤ δ * ‖x - P x‖) :
    (T.singularValue r : ℝ) ≤ δ := by
```

`DavisKahan/OperatorIdeal/ApproximationNumbers/FiniteSourceSingularSystem.lean` — `approximationSingularValue_eq_finiteSourceSingularValue` (declaration header, proof omitted):

```lean
theorem approximationSingularValue_eq_finiteSourceSingularValue
    [CompleteSpace F]
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    (A.singularValue i : ℝ) = finiteSourceSingularValue A i := by
```

**Type and hypothesis map.** The index `r` is zero-based, and `hrank` bounds the projection rank. The hypothesis `hδ` must explicitly assert nonnegativity. For finite-dimensional source, approximation singular values match the singular system; this does not postulate such a discrete system for arbitrary bounded operators.

These are exact excerpts from the supplied DKPS source snapshot. The mathematical narration develops its arguments independently; citing these declarations does not assert that the narrated intermediate proof has been separately compiled in Lean. Where the current declaration lives in `ForTauCeti`, its placement does not imply the mathematical result originated outside the DKPS project.
