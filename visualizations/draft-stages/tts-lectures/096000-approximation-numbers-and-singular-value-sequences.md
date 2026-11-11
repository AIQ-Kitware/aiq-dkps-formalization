# 096000 — Approximation numbers and singular-value sequences

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `052000` singular-value min–max, `053000` Eckart–Young, `095000` compactness. **Next:** `097000` Ky Fan dominance in Hilbert space.

<!-- BEGIN SPOKEN LECTURE -->

# How much error must a low-rank approximation leave?

Suppose a matrix stretches four perpendicular directions by amounts four, two, one, and one half. We are allowed to build a replacement matrix whose outputs occupy only one direction. What is the smallest possible error, measured on the worst unit input?

Keeping the direction stretched by four seems sensible. That replacement reproduces the largest effect perfectly and discards the other three. Its worst-case error is two, from the second direction.

Could we do better by rotating our single retained direction, or mixing several directions together? The answer is no. There is a geometric reason, and understanding it will lead us to approximation numbers for operators on infinite-dimensional Hilbert spaces.

## Why a rank restriction forces an error

Start with the diagonal matrix from our opening: its stretching factors are four, two, one, and one half. Think of its four input directions as coordinate axes.

Any rank-one replacement has an output range of dimension at most one. On the plane spanned by the first two coordinate axes, a rank-one map must kill some nonzero vector. This follows because we are mapping a two-dimensional space into at most one dimension.

Normalize that killed vector to norm one. The original diagonal matrix stretches every unit vector in that plane by at least two. But the proposed replacement sends our chosen vector to zero.

Therefore the error between the original matrix and the replacement is at least two on that vector. Since the operator norm is the worst error over all unit inputs, no rank-one replacement can beat an error of two.

And keeping just the first singular direction achieves two. So the best rank-one error is exactly two.

If we allow rank two, retain the directions stretched by four and two. Then the worst neglected direction has stretch one. The best possible error is one. If we allow rank three, it is one half.

The pattern is simple: the price of discarding all but the largest few singular directions is the first stretching factor we discarded.

## Define the approximation numbers

Now let T be any bounded operator between Hilbert spaces. We do not assume T is compact or that we can list its singular vectors.

The first approximation number of T is simply its operator norm. It is the error of approximating T by a rank-zero operator, meaning the zero operator.

The second approximation number is the smallest error achievable by a replacement of rank strictly less than two. In other words, rank at most one.

More generally, the k-th approximation number is the infimum of the operator-norm error between T and R, over all bounded replacement operators R of rank strictly less than k.

Infimum means the best error we can approach. It need not be achieved by a particular replacement for an arbitrary bounded operator.

The indexing can be easy to confuse. Approximation number one permits rank zero. Approximation number two permits rank one. Number k permits rank k minus one.

As k increases, we allow more replacements, so the approximation numbers can only decrease. They are nonnegative and never exceed the operator norm of T. This gives a sequence for every bounded operator, even when it does not have a discrete singular-value list.

## Return to the infinite diagonal example

Consider ell two, the square-summable sequences. Let T multiply its first coordinate by four, its second by two, its third by one, and subsequent coordinates by one half, one quarter, one eighth, and so forth.

We can keep the first k minus one coordinate directions. The largest discarded diagonal coefficient then gives an upper bound on the approximation error.

For the lower bound, take any rank-less-than-k replacement R. Focus on the k-dimensional span of the first k coordinate vectors. R must kill some nonzero vector in that span. On this span, T stretches every vector by at least the k-th diagonal coefficient. So T minus R makes an error at least that large on a suitable unit vector.

Together, these bounds prove that the k-th approximation number is exactly the k-th diagonal coefficient.

This proof is worth remembering. We never need to analyze every possible clever low-rank approximation. A dimension argument produces an input direction that the replacement must miss.

## A geometric minimax description

There is a second way to think about the same quantity.

Instead of choosing a low-rank replacement, choose a subspace of inputs containing fewer than k independent directions. Imagine telling the operator that we will ignore those selected directions and examine its action on the perpendicular complement.

Now measure the worst stretch of T on that complement. Among every choice of fewer than k directions to exclude, find the smallest possible worst stretch. That value is the k-th approximation number.

Why? If M is our selected input subspace, first project onto M and then apply T. That is a finite-rank replacement of rank less than k. The difference from T is precisely T acting on the perpendicular complement.

Conversely, every rank-less-than-k replacement R has a kernel whose perpendicular complement has dimension less than k. On the kernel of R, the approximation error equals T itself. Thus every such replacement has an error at least as large as T restricted to the appropriate complement.

The two descriptions agree. We can optimize over replacement operators, or over the finite number of input directions we choose to remove.

That is the geometric content of a min-max principle.

## Compactness becomes numerical decay

For an operator on infinite-dimensional ell two, the approximation numbers form an infinite sequence. What happens when that sequence approaches zero?

If the k-th approximation number tends to zero, we can find finite-rank replacements of T with arbitrarily small operator-norm error. That is exactly the finite-rank characterization of compactness between Hilbert spaces.

And conversely, if T is compact, finite-rank operators approximate it arbitrarily closely, so its approximation numbers must tend to zero.

Thus compactness is equivalent to decay of approximation numbers.

Our diagonal operator with coefficients one over n is compact: its approximation numbers are one, one half, one third, and so on, tending to zero.

But consider the identity on infinite-dimensional ell two. No matter how high a finite rank we allow, the replacement has a nonzero vector in its kernel. On that unit vector, the identity still acts with norm one. The best possible error is exactly one for every rank limit.

So all approximation numbers of the identity equal one. This is a precise numerical witness that the identity is not compact.

## When approximation numbers become singular values

For a compact operator, there is more structure. Form its adjoint followed by the operator itself, and then take the positive square root. This positive operator is called the modulus of T.

The modulus of a compact operator is itself compact. The compact self-adjoint spectral theorem lets us list its positive eigenvalues in descending order, repeating each according to multiplicity. These eigenvalues are the singular values of T.

Truncating to the first k minus one singular directions gives an approximation with error equal to the k-th singular value. The same kernel-and-dimension argument supplies the matching lower bound.

So for compact operators, approximation numbers and singular values are the same list, with the natural indexing adjustment if a formalization starts counting at zero.

For a general noncompact operator, the approximation numbers still make sense. But we must not assume they are a list of isolated eigenvalues of its modulus. The identity, for example, retains approximation number one forever. More complicated operators can have continuous spectrum rather than discrete singular directions.

## Why these numbers are stable

Suppose S is a second operator and the operator-norm difference between S and T is at most one hundredth. Any rank-constrained approximation to T is also an approximation to S, with at most one hundredth of additional error. Reverse the argument, and we find that the k-th approximation numbers of S and T differ by no more than one hundredth.

The key point is that this bound is independent of k. A small operator-norm perturbation cannot move any single approximation number by much.

There is another useful estimate. If we put bounded operators before and after T, the approximation number of the resulting composition is at most the corresponding approximation number of T multiplied by the operator norms of those two surrounding maps.

Why? Start with a low-rank approximation R of T. Composing R with bounded maps cannot increase its rank. And the error of the composed approximation is bounded by the usual product-of-norms inequality.

This makes approximation numbers well suited to estimates involving projections, coordinate changes, and operator compositions.

## The picture to retain

For our diagonal matrix, a rank-one approximation cannot hide from the second-largest stretching direction. The same dimension argument works in an infinite Hilbert space, one finite-dimensional test plane at a time.

Approximation numbers answer a concrete question: how accurately can we reproduce an operator while allowing fewer than k independent output directions? Their decay characterizes compactness. For compact operators, the answer is encoded by singular values.

Once we have the entire sequence, we can compare operators through the sum of their largest few approximation numbers. Those finite sums are powerful even when an infinite trace or ideal norm would diverge.

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
