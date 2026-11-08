# Hilbert spaces and orthogonal complements

<!-- BEGIN SPOKEN LECTURE -->

An inner product supplies lengths and angles. Perpendicular vectors have inner product zero, and the squared length of their sum is the sum of their squared lengths. A Hilbert space is a complete inner-product space, and the geometry of its closed subspaces follows from these facts.

Today we ask what happens when there are infinitely many possible directions. We will build the idea of a Hilbert space, distinguish a span from a closed span, and define the collection of all vectors perpendicular to a given subspace. These distinctions will determine when the geometry of finite-dimensional Euclidean space survives in infinite dimensions.

## Completing Euclidean geometry

Start with an inner-product space. We can add and scale vectors. We can measure lengths using the square root of the inner product of a vector with itself. We can measure distance by taking the norm of a difference. And we can talk about convergence: a sequence of vectors approaches x when the distances to x approach zero.

But the rules for inner products do not guarantee that every Cauchy sequence has a limit inside the space. Recall that a Cauchy sequence is one whose late terms get arbitrarily close to each other. A Hilbert space is simply an inner-product space that is complete for its inner-product norm. It combines Euclidean geometry with the guarantee that Cauchy approximations have limits.

All ordinary real and complex coordinate spaces of finite dimension are Hilbert spaces. The distinction matters much more in infinite dimensions. There we can have an inner-product space with all the geometric identities we expect, but missing the limit of a sequence we can construct inside it.

## An infinite coordinate vector

Think about a vector whose coordinates continue forever. We cannot permit every infinite sequence, because the sum of its squared coordinate magnitudes might diverge. Instead, consider sequences for which that sum is finite. Call this space ell two, the space of square-summable sequences.

The first coordinate vector has a one in the first position and zero everywhere else. The second has a one in the second position and zero everywhere else. Continue this way. Each coordinate vector has length one, and any two distinct coordinate vectors are perpendicular.

Now consider the infinite vector whose coordinates are one, one half, one third, one fourth, and so on. Its squared length is the sum of one over n squared, starting at n equal to one. That sum converges, so the vector belongs to ell two. You do not have to know its exact value to see convergence. For n at least two, one over n squared is no larger than one over n times n minus one. The latter terms form a telescoping series with a finite sum.

Compare that with the infinite sequence whose every coordinate is one. Its squared length would be one plus one plus one forever. It is not a vector in ell two.

In this setting the inner product multiplies matching coordinates, conjugating the first factor in the complex case, and sums the products. Cauchy–Schwarz guarantees that the sum defining the inner product converges. So ell two is not just an informal picture of infinitely many coordinates. It has well-defined lengths and inner products.

## Why ell two is complete

Let us examine the hardest part of calling ell two a Hilbert space: completeness.

Suppose we have a sequence of ell-two vectors, each of which is itself an infinite list of coordinates. Assume that, as whole vectors, they form a Cauchy sequence in the ell-two norm.

Look only at the first coordinate. Its difference between two vectors is no larger in magnitude than the norm of their whole-vector difference. So the first coordinates form a Cauchy sequence of scalars and have a limit. The same argument works for the second coordinate, the third, and each later coordinate.

These coordinatewise limits give us a candidate infinite vector. But two questions remain. Does this candidate have a finite squared length? And do our original vectors converge to it in the ell-two norm, rather than merely coordinate by coordinate?

Here the whole-vector Cauchy bound does the work. Cauchy sequences are bounded, so the squared norms of our vectors are bounded by some fixed number. Take any finite number of coordinates and pass to their limits. The sum of their squared magnitudes cannot exceed that fixed bound. Since this holds for every finite initial segment, the entire infinite sum is finite. Our candidate really belongs to ell two.

Next, fix an error tolerance and choose a late vector in the Cauchy sequence. Every still-later vector differs from it by less than that tolerance in norm. If we restrict the difference to the first hundred coordinates, the same bound holds. Pass to the coordinatewise limit, and it still holds. Because the bound works for every finite initial segment, it holds for the whole infinite sum. Thus the chosen late vector is close to the candidate limit in ell-two norm.

That proves convergence. Ell two is complete. Notice how much work the full norm did: coordinatewise convergence alone would not be enough. For example, the successive coordinate unit vectors approach zero in each fixed coordinate, while every one of them remains at distance one from the zero vector.

## Span versus closed span

Now we can see a second distinction. Take all the coordinate unit vectors in ell two. What vectors can we make by taking finite linear combinations of them?

Exactly the sequences with only finitely many nonzero coordinates. That is their ordinary linear span. It does not contain our vector with coordinates one, one half, one third, and so on, because that vector has infinitely many nonzero coordinates.

Nevertheless, we can approximate the vector by cutting off the tail. Keep the first ten coordinates and replace everything after them by zero. Keep the first hundred. Keep the first thousand. The squared error is the sum of the squared magnitudes of the omitted coordinates, and those tails approach zero.

So the vector is not in the span, but it is in the closure of the span. The closure adds every vector that can be reached as a norm limit of vectors from the span. In ell two, the closed span of all the coordinate unit vectors is the entire space.

This gives us two notions we must keep separate: a linear combination uses only finitely many terms, while a limit of finite linear combinations may use arbitrarily many terms in the approximation process. In infinite-dimensional analysis, the closed span is often the natural geometric object.

## What does perpendicular mean for a whole subspace?

In the plane, two vectors are perpendicular when their inner product is zero. For a subspace M, define its orthogonal complement, pronounced M perp, to be all vectors that are perpendicular to every vector in M.

Take ordinary three-dimensional space. If M is the horizontal plane, then M perp is the vertical axis. If M is just the horizontal x-axis, then M perp is the entire plane of directions with zero x-coordinate. The complement means every perpendicular direction, not necessarily a single normal vector.

Why is M perp itself a subspace? If u and v are each perpendicular to every member of M, any linear combination of u and v is too, by the linearity rules of the inner product. The zero vector is also perpendicular to everything.

More importantly, M perp is closed, even when M is not closed. To see why, take a convergent sequence of vectors, all in M perp. Fix any m in M. Every vector in our sequence has inner product zero with m. The inner product is continuous, as follows from Cauchy–Schwarz, so the limit has inner product zero with m as well. Since we could choose any m, the limit is in M perp.

This argument is small but powerful. Orthogonality to a fixed vector is a continuous condition. Requiring it for every vector in a subspace is still preserved under limits.

## What orthogonal complements can and cannot distinguish

Consider the finitely supported sequences in ell two. They form a dense, nonclosed subspace. What vectors are perpendicular to every finitely supported sequence?

If a vector is perpendicular to the first coordinate unit vector, its first coordinate is zero. If it is perpendicular to the second, its second coordinate is zero. Continuing, all coordinates must vanish. Its orthogonal complement contains only zero.

The whole space ell two also has orthogonal complement equal to zero. So two different subspaces can have the same orthogonal complement: the finitely supported sequences and their closure, which is ell two.

This is not a flaw in the definition. It tells us that orthogonality cannot distinguish a subspace from its closure. Indeed, the vectors perpendicular to M are exactly the vectors perpendicular to its closed span.

There is an important converse that we will prove after the projection theorem: the orthogonal complement of the orthogonal complement of M is precisely the closure of M. For a closed subspace, taking the orthogonal complement twice returns the original subspace.

## Orthogonal families and completeness of a family

An orthonormal family consists of vectors of length one that are pairwise perpendicular. For any finite selection from such a family, Pythagoras says that the squared norm of a linear combination is the sum of the squared magnitudes of its coefficients. This immediately explains why no nontrivial finite combination of orthonormal vectors can vanish.

But an orthonormal family need not fill the space. In ell two, take only the coordinate vectors in the even-numbered positions. They remain orthonormal. Every odd coordinate direction is perpendicular to all of them. Their closed span is only part of ell two.

People sometimes say that an orthonormal system is complete when its closed span is the entire Hilbert space. This meaning of complete describes the family, not whether the ambient space is a Hilbert space. Keep the two meanings separate. Ell two is complete as a space regardless of which orthonormal family we choose inside it.

Try reconstructing three arguments. First, why do coordinatewise limits alone not prove convergence in ell two? Second, why is the orthogonal complement of any subspace closed? Third, why do finitely supported sequences have the same orthogonal complement as all of ell two?

For every closed subspace M of a Hilbert space and every x, the projection theorem supplies a unique closest vector in M, with error perpendicular to M. This decomposes x into the sum of its projected and orthogonal parts.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For a complex Hilbert space, one model is
\[
\ell^2=\left\{x=(x_n)_{n\ge1}:\sum_{n\ge1}|x_n|^2<\infty\right\},\qquad
\langle x,y\rangle=\sum_{n\ge1}\overline{x_n}y_n.
\]
For a subspace \(M\le H\),
\[
M^\perp=\{x\in H:\langle m,x\rangle=0\ \text{for all }m\in M\},\quad
M^\perp=(\overline M)^\perp,\quad
(M^\perp)^\perp=\overline M.
\]
The final identity is used after developing orthogonal projection in lesson `011000`.

**Actual Lean source connection.** In `ForTauCeti/Analysis/InnerProductSpace/Basic.lean`, the project expands inner products of finite linear combinations. The declaration begins:

```lean
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
```

The notation `ι →₀ 𝕜` is a finitely supported family of coefficients. It expresses the **algebraic** span side of our distinction. `Finsupp.linearCombination` constructs the finite sum of scaled vectors. On the right, `a.sum` and `b.sum` perform finite sums, while `starRingEnd` conjugates the first coefficient when needed. Thus the Lean statement is precisely the finite-dimensional Gram expansion \(\langle\sum_i a_iv_i,\sum_j b_jv_j
angle=\sum_{i,j}\overline{a_i}b_j\langle v_i,v_j
angle\). `E` is the ambient inner-product space, `v` is the indexed vector family, and `𝕜` is the real or complex scalar type.

For a preview of the **geometric** structure, `ForTauCeti/Analysis/InnerProductSpace/OrthogonalFamilyGluing.lean` has the checked declaration `exists_linearIsometryEquiv_of_orthogonal_blocks`. It uses an `OrthogonalFamily`, the supremum `⨆ i, W i` of subspaces, and the condition `(...)=⊤` that the summands span the entire ambient space. Its additional conclusions concern gluing isometries and belong to later lessons. The symbols `W i` describe actual subspaces, not individual vectors.

**Source and provenance.** Both declarations and their names are present in the supplied DKPS source snapshot. The first concerns finite support; the second uses the language of orthogonal sums. The donor headers identify DKPS-origin contributions, including material reorganized for TauCeti. No new Lean declarations were compiled for this lecture.
