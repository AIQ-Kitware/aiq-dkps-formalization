# 056000 — Convexity and majorization descent

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `055000` majorization and weak majorization; `054000` Ky Fan inequalities; elementary convexity of real-valued functions. **Next:** Schatten and Frobenius norms.

<!-- BEGIN SPOKEN LECTURE -->

# Why spreading mass controls convex measurements

Last time, we learned how to compare two sorted lists by adding their largest entries. One list is weakly majorized by another when all of its leading partial sums are no larger. If the full totals also agree, we call the relation ordinary majorization.

Today we will explain why that ordering controls many measurements beyond prefix sums. The mechanism is convexity. When we average different arrangements of the same data, a convex measurement cannot increase. And when we decrease the sizes of coordinates, an appropriate absolute-value-invariant measurement cannot increase either.

Our main theorem says that weak majorization of nonnegative sorted lists implies an inequality for every convex gauge that is invariant under coordinate permutations and sign changes. We will build enough of the proof to see exactly where each hypothesis enters.

## Convexity as a usable inequality

Take a function F on a finite-dimensional real vector space. It is convex if, for any two vectors u and v and any number t between zero and one, the value of F at the weighted average of u and v is no larger than the same weighted average of F at u and F at v.

One simple example is Euclidean length. Averaging two vectors cannot produce a length greater than the corresponding average of their lengths. That is a form of the triangle inequality.

Another example is the sum of the squares of the coordinates. That function is convex too, although it is not itself a norm, because scaling by two multiplies it by four rather than two.

A third example is the largest absolute coordinate. This is convex because the largest absolute coordinate of an average is no greater than the average of the two largest absolute coordinates.

The only convexity inequality we need immediately involves a vector and one of its rearrangements.

## What symmetry contributes

Call a measurement symmetric if swapping coordinates never changes its value. We also want it to be insensitive to changing the sign of any individual coordinate. For nonnegative singular-value lists, the sign changes are invisible in the inputs, but they become useful in proofs involving coordinate shrinkage.

A norm with these two invariances is a symmetric gauge. The Euclidean norm, the sum of absolute coordinates, and the largest absolute coordinate are all examples.

Suppose we begin with the list five, one. Swap the two coordinates to get one, five. If F is symmetric, both lists have the same F value.

Now average the two lists with equal weights. The result is three, three. By convexity, F of three, three is no larger than the average of F of five, one and F of one, five. By symmetry, that average is simply F of five, one.

So the inequality follows immediately for this elementary equalizing operation.

We have not used any special formula for F. The same argument works for every convex permutation-invariant measurement.

## Allow a partial transfer

A more general operation averages a list with a copy obtained by swapping two coordinates. We can give the original list weight one minus t and the swapped list weight t, where t lies between zero and one.

For two entries a and b, the resulting pair is a weighted mixture of a and b in both positions. The total remains a plus b. If t lies between zero and one half, the larger and smaller entries move toward each other without crossing. If t is greater than one half, they pass each other; this is still a convex mixture with a swap, and the same convexity argument applies.

Because the two endpoint lists have equal F value, the mixture cannot have a larger F value. This is the basic T-transform inequality.

For three coordinates, start with six, zero, zero. First average the first two coordinates equally. We get three, three, zero. Next mix the second and third coordinates with one third of the swapped arrangement. The pair three, zero becomes two, one. We arrive at three, two, one.

Every step is a convex combination of a list and a coordinate-swapped copy. Therefore F of three, two, one is at most F of three, three, zero, which is at most F of six, zero, zero.

That gives a direct proof for one particular majorization comparison. We now need to understand why the same method works for every comparison with equal totals.

## The finite transfer descent

Suppose x and y are sorted nonnegative lists, x is majorized by y, and their totals agree. We want to begin at y and reach x by finitely many mixing operations.

A constructive proof tracks where the current list, call it q, differs from the target x. At the beginning q is y. If q already equals x, we have finished.

Otherwise, find a coordinate where q is larger than x and a later coordinate where q is smaller than x. The prefix-sum inequalities ensure that such a surplus and deficit can be paired in a suitable order. Transfer enough mass from the surplus coordinate toward the deficit coordinate to make at least one of the two match its target value exactly.

Choose the transfer so that all the required prefix inequalities remain true and no coordinate becomes negative. Because mass moves from a larger current coordinate to a smaller one, this can be expressed as a mixture with a transposition.

Here is the reason this process terminates: after each carefully chosen transfer, the number of coordinates that disagree with the target strictly decreases. That count is a nonnegative integer, so it cannot decrease forever.

Eventually the current vector equals the target. Chaining the convexity inequality across the finite sequence proves that a symmetric convex measurement cannot increase under ordinary majorization.

This is often called majorization descent. It replaces a potentially complicated spectral comparison by finitely many elementary two-coordinate averages.

There is a subtlety worth noticing. During the construction, an intermediate list need not remain sorted in exactly the same coordinate order. The algorithm can preserve the prefix conditions needed for the next step while using permutation symmetry to control the measurement. The proof must not silently assume that every intermediate pair is already sorted.

## What changes for weak majorization?

Weak majorization permits loss of total mass. A transfer alone preserves total mass, so it cannot explain the whole theorem.

The missing operation is coordinate shrinkage. If one nonnegative list is coordinatewise at most another, an absolute-value-invariant convex gauge cannot increase when we replace the larger list by the smaller one.

Let's prove that instead of assuming it.

Consider a single coordinate of a vector q, and suppose we want to replace its value by a multiple between zero and one of its current value. We can obtain the desired smaller value by averaging q with the vector obtained by changing just that coordinate's sign. Choose the averaging weight so that the two signed contributions produce the required multiple.

Convexity bounds the measurement of this average by the average measurements of the two endpoint vectors. Sign-change invariance makes those endpoint measurements equal. Therefore shrinking that coordinate does not increase F.

Repeat this independently for every coordinate. We conclude that for nonnegative x and q, if x is coordinatewise at most q, then F of x is at most F of q.

Now combine the operations. A finite weak-majorization descent can perform T-transforms on y until it reaches a vector q that dominates x coordinate by coordinate. The same prefix-domination argument as before guides the transfers, and an integer count of unmatched coordinates guarantees termination. Then shrink q to x, one coordinate at a time.

The T-transforms do not increase F. The coordinate shrinkages do not increase F. Thus F of x is at most F of y.

This is the finite symmetric-convex gauge principle. Its proof requires convexity, permutation symmetry, sign-change symmetry, and the actual prefix inequalities. Dropping any of these ingredients requires a different statement.

## A familiar numerical consequence

Take x equal to three, three, and y equal to five, one. We checked that x is majorized by y.

For the Euclidean norm, x has squared length eighteen, while y has squared length twenty-six. So the Euclidean norm of x is smaller.

For the sum of absolute coordinates, both values are six. That measurement responds to total mass but does not distinguish different distributions of the same nonnegative total.

For the largest absolute coordinate, x has value three and y has value five. This measurement is especially sensitive to concentration in a single coordinate.

All three comparisons are consequences of the same majorization relation, even though the measurements look different.

Convexity also yields a statement about scalar functions. For a convex function of one real variable, ordinary majorization implies that the sum of the function evaluated at the coordinates of x is at most the corresponding sum for y. Each mixing step follows by convexity applied separately to the two affected coordinates. For example, choosing the square function gives the eighteen-versus-twenty-six comparison directly.

## Why convexity cannot be omitted

Consider a quantity obtained by taking square roots of nonnegative coordinates, summing them, and then squaring the result. This is the formula that resembles an ell-p gauge with an exponent below one.

For three, three, the value is twelve. For five, one, it is six plus two times the square root of five, which is a little under ten and a half. The inequality goes in the opposite direction from what we proved for convex symmetric gauges.

That is not a contradiction. This measurement lacks the convexity needed for our theorem. In fact, an equalizing transfer can increase it.

Likewise, a convex function that singles out one labeled coordinate is not necessarily invariant under permutations. The partial-sum order alone cannot control an arbitrary label-dependent measurement.

## Connect the theorem to operators

For matrices, a gauge of singular values gives a measurement of the matrix itself. We already know that changing orthonormal input or output coordinates leaves singular values unchanged. So any symmetric gauge applied to singular values automatically has that unitary invariance.

The majorization-descent theorem supplies a powerful comparison principle. If every Ky Fan sum of A is at most the corresponding sum for B, then every convex symmetric gauge of the singular values of A is at most the same gauge of B.

This explains why the Ky Fan sums are a useful collection of tests. Instead of proving a separate norm inequality for every possible spectral gauge, we can prove all the prefix inequalities once and then transfer the result by convexity.

We will put this to work immediately for Schatten norms, where the gauges are power sums of singular values.

## What to reconstruct

Prove the two-coordinate mixing inequality for a convex permutation-invariant function. Prove the one-coordinate shrinkage inequality using an average with a sign-flipped vector.

Then identify the termination measure in the transfer descent: how many coordinates still disagree with the target? Explain why strict decrease matters.

Finally, calculate the three gauges of three, three and five, one, and explain the reversed comparison for the exponent below one.

We now know how an inequality about all prefix sums can control a broad family of convex spectral measurements.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a convex function \(F:\mathbb R^n\to\mathbb R\) invariant under coordinate permutations,
\[
F((1-t)q+t\pi q)\le (1-t)F(q)+tF(\pi q)=F(q),\quad 0\le t\le1,
\]
where \(\pi\) swaps two coordinates. A finite sequence of these **T-transforms** carries \(y\) toward \(x\) when \(x\prec y\). When \(F\) is also sign-invariant, its convexity implies coordinatewise monotonicity on the nonnegative orthant: changing \(q_j\) into \(tq_j\) for \(0\le t\le1\) is a convex combination of \(q\) and its sign flip at coordinate \(j\). Together, T-transform descent and coordinate shrinkage give the weak-majorization gauge comparison \(x\prec_w y\Rightarrow F(x)\le F(y)\) for convex permutation- and sign-invariant gauges.

**Lean bridge (verbatim source excerpts).** `ForTauCeti/Analysis/Convex/Majorization.lean` retains a constructive one-step transfer whose output has strictly fewer mismatched coordinates:

```lean
theorem exists_isTTransform_of_not_forall_le {z q : Fin n → ℝ}
    (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i) (hq0 : ∀ i, 0 ≤ q i)
    (hpre : ∀ k, prefixSum k z ≤ prefixSum k q) (hnot : ¬ ∀ i, z i ≤ q i) :
    ∃ q', IsTTransform q q' ∧ (∀ i, 0 ≤ q' i) ∧
      (∀ k, prefixSum k z ≤ prefixSum k q') ∧
      (Finset.univ.filter fun i => z i ≠ q' i).card <
        (Finset.univ.filter fun i => z i ≠ q i).card := by
```

The target `z` is decreasing and nonnegative; the current vector `q` need only be nonnegative and prefix-dominating. This distinction is essential: the constructive iteration does not require sorted intermediate vectors. The strictly decreasing `Finset.card` is the finite termination certificate. This result was retained locally after the more general symmetric-convex majorization theory developed in DKPS was upstreamed to `TauCeti.Analysis.Convex.Majorization`.

`ForTauCeti/Analysis/Normed/FiniteLpGauge.lean` makes the power-sum gauge explicit:

```lean
noncomputable def lpGauge (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)
```

The displayed formula also accepts exponents below one; for those exponents the gauge is generally **not convex** and the majorization theorem above cannot be applied without additional hypotheses. For \(p\ge1\), the finite \(\ell^p\) norms are convex symmetric gauges. The next lecture applies them to singular-value lists.

**Reconstruction exercise:** use T-transforms to carry \((6,0,0)\) to \((3,2,1)\), and use signed averaging to prove coordinatewise monotonicity of a convex absolute symmetric gauge on nonnegative vectors.
