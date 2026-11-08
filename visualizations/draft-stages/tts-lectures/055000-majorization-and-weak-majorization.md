# 055000 — Majorization and weak majorization

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `036000` singular-value decomposition; `052000` singular-value min–max; `054000` Ky Fan sums and inequalities. **Next:** convexity and majorization descent.

<!-- BEGIN SPOKEN LECTURE -->

# Comparing whole lists without comparing every entry

In the preceding lecture, we met a pair of matrices that defeats a tempting rule about singular values. The second singular value of a sum can exceed the sum of the two second singular values. Nevertheless, every cumulative sum of the largest singular values obeys a triangle inequality.

That observation suggests an ordering on lists of numbers. Instead of comparing the first entries, then the second entries, one at a time, compare their running totals. This is majorization. It is a useful language for stating how one spectrum is more concentrated than another.

Today we will define two versions, work out examples that distinguish them, and prove an elementary principle that makes these comparisons usable in later norm estimates. Our lists will be finite, real, nonnegative, and arranged from largest to smallest. These hypotheses are natural for singular values, and they let us focus on the geometry of the comparison.

## Begin with sorted nonnegative lists

Take two lists, each containing n numbers, called x and y. Sort each in decreasing order. If the lists originally had different lengths, append zeros to the shorter one. Adding zero singular values does not change a linear map's existing singular values or its positive Ky Fan sums.

For any positive integer k up to n, add the first k entries of x. Call the result the k-th prefix sum of x. Do the same for y.

We say x is weakly majorized by y when every prefix sum of x is at most the corresponding prefix sum of y.

Notice the word every. Comparing only the first entry checks the largest value, but it does not control how many large values appear. Comparing only the total checks the total mass, but it does not control concentration. Weak majorization requires all the intermediate checks too.

Consider x equal to three, three, and zero; y equal to five, one, and zero. Their first prefix sums are three and five. Their second prefix sums are both six. Their third prefix sums are also both six. Therefore x is weakly majorized by y.

Yet the second entry of x is three, larger than the second entry of y, which is one. This is our first important distinction: weak majorization does not imply coordinatewise domination.

Now take x equal to two and one, and y equal to three and three. The first prefixes are two and three. The full totals are three and six. This is another instance of weak majorization, but the totals are different.

## What makes ordinary majorization stronger?

Ordinary majorization adds one requirement: the full totals of the two lists must agree.

Equivalently, every proper prefix sum of x is at most the corresponding prefix sum of y, and the total sums are equal.

The pair three, three and five, one satisfies this stronger relation. The pair two, one and three, three satisfies only the weak relation.

One can think of ordinary majorization as redistributing a fixed quantity. The list five, one concentrates more of its total in the largest coordinate. The list three, three distributes the same total more evenly. In contrast, weak majorization also allows the total quantity to decrease.

Be careful with the direction of the symbol when we describe this in words. The more even list, three, three, is majorized by the more concentrated list, five, one. We use the same ordering convention as in the Ky Fan inequalities: the left-hand list has smaller or equal leading partial sums.

What about equality? If x is majorized by y and y is majorized by x, then their sorted entries agree. To prove it, every prefix sum agrees in both directions. Subtract the prefix sum ending just before position k from the prefix sum ending at k. That difference is exactly the k-th entry. So all entries agree.

Before sorting, the original lists could still differ by a permutation. This is why majorization naturally ignores the choice of labels on coordinates.

## Derive a weighted comparison from the prefixes

Suppose x is weakly majorized by y. Choose another list of weights, also arranged in decreasing order, and assume the weights are nonnegative. We claim that the weighted sum of x is at most the weighted sum of y.

This claim is worth proving. It is often hidden inside longer matrix inequalities.

Write delta k for the prefix sum of y minus the prefix sum of x, through position k. By weak majorization, every delta is nonnegative.

Now look at the weighted difference: the sum of each weight times the corresponding entry of y minus x.

We can reorganize it. The first prefix difference, delta one, is multiplied by the drop from the first weight to the second. Delta two is multiplied by the drop from the second weight to the third. Continue until the second-to-last prefix. Finally add the last weight times the full prefix difference.

Why does this identity hold? Expand the first two terms. The coefficient of the first entry difference receives the first weight, because it appears in every relevant prefix. The coefficient of the second entry difference receives the second weight, and so on. All intermediate terms telescope.

Every coefficient in the reorganized sum is nonnegative: successive weights decrease, the last weight is nonnegative, and all the delta values are nonnegative. So the entire weighted difference is nonnegative.

This technique is called summation by parts, or Abel summation. We have proved the particular form we need, directly from finite sums.

Notice a useful refinement. If x is ordinarily majorized by y, their full prefix difference is zero. Then the final term disappears, and the weights only need to be decreasing; they do not need to be nonnegative. That is another way the equal-total condition changes the theory.

## A numerical weighted example

Return to x equal to three, three, zero, and y equal to five, one, zero. Use decreasing weights four, two, one.

The weighted sum for x is twelve plus six, giving eighteen. For y it is twenty plus two, giving twenty-two. The inequality points in the expected direction.

The prefix differences are two, zero, zero. The first weight drop is two. So summation by parts gives a difference of two times two, or four. That matches twenty-two minus eighteen.

What if we use weights zero, one, zero, which are not decreasing? The weighted sum for x becomes three, while that for y becomes one. The inequality reverses. So the decreasing-weight hypothesis was doing actual work.

## Transfer mass between two coordinates

There is a geometric way to produce majorized lists. Start with two entries a and b, with a at least b. Move some quantity from the larger entry to the smaller, stopping before they cross each other. The total is unchanged, and their difference becomes smaller.

For example, start with five and one. Move two from the first entry to the second. We arrive at three and three. This is the simplest equalizing transfer.

The operation can also be written as an average between the original list and the list obtained by swapping those two entries. In this example, three, three is one half of five, one plus one half of one, five.

Such an operation is often called a T-transform. Any convex combination of a list and one of its coordinate-swapped versions preserves the total and cannot increase the leading prefix sums after resorting.

A three-coordinate example makes the process less trivial. Start with six, zero, zero. Move three from the first coordinate to the second, obtaining three, three, zero. Then move one from the second to the third, obtaining three, two, one. Each operation makes the list less concentrated without changing its total.

The converse is a central finite majorization theorem: if two finite lists have equal total and the prefix inequalities point the right way, one can reach the less concentrated list from the more concentrated list by finitely many of these mixing operations, allowing permutations between steps.

We will derive the convexity consequence, and examine why the constructive algorithm terminates, in the next lecture.

## Apply the definition to singular values

For a linear map A, collect its singular values in decreasing order. Every Ky Fan sum is precisely a prefix sum of that list.

So the statement that every Ky Fan sum of A is at most the corresponding Ky Fan sum of B says exactly that the singular-value list of A is weakly majorized by that of B, after appending zeros if necessary.

This gives us a compact mathematical summary of the preceding lecture. For maps A and B of the same size, the singular-value list of A plus B is weakly majorized by the componentwise sum of the singular-value lists of A and B. Both lists on the right are already decreasing, so their componentwise sum is decreasing too.

We cannot generally replace that cumulative statement with an inequality at each singular-value position. Our diagonal counterexample already disproved the stronger assertion.

Pinching gives another example. Deleting the off-diagonal blocks of a map cannot increase any Ky Fan sum. Therefore the pinched map's singular-value list is weakly majorized by the original map's list.

Neither statement asserts that the singular values retain their old order coordinate by coordinate. The information is in their cumulative sizes.

## Check the limits of the definition

A weak-majorization comparison must use sorted lists. If you compare unsorted entries in their written order, the running sums depend on how someone happened to label coordinates.

The same finite-length convention matters too. When two operators have different source and target dimensions, we will make their lists comparable by padding with zeros. That becomes a separate technical topic later in the course.

And our nonnegativity hypothesis is deliberate. It is automatic for singular values but not for eigenvalues of arbitrary self-adjoint operators. Signed eigenvalue majorization is possible, but its exact hypotheses and consequences differ from the nonnegative weak-majorization setting used here.

## What to reconstruct

Given two decreasing nonnegative lists, compute every prefix and decide whether weak or ordinary majorization holds. Explain why comparing only their totals is insufficient.

Next, prove the summation-by-parts identity by expanding the coefficients of each entry difference. Use it to prove the decreasing-nonnegative-weight comparison.

Then verify the two T-transforms taking six, zero, zero to three, two, one. Finally, restate the Ky Fan triangle inequality as a weak-majorization statement about singular-value lists.

The next lecture will use convexity to turn these cumulative inequalities into comparisons of much broader families of measurements.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For decreasing nonnegative sequences of equal finite length, define
\[
S_k(x)=\sum_{i=1}^k x_i,\qquad
x\prec_w y\iff S_k(x)\le S_k(y)\ (1\le k\le n),
\]
with **ordinary majorization** \(x\prec y\) adding \(S_n(x)=S_n(y)\). For decreasing weights \(a_1\ge\cdots\ge a_n\ge0\),
\[
\sum_{i=1}^n a_i(y_i-x_i)
=\sum_{k=1}^{n-1}(a_k-a_{k+1})(S_k(y)-S_k(x))
+a_n(S_n(y)-S_n(x))\ge0.
\]
If totals agree, the last term vanishes, so the \(a_i\) need only be decreasing.

**Lean bridge (verbatim source excerpts).** `DavisKahan/OperatorIdeal/Majorization/WeakSubmajorization.lean` packages the infinite, decreasing and nonnegative, prefix comparison:

```lean
structure WeaklySubmajorized (x y : ℕ → ℝ) : Prop where
  left_antitone : Antitone x
  right_antitone : Antitone y
  left_nonneg : ∀ n, 0 ≤ x n
  right_nonneg : ∀ n, 0 ≤ y n
  prefix_le : ∀ k, sequencePrefixSum k x ≤ sequencePrefixSum k y
```

This structure uses zero-indexed sequences and sums of the first `k` entries; its `prefix_le` is the mathematical condition \(S_k(x)\le S_k(y)\). The same file proves how finite prefixes inherit the native finite-vector predicate:

```lean
theorem finite_weaklyMajorized_of_weaklySubmajorized
    {x y : ℕ → ℝ} (hxy : x ≺w y) (n : ℕ) :
    IsWeaklyMajorizedBy
      (sequencePrefixVector n x)
      (sequencePrefixVector n y) := by
```

The infix `≺w` is a **local** notation for `WeaklySubmajorized`. The second theorem needs that local context; it is not a statement about unsorted sequences. The native finite predicate `IsWeaklyMajorizedBy` is imported from `TauCeti.Analysis.Convex.Majorization`, a library to which much of the DKPS-developed majorization infrastructure was previously upstreamed.

**Reconstruction exercise:** establish \((3,3,0)\prec(5,1,0)\), compute the three prefix differences, and use Abel summation for weights \((4,2,1)\). Then express Ky Fan triangle inequalities using \(\prec_w\).
