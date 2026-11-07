# Weyl monotonicity and eigenvalue inequalities: comparing operators without matching eigenvectors

<!-- BEGIN SPOKEN LECTURE -->

The Courant–Fischer theorem gave us a way to locate any sorted eigenvalue of a self-adjoint operator. Instead of solving the characteristic polynomial, we can optimize its Rayleigh quotient over subspaces of a chosen dimension.

Today we will see why that is so powerful. Suppose we have two self-adjoint matrices, A and B. Their eigenvectors may point in entirely different directions. How could we compare their eigenvalues without finding an alignment between two separate eigenbases?

The answer is to compare what the operators do to *every* vector. If one quadratic form is everywhere below another, then all its sorted eigenvalues must lie below the corresponding eigenvalues of the other. This is Weyl monotonicity. And if two quadratic forms differ only by a small amount, their corresponding eigenvalues cannot differ by much either.

## Comparing quadratic forms

Let's start in two dimensions with diagonal matrices. Let A scale the horizontal direction by three and the vertical direction by one. Let B scale those directions by four and two.

For every vector, the quadratic form of B is larger than that of A. Specifically, the difference between the two quadratic forms is the squared length of the vector. So every unit direction gets exactly one more unit of quadratic-form value under B.

It is no surprise that the sorted eigenvalues also increase by one: three becomes four, and one becomes two.

But the idea is not confined to diagonal matrices. We say that A is below B in the self-adjoint operator order when the quadratic form of B minus A is nonnegative for every vector. In plain language, B gives at least as large a quadratic-form value as A in every direction.

This is a partial order, not a way to rank every pair of matrices. Sometimes one operator is larger on one direction and smaller on another. Then neither may be below the other.

That limitation is important. We are about to prove a theorem under an actual hypothesis, not announce that all matrices can be ranked.

## Why the order reaches every eigenvalue

Suppose A is below B. Take any fixed subspace V. The Rayleigh quotient of A is no greater than the Rayleigh quotient of B at every unit vector in V. Therefore, the smallest quotient of A in V is no greater than the smallest quotient of B in V.

Now optimize over all subspaces of dimension k. This pointwise inequality survives when we choose the largest possible minimum. And the Courant–Fischer formula tells us that these two optimized quantities are exactly the kth largest eigenvalues of A and B.

Therefore the kth largest eigenvalue of A is no greater than the kth largest eigenvalue of B. The argument works for every k.

Notice the efficiency of the proof. We never compared the kth eigenvector of A with the kth eigenvector of B. We compared the operators on *all* directions, then used the same variational procedure to select the kth eigenvalue of each.

This is one reason the min–max theorem is more useful than just a formula for computing eigenvalues: it lets inequalities pass through an optimization problem.

## How much can a bounded difference change a quotient?

Now suppose we have no ordering between A and B. Define D to be B minus A. The two operators are self-adjoint, so D is self-adjoint too.

For a unit vector x, the difference between the two Rayleigh quotients is the inner product of D x with x. By Cauchy–Schwarz, its absolute value is at most the length of D x. And by the definition of operator norm, the length of D x is at most the operator norm of D.

Call that norm epsilon. It follows that, for every unit direction, the Rayleigh quotient of A is within epsilon of the Rayleigh quotient of B.

We can express this another way. The operator A minus epsilon times the identity is below B, and B is below A plus epsilon times the identity.

Why? Subtract A from these comparisons. The statements reduce to saying that every quadratic-form value of D lies between negative epsilon and positive epsilon on a unit vector. That is exactly the bound we just proved.

We have trapped B between two shifted copies of A.

## Weyl's operator-norm inequality

Apply monotonicity to that pair of bounds. Every kth eigenvalue of B lies between the kth eigenvalue of A minus epsilon and the kth eigenvalue of A plus epsilon.

Shifting A by epsilon times the identity shifts every eigenvalue by epsilon, because its eigenvectors stay the same and each eigenvalue gains that constant.

So the absolute difference between corresponding sorted eigenvalues of A and B is at most the operator norm of B minus A.

That is the operator-norm Weyl inequality. It is a very strong conclusion from a short argument: one norm bound controls *all* the sorted eigenvalues simultaneously, even when their eigenvectors are unrelated.

Let's check a concrete example. Take A with diagonal entries four, two, and zero. Let B have diagonal entries four, two, and one-tenth. The difference has operator norm one-tenth. Two eigenvalues agree exactly and the third shifts by one-tenth. Every sorted eigenvalue moves by no more than the norm bound, just as the theorem predicts.

But the inequality is not generally an equality. An operator perturbation might have its largest effect in a direction that does not correspond to the particular eigenvalue we are tracking.

## A subtle distinction: eigenvalues versus eigenvectors

The inequality compares *ordered numerical values*. It does not guarantee that the eigenvector associated with the kth eigenvalue of B lies near the kth eigenvector of A.

In fact, if two eigenvalues of A are equal or nearly equal, their associated directions can be highly sensitive to changes. Today's theorem has no hypothesis requiring a spectral gap, because it says nothing about those directions.

That is not a defect. It is a precise statement about the object being controlled. We will spend later parts of the course building the additional geometry needed to control subspaces and angles.

## Comparing the eigenvalues of a sum

There is a second Weyl inequality that reveals more of the variational geometry. Suppose C is A plus B. Its largest eigenvalue is at most the largest eigenvalue of A plus the largest eigenvalue of B. That's easy to see: every unit vector has a quotient for C equal to the sum of its quotients for A and B, and each summand is bounded above by its own maximum.

A more general statement is possible. Take the ith largest eigenvalue of A and the jth largest eigenvalue of B. If i plus j minus one is at most n, then the eigenvalue of C in position i plus j minus one is at most the sum of those two selected eigenvalues.

Why that particular index? It comes from counting dimensions.

The subspace spanned by eigenvectors i through n of A has dimension n minus i plus one, and every quotient of A on it is at most the ith eigenvalue. The analogous trailing subspace for B has dimension n minus j plus one, with quotients at most B's jth eigenvalue.

Their intersection has dimension at least n minus i minus j plus two. Every unit vector in the intersection satisfies both bounds, so its quotient for C is at most the sum of the selected eigenvalues.

Now use the *min–max* formula from the previous lecture. To bound the eigenvalue in position i plus j minus one from above, we need a subspace of dimension n minus i minus j plus two on which every quotient is bounded by our proposed value. The intersection gives us at least that many dimensions; if it is larger, choose a subspace of exactly the required dimension inside it.

The min–max formula proves the inequality.

This argument uses the same forced-intersection principle as Courant–Fischer, but now two different operators contribute the two spectral subspaces.

## What to reconstruct

There are three related ideas to retain.

First, a quadratic-form inequality holds in every direction and therefore survives min–max optimization. Second, an operator-norm difference bounds the difference of Rayleigh quotients in every direction; by adding and subtracting a multiple of the identity, that becomes an order comparison. Third, intersecting trailing spectral subspaces gives the more general inequality for eigenvalues of a sum.

Try proving the operator-norm bound on a unit vector before looking at any eigenvalue formula. Then write the two order inequalities and derive Weyl's bound. Finally, check the dimensions in the sum inequality: why is the intersection guaranteed to be large enough for the target eigenvalue index?

Next we will return to one self-adjoint operator and ask how to select *whole groups* of eigenvalues. That leads to spectral projections, the objects whose geometry will eventually carry the Davis–Kahan theory.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For self-adjoint \(A,B\) on an \(n\)-dimensional real or complex inner-product space, write eigenvalues in nonincreasing order: \(\lambda_1(\cdot)\ge\dots\ge\lambda_n(\cdot)\).

- **Quadratic-form order:** \(A\preceq B\) means \(\langle Ax,x\rangle\le\langle Bx,x\rangle\) for every \(x\). Courant–Fischer implies \(\lambda_k(A)\le\lambda_k(B)\) for every \(k\).
- **Operator-norm Weyl inequality:** with \(\varepsilon=\|A-B\|\), the inequalities \(A-\varepsilon I\preceq B\preceq A+\varepsilon I\) yield
  \[
  |\lambda_k(A)-\lambda_k(B)|\le\|A-B\|.
  \]
- **Weyl sum inequality:** when \(i,j\ge1\) and \(i+j-1\le n\),
  \[
  \lambda_{i+j-1}(A+B)\le\lambda_i(A)+\lambda_j(B).
  \]
  The argument uses the intersection of trailing spectral subspaces. This last inequality is proved in the narration; the cited Lean snippet below covers the operator-norm inequality, **not** the general sum inequality.

**Lean bridge.** The existing `visualizations/lectures/002666_minmax/facts.lean` contains the exact application:

```lean
example :
    |hT.eigenvalues hn k -
      hS.eigenvalues hn k| ≤ ‖T - S‖ :=
  hT.abs_eigenvalue_sub_eigenvalue_le_norm hS hn k
```

`T` and `S` are continuous linear maps on a finite-dimensional real inner-product space; `hT` and `hS` witness their symmetry. `hn` fixes the dimension, and `k : Fin n` is a zero-based spectral index. The absolute value corresponds to \(|\lambda_k(T)-\lambda_k(S)|\), while `‖T - S‖` is the operator norm. This source invokes the accepted TauCeti result. The mathematical proof route through min–max and quadratic-form order belongs to our first-principles course whether a declaration currently lives in DKPS or TauCeti; the precise donor provenance is tracked separately.
