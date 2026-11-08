# Courant–Fischer min–max: finding every eigenvalue by geometry

<!-- BEGIN SPOKEN LECTURE -->

For a self-adjoint matrix A, the Rayleigh quotient of a nonzero vector x is the inner product of A x with x divided by the squared norm of x. Expressing x in an orthonormal eigenbasis shows that this quotient is a weighted average of the eigenvalues. Its maximum is the largest eigenvalue, and its minimum is the smallest. The Courant-Fischer principle extends this optimization to every eigenvalue in the ordered list.

But that leaves a question. Suppose a matrix has ten eigenvalues. Can we recover the fourth one without first calculating all the eigenvectors? And could we describe that fourth eigenvalue in a way that does not depend on a particular eigenbasis?

The Courant–Fischer theorem answers both questions. Its key idea is to optimize not over one vector at a time, but over whole subspaces. The proof rests on a piece of geometry we can understand before writing any complicated expression: if two subspaces occupy enough dimensions of the same space, they must have a nonzero vector in common.

## Why simply finding the second-best vector fails

Start with a three-dimensional real symmetric matrix having eigenvalues five, two, and negative one. Imagine its three perpendicular unit eigenvectors. In the direction of the first, the Rayleigh quotient is five. In the second, it is two. In the third, it is negative one.

Could we get the second eigenvalue by asking for the largest Rayleigh quotient among vectors that are not the top eigenvector? No. We can choose vectors almost parallel to the top eigenvector. Their quotients are arbitrarily close to five. Excluding one line does not make two the new maximum.

One way out would be to forbid every component along the top eigenvector. Then the maximum over its perpendicular plane is two. That works, but it assumes we already know the top eigenvector. We want a characterization that does not require it.

Instead, we will let someone choose a plane, ask what the smallest Rayleigh quotient in that plane must be, and then choose the plane with the best possible worst case.

## An experiment with planes

Stay in three dimensions. Every plane through the origin contains many directions. The Rayleigh quotient will usually vary as we move around those directions.

If the plane is spanned by the eigenvectors for five and two, every unit vector in it has a quotient between two and five. Its smallest quotient is exactly two.

What if we choose another plane? Here is the important observation: every plane through the origin intersects the plane spanned by the eigenvectors for two and negative one along at least one nonzero direction. Along that second plane, the quotient is never greater than two. Therefore our chosen plane contains at least one direction whose quotient is at most two.

No plane can make its worst direction better than two. And we already found a plane whose worst direction achieves two. So the best possible worst Rayleigh quotient among two-dimensional planes is exactly the middle eigenvalue, two.

The expression “best possible worst case” is the max–min construction: choose a subspace to maximize the minimum Rayleigh quotient inside it.

## Why two planes must intersect

Let's justify the geometric step rather than simply assert it.

A plane through the origin in three-dimensional space has two independent directions. Two such planes would have four independent directions between them if they shared nothing except zero. But the ambient space has room for only three independent directions. So they must share a nonzero vector.

In general, suppose a space has dimension n, while two subspaces have dimensions p and q. If their intersection were only zero, we could combine a basis from each to get p plus q independent vectors. That is impossible when p plus q exceeds n.

More precisely, the dimension of their intersection is at least p plus q minus n. We need only the consequence: when their dimensions add to more than n, the intersection contains a nonzero vector.

The proof of Courant–Fischer repeatedly uses this fact to force an arbitrary subspace to meet a carefully chosen spectral subspace.

## The general max–min formula

Take an n-dimensional real or complex inner-product space and a self-adjoint operator A. List its eigenvalues from largest to smallest, counting repetitions: lambda one, lambda two, through lambda n.

Pick an index k, somewhere between one and n. Consider every subspace of dimension k. For each subspace, find the smallest Rayleigh quotient among its unit vectors. Then take the largest of those smallest values over all choices of the subspace.

Courant–Fischer says the result is lambda k.

Let's prove both directions of that equality.

First, choose the particular k-dimensional subspace spanned by eigenvectors one through k. On this subspace, the quotient is a weighted average of the first k eigenvalues. Its minimum is lambda k, achieved by the kth eigenvector. So the max–min value is at least lambda k.

Second, let someone choose any other k-dimensional subspace V. Look at the spectral subspace spanned by eigenvectors k through n. Its dimension is n minus k plus one. The dimensions of these two subspaces add to n plus one. Their intersection therefore contains a nonzero vector.

Normalize a vector from that intersection. Because it lies in the trailing spectral subspace, its Rayleigh quotient is a weighted average of lambda k and the smaller eigenvalues. So its quotient cannot exceed lambda k.

Since this vector lies in V, the minimum quotient in V is at most lambda k. This holds for every k-dimensional V. So even the best choice of V has minimum at most lambda k.

We have both inequalities. The max–min value equals lambda k.

Notice that nothing depended on choosing a particular basis inside a repeated eigenspace. The proof used the dimensions and the invariant subspaces. Those are geometric properties of the operator.

## Turning the order around

There is a companion formula, sometimes called the min–max form. Instead of choosing a k-dimensional subspace and maximizing its minimum, choose a subspace of dimension n minus k plus one and minimize its maximum Rayleigh quotient.

Why should that also give lambda k?

Take the trailing spectral subspace, spanned by eigenvectors k through n. Its maximum quotient is lambda k. So the min–max value cannot be greater than lambda k.

Now let someone choose any subspace of that same dimension. It must intersect the leading spectral subspace, spanned by eigenvectors one through k, because their dimensions again add to n plus one. A unit vector in the intersection has a quotient at least lambda k. Hence the maximum quotient in the chosen subspace is at least lambda k.

The best attempt to make that maximum small cannot push it below lambda k. The min–max value therefore also equals lambda k.

These are two symmetric ways of locating the same eigenvalue: maximize the minimum on a k-dimensional subspace, or minimize the maximum on a complementary-sized subspace.

## Why multiplicities do not break the argument

Suppose the second and third eigenvalues are both two. Their eigenvectors span a two-dimensional eigenspace, and we may rotate our orthonormal basis inside it. Nothing changes in either variational expression.

Our statements use eigenvalues with multiplicity and the *dimensions* of chosen subspaces. They do not require us to pick a unique second or third eigenvector.

This feature becomes important when a numerical calculation gives us an approximate subspace but not a uniquely aligned list of eigenvectors.

## A first consequence for trial spaces

Remember the Rayleigh–Ritz construction. We restricted an operator to a smaller trial subspace and obtained a compressed self-adjoint matrix. Every quotient in that compressed problem is an ambient Rayleigh quotient evaluated on a vector from the trial subspace.

The min–max theorem therefore gives a direct route to comparing Ritz values with the full operator's eigenvalues. We can optimize inside fewer available directions, and the constraint changes what maxima and minima are possible. Later we will make that comparison precise.

For now, the essential result is complete. We can recover every sorted eigenvalue by a competition between choosing subspaces and choosing directions inside them.

Try reconstructing the middle-eigenvalue example in three dimensions without formulas. Then explain why two subspaces whose dimensions add to more than the ambient dimension must intersect. Finally, repeat the two halves of the general proof, carefully identifying which spectral subspace produces the upper bound and which one attains equality.

The min-max characterization allows eigenvalue comparisons of different self-adjoint matrices without requiring their eigenvectors to align.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

Let \(A=A^*\) on an \(n\)-dimensional real or complex Hilbert space, with eigenvalues \(\lambda_1\ge\cdots\ge\lambda_n\), counted with multiplicity. For \(x\ne0\), \(R_A(x)=\langle Ax,x\rangle/\|x\|^2\). Then, for \(1\le k\le n\),

\[
\lambda_k
=\max_{\dim V=k}\;\min_{\substack{x\in V\\\|x\|=1}}R_A(x)
=\min_{\dim W=n-k+1}\;\max_{\substack{x\in W\\\|x\|=1}}R_A(x).
\]

The key geometric lemma is \(\dim(U\cap V)\ge\dim U+\dim V-n\). With \(V\) arbitrary of dimension \(k\), intersect it with \(\operatorname{span}(e_k,\dots,e_n)\); with \(W\) arbitrary of dimension \(n-k+1\), intersect it with \(\operatorname{span}(e_1,\dots,e_k)\). No distinct-eigenvalue hypothesis is needed.

**Lean bridge.** `visualizations/lectures/002666_minmax/facts.lean` gives the following exact application of the accepted TauCeti min–max API (the index `k : Fin n` is zero-based):

```lean
example : hT.eigenvalues hn k =
    ⨆ V : {V : Submodule ℝ E //
        finrank ℝ V = (k : ℕ) + 1},
      ⨅ x : {x : E //
          x ∈ (V : Submodule ℝ E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_ℝ :=
  hT.eigenvalues_eq_iSup_iInf_re_inner hn k
```

`Submodule ℝ E` is a real linear subspace, `finrank` is its dimension, and the dependent subtype after `//` carries the dimension or unit-vector requirement. `⨆` and `⨅` are indexed supremum and infimum, not computational loops; for the finite-dimensional setting they express the extrema proved above. The statement in this source is real-scalar; the spoken proof also applies to complex self-adjoint operators. The matching mathematics was developed in the DKPS project and moved into the TauCeti library; importing it from TauCeti does not make it external to this course's proof obligations. The Lean sample invokes the theorem rather than reproducing its proof term, which is why the transcript supplies the geometric proof.
