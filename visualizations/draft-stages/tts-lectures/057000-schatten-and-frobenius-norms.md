# 057000 — Schatten and Frobenius norms

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `023000` rectangular Gram operators; `035000` modulus; `036000` SVD; `054000` Ky Fan sums; `055000` weak majorization; `056000` convex gauge comparisons. **Next:** unitarily invariant norms and symmetric gauges.

<!-- BEGIN SPOKEN LECTURE -->

# Several ways to measure one linear map

A linear map has several natural notions of size. If we care about its largest effect on a unit input, we use the operator norm. If we care about its total squared action on an orthonormal collection of inputs, we use the Frobenius norm. If we want the sum of all singular values, we use the nuclear norm.

These are not isolated constructions. They belong to one family, the Schatten norms. We have now developed enough singular-value theory and majorization theory to derive their formulas, compare them, and explain why they satisfy triangle inequalities.

The central idea is simple. A Schatten norm is an ordinary finite-dimensional ell-p norm applied to the singular-value list. But establishing the consequences requires care, especially for rectangular maps and for different exponents.

## Start from the singular values

Let A map a finite-dimensional real or complex inner-product space E into another one F. Write its singular values in decreasing order, with zeros included when needed. There are as many right singular directions as the dimension of E; the positive singular values number at most the smaller dimension.

Choose a real exponent p at least one and finite. Raise each singular value to the p-th power, add the results, and take the p-th root. That gives the Schatten p norm of A.

For p equal to one, nothing is squared. We simply add all singular values. This is the nuclear norm, also called the trace norm.

For p equal to two, we add the squares of the singular values and take a square root. This is the Frobenius norm, also called the Hilbert–Schmidt norm in the finite-dimensional setting.

As p becomes very large, the biggest singular value dominates the power sum. The limiting Schatten infinity norm is the largest singular value, which is the operator norm.

At this point the definitions are measurements based on a list of nonnegative numbers. We must still show that they behave like genuine norms on maps.

## A single example, four measurements

Take a map from two-dimensional real space to three-dimensional real space. Its first column is three times the first output coordinate vector, and its second column is four times the second output coordinate vector. The third output coordinate is always zero.

The right singular directions are the two input coordinate axes. The singular values are four and three, arranged from largest to smallest.

The nuclear norm is four plus three, which equals seven.

The Frobenius norm is the square root of sixteen plus nine, so it equals five.

The operator norm is four.

For Schatten four, we add four to the fourth power and three to the fourth power, obtaining three hundred thirty-seven, then take the fourth root. That result is between four and five.

These values capture different aspects of the same map. The operator norm sees only the strongest direction. The Frobenius norm combines squared contributions. The nuclear norm adds all the lengths without squaring them.

Notice also that the unused third output coordinate contributes no new singular value. Rectangularity causes no difficulty because we work from the input and output singular vectors rather than pretending A has a square eigenvalue matrix.

## Derive the Frobenius formula from columns

Choose any orthonormal basis of the source space E. Apply A to each basis vector, take the squared length of each output, and add these squared lengths. We claim that the result is the sum of the squares of all singular values.

First prove it for a particularly convenient basis: the right singular-vector basis. The image of each basis vector has length equal to its singular value. So the sum of squared output lengths is exactly the sum of singular values squared.

But why does the answer stay the same for a different orthonormal basis?

Let G denote the Gram operator A adjoint followed by A. For every input vector e, the squared output length of A e equals the inner product of G e with e.

Now choose an orthonormal eigenbasis of G. We know that its eigenvalues are the squares of A's singular values. For any other orthonormal basis, expand each basis vector in the Gram eigenbasis. The total contribution from a fixed Gram eigenvector is its eigenvalue multiplied by the sum, over the chosen basis vectors, of squared overlap coefficients.

Parseval's identity says that this last sum equals one, because the chosen basis is complete and orthonormal.

Therefore every Gram eigenvalue contributes exactly once. The total is independent of the chosen orthonormal basis and equals the sum of squared singular values.

Taking the square root gives the Frobenius norm. In matrix coordinates, this is the familiar square root of the sum of squared absolute values of all matrix entries. In the complex case, use squared magnitudes, not ordinary squares.

This proof connects the Frobenius norm to Hilbert-space geometry instead of treating it as a formula attached to a particular matrix.

## Where the trace enters

For a square endomorphism, the trace is the sum of its diagonal entries in an orthonormal basis. We can also define it as the sum of its eigenvalues counted with multiplicity, when the operator is self-adjoint.

The Gram operator A adjoint A acts on the source space, even when A itself is rectangular. It is positive, and its eigenvalues are singular values squared. Thus the square of the Frobenius norm equals the trace of A adjoint A.

Similarly, the modulus of A is the positive square root of A adjoint A. Its eigenvalues are the singular values of A. Therefore the nuclear norm of A equals the trace of its modulus.

This is why the nuclear norm is called the trace norm. For a rectangular map, we take the trace of the positive modulus on the source, not a trace of the rectangular map itself.

These are finite-dimensional formulas. Infinite-dimensional trace class and Hilbert–Schmidt class require convergence conditions that we have not introduced yet.

## Why the Schatten measurements are norms

A norm must be nonnegative, vanish only at zero, scale by absolute value under scalar multiplication, and satisfy the triangle inequality.

The first properties follow directly from singular values. They are nonnegative. If all vanish, the operator's modulus is zero, hence the operator is zero. Multiplying A by a scalar multiplies every singular value by the scalar's absolute value.

The triangle inequality is the interesting part.

From the Ky Fan lecture, we know that the singular values of A plus B are weakly majorized by the componentwise sum of the singular-value lists of A and B.

From the previous lecture, any convex symmetric gauge cannot increase under weak majorization. The finite ell-p norm is such a gauge when p is at least one.

Therefore the ell-p norm of the singular-value list of A plus B is no larger than the ell-p norm of the list obtained by adding the singular values of A and B componentwise.

Now use the ordinary ell-p triangle inequality, sometimes called Minkowski's inequality, on those two nonnegative lists. The ell-p norm of their sum is at most the sum of their ell-p norms.

Combining the inequalities proves the Schatten p triangle inequality.

The proof does not require A and B to share singular vectors. That is its main strength. The singular-value lists of A and B cannot generally be added position by position to obtain the singular-value list of their sum, but the majorization comparison is enough.

For p equal to infinity, the same argument can use the maximum-coordinate gauge, or we can return to the direct operator-norm triangle inequality.

## Compare the endpoint norms

For any finite nonnegative list, the largest entry is at most the square root of the sum of squared entries. That square root is at most the sum of all entries.

Applying these facts to singular values gives the operator norm at most the Frobenius norm, and the Frobenius norm at most the nuclear norm.

These comparisons do not need a matrix dimension constant.

We can also obtain reverse bounds that depend on rank. Suppose A has exactly r positive singular values. By Cauchy–Schwarz, their sum is at most the square root of r times the square root of their squared sum. Thus the nuclear norm is at most the square root of r times the Frobenius norm.

And because each singular value is at most the largest one, their squared sum is at most r times the largest squared singular value. So the Frobenius norm is at most the square root of r times the operator norm.

When r equals one, all three norms coincide. For a rank-one map with singular value seven, each norm equals seven.

At the other extreme, suppose the r nonzero singular values are all equal to one. Then the operator norm is one, the Frobenius norm is the square root of r, and the nuclear norm is r. Those examples achieve the rank-dependent bounds.

For general finite exponents, analogous comparisons follow from the ordinary relations between finite ell-p norms. We do not need their full proof today; the three classical norms already show how the exponent changes the emphasis on the largest singular directions.

## Why orthonormal coordinates do not matter

Suppose we change orthonormal coordinates in the source and target. The matrix of A becomes U A V adjoint, where U and V are unitary maps in the respective coordinate spaces.

The new Gram operator is V followed by A adjoint A followed by V adjoint. It is unitarily similar to the old Gram operator, so it has the same eigenvalues, including multiplicities.

Therefore it has the same singular values, and every Schatten norm is unchanged. This is a basis-independent measurement of the linear map.

This unitary invariance also explains why the column-energy formula remains constant under a change of orthonormal input basis. The coordinates change, but the sum of squared output lengths does not.

## What these norms prepare us to prove

In Davis–Kahan theory, we want to measure how much a spectral subspace changes under perturbation. The operator norm controls the single largest rotation. The Frobenius norm aggregates the squared motion across orthogonal directions. The nuclear norm aggregates all singular-value magnitudes.

Using several Schatten norms lets us state perturbation estimates at different levels of sensitivity to rank and multiplicity.

Our majorization work says even more: we can often prove an inequality about every Ky Fan sum and then deduce all the Schatten estimates at once. The next lecture will describe that principle for general unitarily invariant norms, without restricting ourselves to a particular power p.

## What to reconstruct

Compute all four measurements of the rectangular example with singular values four and three. Prove the Frobenius column-energy identity by expanding an arbitrary orthonormal basis in a right singular basis.

Then reproduce the Schatten triangle inequality as two steps: first weak majorization, then Minkowski's inequality.

Finally, prove the rank-dependent comparisons, and identify examples attaining equality.

These calculations turn singular-value lists into concrete operator measurements that we can use in perturbation estimates.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a finite-dimensional map \(A:E\to F\) with singular values \(\sigma_i(A)\ge0\),
\[
\|A\|_{S_p}=\left(\sum_i\sigma_i(A)^p\right)^{1/p}
\quad(1\le p<\infty),\qquad
\|A\|_{S_\infty}=\max_i\sigma_i(A).
\]
The important cases are \(S_1\) (nuclear/trace), \(S_2\) (Frobenius/Hilbert–Schmidt), and \(S_\infty\) (operator). Writing \(G=A^*A\),
\[
\|A\|_{S_2}^2=\operatorname{tr}(A^*A)
=\sum_i\|Ae_i\|^2=\sum_i\sigma_i(A)^2,
\qquad
\|A\|_{S_1}=\operatorname{tr}|A|.
\]
For \(r=\operatorname{rank}A\ge1\),
\[
\|A\|_{S_\infty}\le\|A\|_{S_2}\le\|A\|_{S_1},\qquad
\|A\|_{S_1}\le\sqrt r\,\|A\|_{S_2}
\le r\,\|A\|_{S_\infty}.
\]
The triangle inequality for \(p\ge1\) follows from \(\sigma(A+B)\prec_w\sigma(A)+\sigma(B)\), weak-majorization monotonicity of \(\ell^p\), and Minkowski's inequality.

**Lean bridge (verbatim source excerpts).** `DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtFrobenius.lean` supplies the finite-dimensional identification:

```lean
theorem hilbertSchmidtNorm_eq_frobenius
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    ContinuousLinearMap.hilbertSchmidtNorm A =
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := F)
        A.toLinearMap := by
```

The types `E` and `F` are allowed to differ, and `CompleteSpace` is explicit because the Hilbert–Schmidt definition applies to complete spaces; finite-dimensionality supplies those instances mathematically. The displayed theorem identifies two formalized gauges; it does not establish by itself every Schatten triangle inequality.

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Instances.lean` establishes the finite-column formula for the **nuclear norm of the Gram operator**:

```lean
theorem nuclear_adjoint_comp_self_eq_sum_sq_norm
    (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    nuclear 𝕜 E E (A.adjoint ∘ₗ A) = ∑ i, ‖A (b i)‖ ^ 2 := by
```

Because \(A^*A\) is positive, its nuclear norm equals its trace, namely the sum of the squared singular values of \(A\). This source theorem therefore supports the **squared Frobenius column-energy identity**; it should not be misread as claiming the nuclear norm of \(A\) is the same as its squared Frobenius norm. The general nuclear, Frobenius and Schatten seminorm constructors now reside in imported TauCeti modules, with DKPS provenance recorded in the retained staging files.

**Reconstruction exercise:** for \(A=\begin{psmallmatrix}3&0\\0&4\\0&0\end{psmallmatrix}\), compute \(S_1,S_2,S_4,S_\infty\), and verify the trace/column identity and rank-dependent bounds.
