# 036000 — Singular-value decomposition

**Draft status:** audio-first mathematical lecture. **Prerequisites:** Gram operators, the finite spectral theorem, adjoints, operator modulus, orthonormal bases. **Next:** polar decomposition.

<!-- BEGIN SPOKEN LECTURE -->

# Finding the directions a linear map stretches

Imagine a flat sheet of material drawn as a circle. Apply a linear transformation. Typically, the circle becomes an ellipse. One direction is stretched most, another least, and in higher dimensions there are several independent stretching directions.

A general matrix does not tell us those directions just by looking at its entries. It mixes stretching with changes in orientation, and the matrix may be rectangular. But the operator modulus gives us a precise way to find the stretching information.

The singular-value decomposition, or S V D, follows from the spectral theorem for the positive Gram operator. Its eigenvectors identify input directions, and their images determine the corresponding output directions.

## Start with the source Gram operator

Let A be a linear map from a finite-dimensional real or complex inner-product space E to another such space F.

The source Gram operator, A adjoint A, acts on E. It is positive and self-adjoint. Therefore the finite spectral theorem supplies an orthonormal basis of E consisting of its eigenvectors.

Call these vectors v one, v two, and so on. Each has a nonnegative eigenvalue, since a Gram operator is positive.

For each eigenvalue, take its nonnegative square root. Call that number the corresponding singular value. We conventionally arrange the singular values from largest to smallest, counting multiplicity.

Why take square roots? Because the eigenvalues of A adjoint A describe *squared* output lengths. The singular values describe actual stretching factors.

If a unit input vector v has Gram eigenvalue nine, the length of A v is three. It is three, not nine, that belongs in a decomposition of A as stretches followed by orientation changes.

## Construct the output directions

Consider an eigenvector v with a *positive* Gram eigenvalue. Its image A v is nonzero. We can normalize it by dividing by its singular value.

Call the resulting unit vector u. In words, u equals A v divided by sigma, where sigma is the positive singular value.

Then A v equals sigma times u. We have a unit input direction, a nonnegative stretching factor, and a unit output direction.

Now the crucial question: if two input eigenvectors are orthogonal, are their corresponding output directions orthogonal?

Take two eigenvectors v i and v j with positive eigenvalues. Compute the inner product of A v i and A v j. Move A from the first slot to the second using the adjoint identity. What remains is the inner product of v i with A adjoint A v j.

Because v j is an eigenvector, that is its Gram eigenvalue multiplied by the inner product of v i and v j. For distinct indices, the latter is zero. So the output images are orthogonal.

On a single index, the squared length of A v i equals the corresponding Gram eigenvalue, which is sigma i squared. Therefore dividing by sigma i makes a unit vector.

We have proved that the output vectors obtained from the positive singular values are orthonormal.

This is the heart of the singular-value decomposition. The Gram operator identifies perpendicular input directions that A sends to perpendicular output directions.

## What happens when a singular value is zero?

We cannot divide by zero, and we do not need to.

A zero Gram eigenvalue means the squared length of A v is zero. So A v is the zero vector.

Those zero-eigenvalue input vectors form an orthonormal basis for the kernel of A. They are exactly the directions that disappear under the map.

For every positive singular value, we get a unit output direction. Since those output directions are orthonormal, we can extend them to an orthonormal basis of the entire output space F. The additional output vectors do not need matching nonzero input directions; they simply complete the coordinate system.

This handles rectangular maps and rank-deficient maps in one construction.

## A complete example

Take A from two-dimensional real space to three-dimensional real space. It sends the vector with coordinates x and y to the three-coordinate vector x plus y, zero, zero.

Its matrix has three rows and two columns. The first row is one, one. The other rows are zero.

For A of x comma y equal to x plus y, zero, zero, the adjoint sends an output triple to the pair whose two entries both equal the first coordinate of the triple. Consequently A adjoint A sends x comma y to x plus y, x plus y. Its two-by-two matrix has all entries one, as can also be checked by taking the dot products of A's two identical columns.

There are two perpendicular unit input directions. The first points along equal coordinates: one over square root of two, one over square root of two. Its Gram eigenvalue is two. The second points along opposite coordinates: one over square root of two, negative one over square root of two. Its Gram eigenvalue is zero.

Thus the singular values are square root of two and zero.

Apply A to the first unit input direction. Its output is square root of two, zero, zero. Normalize by its singular value and we obtain the first output basis vector, one, zero, zero.

Apply A to the second input direction and we obtain zero. That direction spans the kernel.

To finish the output basis, we can choose the other two coordinate axes in three-dimensional space. They are orthogonal to the first output vector and to each other.

In these specially chosen input and output coordinates, A does something very simple: it multiplies the first input coordinate by square root of two and sends the second to zero. Nothing else happens.

The complicated-looking relationship between the original coordinate systems has been absorbed into the choices of orthonormal bases.

## Putting the pieces into a factorization

Let V be the matrix whose columns are the orthonormal input eigenvectors we constructed. Let U be the matrix whose columns form the orthonormal output basis.

These are unitary matrices in complex coordinates, or orthogonal matrices in real coordinates.

Between them, place a rectangular diagonal matrix called Sigma. Along its diagonal are the singular values, in decreasing order. The remaining entries are zero.

The transformation A can then be written as U times Sigma times V adjoint.

Read that formula from right to left. First, V adjoint expresses the input in the special input basis. Second, Sigma independently stretches each coordinate by a nonnegative amount, possibly collapsing some to zero. Third, U places the result into the output space using the chosen output basis.

That is the singular-value decomposition.

We did not assume that A was normal, symmetric, square, or invertible. We only used finite-dimensional inner-product geometry and the spectral theorem for the positive Gram operator.

## What is intrinsic, and what can vary?

The ordered singular values are determined by A. They do not depend on which orthonormal bases we used to represent it. They are the eigenvalues of the modulus, with the appropriate zero-padding convention for rectangular matrices.

The singular vectors are less rigid.

If two positive singular values are equal, we can choose different orthonormal bases within their shared eigenspace and get different, equally valid singular vectors. Even for an isolated singular value, multiplying a complex singular vector by a unit-modulus phase changes its coordinates without changing the underlying decomposition when the corresponding output vector changes compatibly.

And when a singular value is zero, there is no associated normalized image vector. Choices made when completing the output basis are not determined by A.

This repeats a theme from spectral theory: eigenvalues and eigenspaces carry more intrinsic information than a particular selected basis.

## The two Gram operators and rank

The source Gram operator A adjoint A and the output Gram operator A A adjoint live on different spaces. Yet they have the same *positive* eigenvalues, counted with multiplicity.

We can now see why. Every positive singular value sigma yields an input vector v and output vector u satisfying A v equals sigma u. Applying A adjoint to u gives sigma v. It follows that A A adjoint acts on u by sigma squared, just as A adjoint A acts on v.

The reverse construction works too for every nonzero eigenvalue, so the positive eigenspaces match in dimension. Their zero eigenspaces can have different dimensions because E and F need not have equal dimensions.

The number of positive singular values is the rank of A. And the largest singular value is the operator norm of A: the largest amount any unit input can be stretched.

Later, sums and functions of singular values will define the Schatten norms and the unitarily invariant norms used in Davis–Kahan estimates.

## The bridge to polar decomposition

The modulus tells us the stretching factors. The S V D also tells us how to carry each nonzero input stretching direction to its output direction without changing length.

That second operation can be assembled into a partial isometry. Composing the modulus with that partial isometry recovers A.

We will construct this factorization next, including what happens on the kernel and why the partial isometry is not always a unitary operator.

For now, reconstruct the proof that positive Gram eigenvectors produce orthonormal output directions. Explain why division by a singular value requires that it be positive. Then work through the three-by-two example and identify its rank, kernel, operator norm, and one possible pair of orthonormal input and output bases.

If you can do those things, the S V D is no longer merely a formula to remember. You have built it.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

Let \(A:E\to F\) be a finite-dimensional linear map over \(\mathbb R\) or \(\mathbb C\). Choose an orthonormal eigenbasis \(v_i\) of \(A^*A\), with eigenvalues \(\lambda_i\ge0\). Let \(\sigma_i=\sqrt{\lambda_i}\). For \(\sigma_i>0\), define \(u_i=Av_i/\sigma_i\); these vectors are orthonormal. Extend to an orthonormal basis of \(F\). Then

\[
A=U\Sigma V^*,\qquad |A|=V(\Sigma^*\Sigma)^{1/2}V^*,
\]

where \(\Sigma\) is rectangular diagonal with nonnegative entries and suitable zeros. The number of positive singular values is \(\operatorname{rank}A\), and \(\|A\|_{\mathrm{op}}=\max_i\sigma_i\), with value zero if there are no positive singular values.

**Lean bridge.** The DKPS-staged file `ForTauCeti/Analysis/InnerProductSpace/RectangularSingularValues.lean` proves equality of the nonzero Gram spectral multiplicities. Its exact theorem signature is:

```lean
theorem finrank_eigenspace_adjointCompSelf_eq_selfCompAdjoint
    (A : E →ₗ[𝕜] F) (μ : 𝕜) (hμ : μ ≠ 0) :
    finrank 𝕜 (Module.End.eigenspace (A.adjoint.comp A) μ) =
      finrank 𝕜 (Module.End.eigenspace (A.comp A.adjoint) μ) :=
```

The corresponding equivalence is explicitly constructed by `nonzeroEigenspaceEquivAdjointCompSelfSelfCompAdjoint`, using the action \(x\mapsto Ax\) and inverse \(y\mapsto\mu^{-1}A^*y\). Thus this bridge captures the multiplicity-preserving argument from the spoken proof rather than merely mentioning singular values by name.

The same source also gives the exact relationship between singular values and the output Gram eigenvalues:

```lean
theorem sq_singularValues_selfCompAdjoint (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 F = n) (i : Fin n) :
    A.singularValues i ^ 2 = (isSymmetric_self_comp_adjoint A).eigenvalues hn i := by
```

`A.singularValues` is the zero-padded finite sequence used by the library. `finrank` is dimension, and `Module.End.eigenspace` packages the eigenspace as a submodule. The accepted TauCeti singular-value machinery now supplies portions of the construction consumed by this local bridge; that does not erase the DKPS donor history.

**Reconstruction:** Prove orthonormality of \(u_i=Av_i/\sigma_i\), identify the kernel from zero Gram eigenvalues, and derive the rectangular formula \(U\Sigma V^*\). Explain why an output Gram operator has additional zero eigenvalues if the output dimension is larger than the rank.
