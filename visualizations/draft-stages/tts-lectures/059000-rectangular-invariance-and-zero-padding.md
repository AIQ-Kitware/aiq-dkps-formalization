# 059000 — Rectangular invariance and zero padding

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `023000` rectangular Gram operators; `036000` SVD; `057000` Schatten norms; `058000` symmetric gauges. **Next:** pinching and block direct sums.

<!-- BEGIN SPOKEN LECTURE -->

# The same map inside a larger space

Imagine a linear map that sends a two-dimensional input into three-dimensional output space. Suppose we add a fourth output coordinate, but the map always puts zero in that new coordinate. The map has not changed how it stretches any input. Should its norm change?

For the operator, Frobenius, nuclear, and Schatten norms, the answer is no. But this conclusion relies on more than invariance under square unitary changes of coordinates. We must understand isometric embeddings, rectangular singular values, and the precise role of zero padding.

The geometric issue is that changing coordinates within one space and embedding that space into a larger one are different operations. Today we will prove which singular values survive an embedding, then identify what assumptions a consistent cross-dimensional norm family needs.

## The most direct calculation

Let A take real two-dimensional inputs to real three-dimensional outputs. It sends the first input basis vector to four times the first output basis vector, and the second to two times the second output basis vector. It never uses the third output coordinate.

The matrix has three rows and two columns, with four and two on the first two diagonal positions and zeros everywhere else.

Its adjoint followed by itself is a two-by-two diagonal matrix with entries sixteen and four. Its singular values are therefore four and two.

Its self-composition with the adjoint, in the other order, is a three-by-three diagonal matrix with entries sixteen, four, and zero. The positive eigenvalues are still sixteen and four, with an extra zero because the output space has an unused direction.

Now place the entire output space inside a four-dimensional space by appending one more zero row. The adjoint Gram operator is unchanged. The positive singular values are unchanged, and so are the operator, Frobenius, and nuclear norms.

This calculation suggests a general proof.

## Isometric embeddings preserve the input Gram operator

Let J be a linear isometric embedding from an output space F into a larger output space G. Saying that J is an isometry means that the length of J y equals the length of y for every y in F.

For inner-product spaces, this implies that the adjoint of J followed by J is the identity on F. We can prove it directly: preserving all lengths also preserves inner products by polarization. The defining property of the adjoint then gives J adjoint J equal to the identity.

Form the new operator J followed by A. Its Gram operator is A adjoint followed by J adjoint, then J, then A.

Because J adjoint J is the identity, the middle factors cancel. We recover A adjoint A exactly.

Therefore the two maps have identical source Gram operators, identical singular-value lists indexed by the source space, and identical nonzero singular values. Their singular vectors in the output space may occupy different ambient coordinates, but their action on inputs has the same geometry.

This argument is stronger than a calculation for a particular padding matrix. It works for any isometric embedding, even one that sends the original output coordinates to a tilted subspace of the larger output space.

## What happens when the input space grows?

Padding columns is related, but the direction of the construction changes.

Suppose E is included isometrically in a larger input space H. We want a map from H to F that agrees with A on the old input subspace and sends every orthogonal new direction to zero.

The natural formula is A followed by the adjoint of the inclusion. The inclusion's adjoint takes a vector in H and extracts its component in E. The resulting map uses exactly the old input coordinates and discards the new ones.

Relative to the orthogonal splitting of H into the included copy of E and its orthogonal complement, the new Gram operator has two diagonal blocks: A adjoint A on the old part, and zero on the new part.

Hence all positive singular values are unchanged, and the enlarged source contributes additional zero singular values. Unlike output padding, input padding changes the length of the full source-indexed singular-value list. It does not change the nonzero part of that list.

This is why the convention for counting singular values matters. A rectangular matrix has two Gram operators of different sizes. One is indexed by input dimension; the other by output dimension. They share the positive spectral data, but their zero multiplicities need not agree.

## A short proof using the singular-value decomposition

There is a second route to the same result. Start with the singular-value decomposition of A. It gives orthonormal right singular vectors, orthonormal left singular vectors for the positive singular values, and a diagonal list of stretching factors.

Embedding the output sends every left singular vector to another orthonormal vector, because the embedding preserves inner products. The right singular vectors and singular values can remain unchanged.

Enlarging the input and adding zero action contributes extra right singular directions with stretching factor zero. Thus the positive singular blocks remain exactly the same.

Both perspectives are useful. The Gram proof is coordinate-free and short. The singular-vector proof makes the geometry visible.

## A warning about invariance in each dimension

Here is a tempting but incorrect argument: if a norm is unitarily invariant on every matrix space, adding zero rows or columns must preserve its value.

It need not.

For example, define a separate norm on matrices with m rows and n columns by multiplying their ordinary operator norm by m plus n. For each fixed shape, this is a valid unitarily invariant norm. But padding a zero row changes m, so it changes the assigned value even though the nonzero singular values remain unchanged.

Thus separate invariance within each matrix space does not force compatibility between different matrix shapes.

To obtain padding invariance, we must choose a cross-dimensional rule that gives the same measurement to a singular-value list after adjoining zeros. Schatten norms have this property. So do Ky Fan norms when the same prefix length is used, with missing singular values treated as zero.

An operator-ideal norm family formalizes compatibility with maps between different spaces. In particular, if composing with contractions cannot increase the norm, we can apply that rule in both directions along an isometric embedding and its adjoint to force equality for the embedded map.

The same reasoning applies to the zero-extended input construction. One inequality comes from composition with the inclusion or its adjoint. The reverse inequality comes from recovering A by composing the larger operator with the inclusion.

## Padding is not compression

There is another operation that looks superficially similar: project an operator's outputs onto a smaller subspace, discarding a component that was previously nonzero.

That is compression or contraction, not mere padding. It generally decreases singular values or their aggregate norms, and can decrease them strictly.

Take the map from two-dimensional input to two-dimensional output that stretches the first direction by four and the second by two. Project all outputs onto the first coordinate axis. The second singular value becomes zero. The operator norm stays four, but the Frobenius norm drops from the square root of twenty to four, and the nuclear norm drops from six to four.

The example makes the distinction concrete. Padding preserves all existing output information and adds an unused direction. Projecting may destroy information.

For general contractions, singular-value comparisons lead to bounds of the form: the norm of the composition is at most the operator norm of the contraction times the original invariant norm. When the contraction is an isometry on the relevant range, equality can return.

## Connection to subspace perturbation theory

Later we will compare an operator restricted to a trial subspace with an operator written in the ambient Hilbert space. Or we will transport a rectangular residual from one coordinate chart to another.

Those operations frequently involve isometric inclusions, adjoints of those inclusions, and zero blocks. Without padding invariance, the same residual could acquire different measured sizes merely because we wrote it in a larger ambient space.

The source formalization contains explicit transport constructions for rectangular unitarily invariant seminorms. It also proves that singular values agree when the source Gram operators agree. The latter theorem is the compact mathematical reason behind the zero-row argument.

The next lecture will go beyond preserving a map inside a larger space. We will actively suppress its off-diagonal blocks by a process called pinching, and prove that this operation cannot increase any unitarily invariant norm compatible with the contraction laws.

## What to reconstruct

Compute both Gram operators for the three-by-two example. Then append a zero output row and verify that the source Gram operator does not change. Append a zero input column and identify the extra zero eigenvalue of the new source Gram operator.

Prove the identity J adjoint J equals the identity for an isometric embedding. Use it to prove equality of nonzero singular values under output inclusion.

Finally, construct a dimension-dependent invariant norm that fails zero-padding invariance, and explain exactly which cross-dimensional compatibility property is missing.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

If \(J:F\hookrightarrow G\) is an isometry, then \(J^*J=I_F\), so
\[
(JA)^*(JA)=A^*A.
\]
If \(I:E\hookrightarrow H\) is an isometry, the zero-extended map \(AI^*:H\to F\) has source Gram operator unitarily equivalent to \((A^*A)\oplus 0\). Adding zeros preserves standard cross-dimensionally compatible singular-value gauges. Independent norms on every shape need not satisfy that compatibility.

**Lean bridge (verbatim excerpts).**

`ForTauCeti/Analysis/InnerProductSpace/RectangularSingularValues.lean`:

```lean
theorem singularValues_eq_of_gram_eq {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F'] {A : E →ₗ[𝕜] F} {B : E →ₗ[𝕜] F'}
    (h : A.adjoint ∘ₗ A = B.adjoint ∘ₗ B) : A.singularValues = B.singularValues := by
```

The equality is for finite-dimensional maps with a common source and possibly different codomains; it matches the output-isometry Gram proof.

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Instances.lean`:

```lean
theorem frobenius_linearIsometry_comp
    (ι : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    frobenius 𝕜 E G (ι.toLinearMap ∘ₗ A) = frobenius 𝕜 E F A := by
```

This specialization is the Frobenius identity for an isometric codomain embedding, including a rectangular source and target.

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Transport.lean`:

```lean
@[simp] theorem codomainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] H) :
    N.codomainIsometryTransport ι A = N (ι.toLinearMap ∘ₗ A) :=
```

This is the definitional equality for transporting a rectangular unitarily invariant seminorm along a codomain isometry.

**Reconstruction exercise:** Reprove the principal displayed identity from the spoken lecture, then identify the exact source/target types and extra assumptions in each displayed Lean declaration.
