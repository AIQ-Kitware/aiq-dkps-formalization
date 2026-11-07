# Frame operators and Parseval identities

<!-- BEGIN SPOKEN LECTURE -->

Last time we built a Gram operator from a collection of vectors. We started with coefficients, synthesized a vector, and analyzed it again. The result lived in coefficient space. Today we will reverse the order. We will start with an actual vector, measure it against the collection, and reconstruct from those measurements. The result lives back in the original space.

This new composition is the frame operator. And its behavior tells us whether a family of vectors gives a faithful, incomplete, distorted, or redundant way of describing the space.

There is an important distinction to keep in mind. A collection of vectors can record every direction in a space without being a basis. In fact, it can contain repeated vectors and still allow perfect reconstruction, provided we interpret the measurements correctly.

## Which way do the arrows go?

Recall our two machines. Synthesis accepts a list of coefficients and returns their weighted sum of selected vectors. Analysis accepts a vector and returns its inner products with the selected vectors. We called synthesis S, and analysis S star, because they are adjoints.

The Gram operator from the previous lecture was S star followed by S, or, said in the usual order of composition, S star times S. It acts on coefficient lists.

The frame operator is the other product: S times S star. It acts on ambient vectors.

Let us calculate what this means. Given a vector x, first measure its inner product with every selected vector. Then multiply each selected vector by its measured coefficient and add the contributions. So the frame operator sends x to the sum, over all the chosen vectors, of each vector multiplied by its inner product with x.

If you see the expression S times S star later, this is what it is doing. It is rebuilding a vector from inner-product measurements, without yet guaranteeing that the reconstruction equals the original.

## An example where reconstruction distorts

Take the ordinary plane and select three vectors. One points right with length one. The second is another copy of that same right-pointing vector. The third points up with length one.

Now measure the vector x whose coordinates are p and q. Analysis returns three numbers: p, p, and q. Synthesis then uses those three numbers against our three selected vectors. The reconstructed vector has coordinates two p and q.

Our frame operator doubles the horizontal component and leaves the vertical component unchanged.

Nothing mysterious happened. We measured the same horizontal direction twice, then added both contributions. Redundancy increased its weight.

Compare that with our previous Gram operator. The Gram operator acts on the three-dimensional coefficient space, even though the physical vectors occupy only a plane. Its matrix has repeated information. The frame operator acts directly on the plane and reveals the different weights assigned to its directions.

This example illustrates why the order of composition matters. In general, S star S and S S star are not equal. They may not even act on spaces of the same dimension.

## Positivity and what the measurements know

There is a simple identity behind all frame theory. Take the inner product of x with the frame operator applied to x. Since the frame operator is S S star, move S across the inner product using the adjoint relationship. What remains is the squared length of S star of x.

But S star of x is the list of inner-product measurements. Therefore the frame quadratic form equals the sum of the squared magnitudes of all those measurements.

This is automatically nonnegative. So the frame operator is positive semidefinite, just like the Gram operator.

More interestingly, the quadratic form vanishes exactly when every measurement vanishes. If every inner product with a chosen vector is zero, then x is perpendicular to the span of the chosen family.

For a finite family, that means the kernel of the frame operator is exactly the orthogonal complement of the family’s span.

Notice the contrast. The Gram operator's kernel detects redundant coefficient combinations. The frame operator's kernel detects directions the family cannot see at all.

That is a useful mental picture: coefficient redundancy on one side, invisible ambient directions on the other.

## Orthonormal families: reconstruction becomes projection

Now choose vectors that are mutually perpendicular and each have length one. Such a family is orthonormal. In the plane, use the horizontal and vertical unit vectors.

Analysis of the vector with coordinates p and q gives p and q. Synthesis produces the same vector. The frame operator is the identity.

Suppose instead that we keep only the horizontal unit vector. Analysis gives p, and synthesis reconstructs the horizontal vector with coordinate p. The vertical part is lost. The frame operator is not the identity, but it is the orthogonal projection onto the chosen line.

This generalizes to any finite orthonormal family. Analysis followed by synthesis gives the orthogonal projection onto its span. The reason is that the difference between x and its reconstruction has zero inner product with every selected vector, so it is orthogonal to their span. We have already proved that this characterizes orthogonal projection.

The measurement identity then becomes a Pythagorean statement. The sum of squared inner-product measurements equals the squared length of the projection.

That sum can never exceed the squared length of x. This is Bessel's inequality.

If the orthonormal family spans the entire finite-dimensional space, its projection is the identity. The sum of squared measurements equals the squared length of x itself. This is Parseval's identity.

Parseval is not merely a rule for adding squares of coordinates. It says analysis preserves the total squared length of a vector when no direction has been left out.

## Why this still matters in infinite dimensions

Consider a sequence space whose vectors are infinite lists of numbers with summable squared magnitudes. The coordinate unit vectors form an infinite orthonormal family. Measuring a sequence against these unit vectors recovers its entries, and the sum of the squared magnitudes of those entries gives its squared length.

Here, the reconstruction involves a limit of finite partial sums. We do not simply announce an infinite sum and assume it converges. Instead, the squared length of the tail equals the sum of squared magnitudes of its remaining entries, which tends to zero. That proves the partial reconstructions converge in the Hilbert-space norm.

For a general infinite orthonormal family, the same pattern requires Bessel's inequality and the Hilbert-space completeness developed earlier. The exact statement is that Parseval's identity holds when the closed span of the family is the whole space.

The word closed matters. Finite combinations may only approximate a vector, rather than represent it exactly. We have already seen why closed span is the right concept.

## Frames without orthogonality

Return to our three vectors in the plane, with the horizontal unit vector counted twice and the vertical one counted once. For x with coordinates p and q, the measurement energy is two p squared plus q squared.

This is not equal to the squared length of x, which is p squared plus q squared. But it lies between one times that squared length and two times that squared length.

We say our family has a lower frame bound of one and an upper frame bound of two. More generally, a frame is a family for which positive constants bound the total squared measurement energy below and above by corresponding multiples of the vector's squared length.

The lower bound says that no nonzero direction is invisible. The upper bound says the measurements cannot amplify arbitrarily relative to the input. For finite families, an upper bound always exists; the lower bound is the more informative requirement for spanning the ambient finite-dimensional space.

In our example, the frame operator stretches horizontal components by two and vertical components by one. Because neither scale factor is zero, we can undo this stretching. If the frame operator is invertible, reconstruction can be corrected: first apply the inverse frame operator, then analyze and synthesize. This gives the original vector back.

We have not yet developed every theorem about invertible positive operators, so treat that construction here as a finite-dimensional observation. Its full operator-theoretic form will become clearer after our spectral theory lectures.

## Redundancy can coexist with a perfect identity

Here is one last experiment. Keep two copies of the horizontal direction, but shorten each of them to length one over the square root of two. Keep the vertical unit vector unchanged.

For a vector with coordinates p and q, analysis produces p over the square root of two, the same number again, and q. The sum of their squared magnitudes is one half p squared plus one half p squared plus q squared. That equals p squared plus q squared.

The family is redundant, because it has three vectors in a plane. Yet its measurements satisfy Parseval's identity exactly, and the frame operator is the identity.

This is a Parseval frame. It is not an orthonormal basis. Analysis is length-preserving, but its outputs occupy only a two-dimensional subspace of the three-dimensional coefficient space. Synthesis after analysis recovers every ambient vector; analysis after synthesis is a projection on coefficient space, not the identity there.

That distinction is worth holding onto. Exact reconstruction does not imply unique coordinates, and Parseval's identity does not require an orthonormal basis.

## Reconstruct the argument

Before moving on, try to answer four questions without looking at a formula. Why does a frame operator act on the ambient space while a Gram operator acts on coefficient space? Why is the frame operator positive? What precisely gets lost when an orthonormal family is incomplete? And how can a redundant family satisfy Parseval's identity?

Next we will focus on the special case where the selected vectors are orthonormal. Synthesis then becomes a length-preserving embedding of coefficient space into the ambient space. Its adjoint reveals a particularly important pair of identities: the identity on coefficient space and the projection onto the represented subspace.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `S : 𝕜^ι → E` denote finite synthesis of a family `v : ι → E`, with analysis `S*`. The operators have different domains:

\[
G = S^*S : \mathbb K^{\iota}\to\mathbb K^{\iota}, \qquad
F = SS^* : E\to E.
\]

For every `x : E`,

\[
\langle x,Fx\rangle=\|S^*x\|^2=\sum_{i\in\iota}|\langle v_i,x\rangle|^2.
\]

The finite-frame condition is \(a\|x\|^2\le\sum_i |\langle v_i,x\rangle|^2\le b\|x\|^2\) for constants \(0<a\le b\). A Parseval frame has `F = I`, even if it is redundant. For an orthonormal family, `F` is the projection onto its span; for an orthonormal basis, `F = I`.

**Lean bridge.** The DKPS-developed source `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` defines the two compositions and proves the quadratic-form identity:

```lean
/-- Frame operator `synthesis ∘ analysis` on the ambient space. -/
noncomputable def finiteFrameOperator (v : ι → E) : E →ₗ[𝕜] E :=
  (finiteSynthesis 𝕜 v).comp (finiteAnalysis 𝕜 v)

/-- Gram operator `analysis ∘ synthesis` on coefficient space. -/
noncomputable def finiteGramOperator (v : ι → E) :
    EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (finiteAnalysis 𝕜 v).comp (finiteSynthesis 𝕜 v)
```

The same module proves the positivity of the frame operator:

```lean
/-- The frame operator is positive. -/
theorem finiteFrameOperator_isPositive (v : ι → E) :
    (finiteFrameOperator 𝕜 v).IsPositive := by
  rw [finiteFrameOperator_eq_adjointCompSelf]
  exact (finiteAnalysis 𝕜 v).isPositive_adjoint_comp_self
```

It also proves `norm_sq_finiteAnalysis` and `re_inner_finiteFrameOperator_eq_sum_sq`, which are the formal squared-measurement and frame-quadratic-form identities. `EuclideanSpace 𝕜 ι` is coefficient space; `E` is ambient space. `RCLike.re` takes the real part of a complex inner product (and is the identity for real scalars). The file documents its origin in the DKPS project and its movement into the `ForTauCeti` staging layer.
