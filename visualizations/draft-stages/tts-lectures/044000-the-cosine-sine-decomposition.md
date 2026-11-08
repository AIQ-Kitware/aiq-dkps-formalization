# 044000 — The cosine–sine decomposition

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `020000` coordinate embeddings; `026000` finite spectral theorem; `036000` SVD; `042000` principal angles; `043000` cross projections. **Next:** Halmos two-projection decomposition.

<!-- BEGIN SPOKEN LECTURE -->

# Can two subspaces be understood one plane at a time?

For two subspaces, their cosine and sine overlap operators satisfy a Pythagorean identity: the squared cosine contribution plus the squared sine contribution is the identity on the appropriate coordinates. Principal planes turn this operator relation into simple two-by-two projection matrices.

We will show that, in finite dimensions, a pair of subspaces can be studied through mutually perpendicular two-dimensional planes, together with directions where the projections already agree or are completely opposed.

On each tilted plane, the entire relationship reduces to an ordinary angle theta. This is the cosine–sine decomposition. It is a geometric explanation of why complicated projection formulas so often reduce to expressions involving sine theta, cosine theta, and sine of twice theta.

## Begin with one tilted pair

Let U be the horizontal axis in a two-dimensional plane. Choose unit vectors e along U and f perpendicular to U.

Let V be the line making an angle theta with e, where theta lies strictly between zero and ninety degrees. Choose its unit direction v to be cosine theta times e plus sine theta times f.

The orthogonal projection P onto U takes the e component of a vector and discards the f component. Its matrix in the ordered basis e, f has one in the upper-left corner and zeros everywhere else.

To project onto V, take the inner product with v and multiply by v. When we calculate that operation in the e, f basis, the entries of Q are cosine squared theta in the upper-left, sine squared theta in the lower-right, and cosine theta times sine theta in each off-diagonal position.

These four entries are not an arbitrary trick. They follow from the fact that Q is the rank-one operator that maps x to the inner product of v with x, multiplied by v.

Try projecting e. The result is cosine theta times v, which has an e component of cosine squared theta and an f component of cosine theta times sine theta. Project f and we get sine theta times v. Those are the two columns of Q.

Now calculate the square of Q. The cosine-squared plus sine-squared identity makes the result equal Q. Likewise, Q equals its transpose, or its adjoint in the complex case. So the block really is an orthogonal projection.

## Where does the paired plane come from?

For a single tilted line, we simply drew the perpendicular vector f. In higher dimensions we must show that suitable vectors f exist and remain orthogonal across different pairs.

Start with two subspaces U and V of a finite-dimensional Hilbert space. Let u be a unit principal vector in U and v its matched unit principal vector in V, with principal angle theta strictly between zero and ninety degrees.

We know from the singular-value construction that the projection of v onto U equals cosine theta times u. This is a defining property of a correctly matched principal pair.

Subtract that projection from v. The result is perpendicular to U. Its squared length is one minus cosine squared theta, hence sine squared theta.

Because theta is strictly between zero and a right angle, sine theta is positive. Divide the perpendicular remainder by sine theta and call the result f.

We have just derived the decomposition: v equals cosine theta times u plus sine theta times f. And f is a unit vector perpendicular to U.

This construction explains the role of the angle restriction. If theta were zero, the perpendicular remainder would vanish and there would be nothing to normalize. Zero-angle directions must be treated separately. At a right angle, the formula itself remains valid, but the corresponding direction is a perpendicular defect rather than a genuinely tilted overlap.

## Why the different planes do not interfere

Principal vectors come from a singular-value decomposition. We can choose the u vectors to be orthonormal within U and the v vectors to be orthonormal within V. Their cross-inner-products vanish for distinct indices.

Each f vector is formed by subtracting cosine theta times its matched u vector from v, then dividing by sine theta.

For two distinct nontrivial indices, expand the inner product of the corresponding f vectors. The inner product of the v vectors is zero. The cross-inner-products vanish. The inner product of the u vectors is zero. Thus the f vectors are orthogonal.

And by construction every f lies in U perpendicular, so every f is perpendicular to every u. Therefore the two-dimensional planes spanned by each u and its f are mutually perpendicular.

On each plane P and Q have exactly the two-by-two matrices we just derived.

This is more than a convenient change of coordinates. Both projections preserve each such plane, and they preserve its orthogonal complement. In operator language, each principal plane is a reducing subspace for both projections.

## Two independent angles

Picture two perpendicular copies of our tilted-line example, sitting inside four-dimensional space. In the first plane, let the target line tilt by thirty degrees. In the second, let it tilt by sixty degrees.

The first subspace U is spanned by the first coordinate direction in each plane. The second subspace V is spanned by the corresponding tilted directions.

If we order the ambient basis by principal plane, P has two copies of the simple diagonal projection block. Q has one cosine–sine block for thirty degrees and another for sixty degrees.

Suppose we take a unit vector in U supported entirely in the first plane. Its perpendicular escape into V perpendicular has length sine thirty degrees, or one half. A unit vector in the second source direction escapes with length sine sixty degrees, or the square root of three divided by two.

The operator norm of the escape map picks the larger value. Its Frobenius norm, by contrast, squares both values, adds them, and takes the square root.

Thus different norms summarize the same list of geometric angles differently. That observation will matter when we move from a single sine-theta bound to unitarily invariant norms.

## What about zero and ninety degrees?

The neat two-dimensional tilted blocks require genuine intermediate angles. A complete decomposition must also account for the endpoints.

An angle of zero describes a direction shared by U and V. On that direction both projections equal identity. No two-dimensional rotation is needed.

A right angle describes a direction in one subspace perpendicular to the other. On a source direction of that kind P equals identity while Q equals zero. If the opposite subspace has an unmatched perpendicular direction, the projection values are reversed.

Directions perpendicular to both U and V are also possible. On those, both projections equal zero.

These one-dimensional or higher-dimensional pieces are not errors in the decomposition. They are essential parts of the complete answer, especially when subspace dimensions differ.

Sometimes one can pair a source-only and target-only right-angle direction and display them as a ninety-degree two-by-two block. But such a pairing requires matching dimensions; it cannot always be done for every defect direction.

## A balanced complete block theorem

There is a particularly clean case. Suppose U and V have the same finite dimension, and the ambient space has exactly twice that dimension.

Then U and U perpendicular have matching dimensions. We can choose a complete orthonormal basis for U and a complete orthonormal basis for its complement so that the target vectors take the form cosine theta times a source vector plus sine theta times the matching complement vector.

In these coordinates, P is a block matrix with identity in the upper-left and zero in the other three blocks. Q has diagonal matrices of cosine squared and sine squared on its diagonal, and cosine-times-sine diagonal matrices in its crossing blocks.

The zero-angle and right-angle cases can be included in this balanced representation by choosing the unused complementary basis vectors appropriately. But this neat global matrix is not the only form of the cosine–sine decomposition, and its dimension assumptions should not be silently extended to arbitrary pairs.

For unequal dimensions or an ambient space with extra orthogonal directions, we instead retain the smaller principal planes and the remaining one-sided and exterior pieces.

## Why this decomposition is useful

Look again at the off-diagonal entry of Q on one principal plane. It is cosine theta times sine theta. From elementary trigonometry, twice that product is sine of twice theta.

That simple observation foreshadows the double-angle theorems. They arise in part because the off-diagonal blocks of projection operators naturally contain sine theta times cosine theta.

There is another payoff. A rotation through theta maps e to v inside a principal plane. Because the planes are perpendicular, we can rotate them independently. Combining those planar rotations is the beginning of the direct rotation between subspaces.

It is crucial, though, to distinguish a canonical choice of motion from the mere existence of some unitary map. We will develop that distinction in its own lectures.

## Reconstruction

Start with an orthonormal pair e and f, and let v equal cosine theta times e plus sine theta times f. Derive the complete matrix of the projection onto v, directly from the rank-one projection formula. Verify its square equals itself.

Next, start with a principal pair u and v, and derive f from the component of v perpendicular to U. Explain why different principal pairs produce orthogonal planes. Finally, tell me what goes wrong if you try to divide by sine theta at a zero angle.

If you can do those steps, you have not memorized a cosine–sine block. You have constructed it.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

In a principal plane with orthonormal basis \((u,f)\), \(v=cu+sf\), \(c=\cos\theta\), \(s=\sin\theta\), the projections are
\[
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad Q=\begin{pmatrix}c^2&cs\\cs&s^2\end{pmatrix}.
\]
For \(0<\theta<\pi/2\), \(f=(v-cu)/s\in U^\perp\). Different principal pairs yield orthogonal two-dimensional reducing subspaces. At \(\theta=0\), treat common directions separately; at \(\theta=\pi/2\), retain defect dimensions rather than assuming they always pair off.

**Lean bridge.** `ForTauCeti/Analysis/InnerProductSpace/Projection/CosineSineBasis.lean` contains the balanced full-ambient matrix form:

```lean
theorem exists_cosineSine_projection_matrices
    (K L : Submodule 𝕜 E)
    (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L)
    (hdim : Module.finrank 𝕜 E = 2 * Module.finrank 𝕜 L) :
    ∃ b : OrthonormalBasis
        (Fin (Module.finrank 𝕜 L) ⊕ Fin (Module.finrank 𝕜 L)) 𝕜 E,
      LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap =
        Matrix.fromBlocks 1 0 0 0 ∧
      LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap =
        Matrix.fromBlocks
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) =>
            ((Real.cos (K.principalAngles L i)^2 : ℝ) : 𝕜)))
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) => ((Real.cos (K.principalAngles L i) *
            Real.sin (K.principalAngles L i) : ℝ) : 𝕜)))
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) => ((Real.cos (K.principalAngles L i) *
            Real.sin (K.principalAngles L i) : ℝ) : 𝕜)))
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) =>
            ((Real.sin (K.principalAngles L i)^2 : ℝ) : 𝕜))) := by
```

The hypotheses require **equal source and target dimensions** and **ambient dimension twice their common dimension**. The conclusion supplies an ambient orthonormal basis and both projection matrices, including the cosine-squared, sine-squared, and crossing cosine-times-sine blocks. In `ForTauCeti/Analysis/InnerProductSpace/Projection/CosineSineBlocks.lean`, the following theorem records finite principal-plane block data, including the reduction properties:

```lean
theorem cosineSineFrameBlock_data
    (K L : Submodule 𝕜 E)
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L)
```

These are excerpts of existing declaration headers; their full hypotheses and conclusions are in the cited Lean modules. The distinction is between the balanced complete matrix model and selected reducing principal planes available under their respective assumptions.

**Reconstruction:** Derive the rank-one block, reconstruct \(f\) for a nonzero angle, prove the principal planes are mutually orthogonal and reducing, and state what additional bookkeeping the endpoint and unequal-dimension cases require.
