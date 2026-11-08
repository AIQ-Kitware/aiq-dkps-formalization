# 131000 — The squared displacement of orthonormal frames

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `018000`, `042000`, `052000`, `130000`. **Next:** `132000`.

<!-- BEGIN SPOKEN LECTURE -->

# The squared displacement of orthonormal frames

Proposition four point two asks what happens when we select an orthonormal family in the source subspace, transport every vector by the same unitary, and add up their angular errors. We will prove the lower bound from orthogonal projections and the trace of a positive operator. Along the way we must distinguish the square of a sine from the square of a Euclidean chord.

## One vector, two error measures

Let x be a unit vector in the source subspace U. Let W be an orthogonal or unitary operator that carries U onto V. Write y for W x. Because W is unitary, y is also a unit vector, now in V.

There are at least two natural ways to quantify how much x has changed. The first is its Euclidean displacement, the length of x minus y. Its square is two minus twice the real part of the inner product of x and y.

The second is the square of the sine of the angle between x and y. For real unit vectors, this equals one minus the square of their inner product. For complex vectors it equals one minus the squared modulus of the inner product. In both cases it measures failure to remain on the original one-dimensional line; a change of complex phase has zero sine-angle error but may have nonzero Euclidean displacement.

Proposition four point two uses the second quantity: squared sine of the vector angle. We will keep these two measures separate for the entire lecture. They can have different minimizers because their phase sensitivity differs.

## Projecting gives a universal lower bound

The transported vector y belongs to V. The absolute inner product between x and y is at most the length of the projection of x onto V. This is immediate from writing the inner product with the V projection of x and applying Cauchy–Schwarz.

Subtract squared quantities from one. We find that the squared sine of the angle from x to y is at least one minus the squared norm of the V projection of x.

Since x has length one, the Pythagorean identity for the orthogonal decomposition into V and V perpendicular says that one minus the squared V projection is exactly the squared norm of the projection of x onto V perpendicular.

Thus, for every x in U of length one, the sine-squared angle between x and W x is at least the squared norm of the component of x outside V. There is no optimization over W in this last expression. The right-hand side depends only on the two subspaces.

This is a pointwise inequality, but the vectors that simultaneously make it an equality may not be the same vectors for an arbitrary W. The next step avoids making any simultaneous-attainment assumption.

## Sum over an orthonormal basis

Choose an orthonormal basis u-one through u-r of U. Apply the preceding inequality to each basis vector and add. The total sine-squared angular error for W is at least the sum of the squared norms of the V-perpendicular projections of all those basis vectors.

Define T as the rectangular projection map from U into V perpendicular. The sum on the right is the squared Frobenius norm of T. Equivalently, it is the trace of T adjoint T, its positive Gram operator.

Why is this independent of the chosen orthonormal basis? If we change the basis by a unitary coordinate transformation, the trace of the Gram operator does not change. More concretely, the sum of squared output lengths of T over an orthonormal basis equals the sum of its squared singular values. That identity was the starting point of our Hilbert–Schmidt lectures.

The singular values of T are the sines of the principal angles between U and V. Thus the bound becomes: the sum of sine-squared transport angles over any orthonormal basis of U is at least the sum of sine-squared principal angles.

The source statement is stronger in another direction: it can use an arbitrary Hilbert basis indexed by an infinite set and interpret both sums as extended nonnegative numbers. When the principal sine sequence is not square-summable, the lower bound is infinite, and every admissible transport has infinite total sine-squared error.

## A two-dimensional example

Let U be the span of the first two coordinate vectors in four-dimensional Euclidean space. Let V be spanned by vectors that are obtained by turning the first coordinate plane through thirty degrees and the second through sixty degrees, using orthogonal principal planes.

The sines are one half and square root of three over two. Their squares add to one quarter plus three quarters, which equals one. For every orthonormal pair in U and every orthogonal W mapping U onto V, the sum of squared sines of the angles between each chosen vector and its transported image is at least one.

For the canonical direct rotation and the principal basis, the individual angles are exactly thirty and sixty degrees. Therefore equality holds, and the lower bound is sharp.

Now change the orthonormal basis within U by forty-five degrees. The two new basis vectors are mixtures of the original principal directions. Their individual escape norms are generally different from the original sine values, but their squared escape norms still add to one. This is because the Frobenius norm does not depend on the basis.

If we also rotate the target basis after the canonical transport, the angular errors may increase. They cannot decrease below the total geometric leakage of U into V perpendicular.

## Why squared sine is convenient

For a general set of vectors, summing angles themselves does not produce a simple trace identity. Squaring the sine turns the problem into the sum of squared norms of a linear map. That is why spectral theory enters so naturally.

In the complex setting, the modulus of an inner product is phase independent. A unitary can multiply a vector by a phase without changing its one-dimensional direction, so sine-squared angular error ignores that phase. By contrast, Euclidean chord displacement includes the phase. Later, the counterexample to unsquared ambient displacement will exploit the fact that changing phases and mixing directions can reduce the sum of chords.

There is another useful comparison. For a small angle theta in radians, sine squared theta is approximately theta squared, and the squared chord two minus two cosine theta is also approximately theta squared. But those are only approximations near zero. At a right angle, sine squared theta equals one, while the squared chord equals two. A proof involving one expression cannot be silently relabeled as a proof about the other.

## Infinite-dimensional detail

An infinite-dimensional source subspace may have a countable or more general Hilbert basis, depending on the setting. The sum of squared escape norms is naturally a nonnegative extended sum. The positive Gram operator need not be trace class. If the sum diverges, we retain a valid inequality in the extended nonnegative reals rather than claiming a finite Frobenius norm.

The formalized source result uses the principal sine sequence from approximation numbers. It keeps the inherited compactness and crossed-defect hypotheses in its source-shaped wrapper, though the underlying inequality has a stronger derivation that does not require those assumptions. This is an example of separating a theorem's natural generality from the exact hypotheses under which the historical paper presented it.

## End of the argument

We proved the inequality without choosing a special competing unitary and without solving a matrix optimization problem. Each transported vector lies in V. Its angular error is at least the energy that its original direction has outside V. Summing that projection energy over an orthonormal basis produces the squared Hilbert–Schmidt norm of the escape map, which is the sum of the squared principal sines.

Next we will return to full ambient displacement, but keep the square inside a positive operator. The resulting norm inequality is much stronger than this basis-energy estimate, and its proof uses block pinching and Ky Fan sums.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For an orthonormal basis \((u_i)\) of \(U\), \(W U=V\), and \(\sin^2\angle(x,y)=1-|\langle x,y\rangle|^2\) for unit vectors,
\[
\sum_i \sin^2\angle(u_i,Wu_i)
\ge \sum_i\|P_{V^\perp}u_i\|^2
=\|P_{V^\perp}|_U\|_{\mathrm{HS}}^2
=\sum_j\sin^2\theta_j.
\]
In infinite dimension interpret as sums in \([0,\infty]\). The theorem's angular square is **not** the squared Euclidean chord \(\|u_i-Wu_i\|^2\). The Section 4 source-shaped wrappers carry compactness and crossed-defect hypotheses even though the underlying estimate is more general.

## Exact Lean declaration excerpts

**`proposition4_2_compact_nonacute`.** The `HilbertBasis` lives in the source subspace. The summands are squared *sine-angle* errors (`displacementAngleSineSq`), not squared Euclidean displacement; `ENNReal` supports possibly divergent sums.

`DavisKahan/Sources/DavisKahan1970/Section4.lean` — `proposition4_2_compact_nonacute` (exact declaration header; proof body omitted):

```lean
theorem proposition4_2_compact_nonacute
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (_hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    {ι : Type u4} (b : HilbertBasis ι ℂ U)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal
        (DavisKahan.Section4.displacementAngleSineSq W ((b i : U) : H)) :=
```

**`proposition4_2_compact_nonacute_real`.** The real variant uses a real Hilbert basis and the real squared sine-angle definition. Compactness and crossed-defect equivalence are retained as source-scope hypotheses.

`DavisKahan/Sources/DavisKahan1970/Section4Real.lean` — `proposition4_2_compact_nonacute_real` (exact declaration header; proof body omitted):

```lean
theorem proposition4_2_compact_nonacute_real
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (_hcrossed : CrossedDefectsEquivalent U V)
    {ι : Type v} (b : HilbertBasis ι ℝ U) (W : E →L[ℝ] E)
    (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal (displacementAngleSineSqR W ((b i : U) : E)) :=
```

