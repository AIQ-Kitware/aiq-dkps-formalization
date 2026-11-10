# 005000 — Canonical direct rotation

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 049000. **Section:** geometry. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

# Which rotation belongs to two subspaces?

Suppose someone hands us two lines in the plane. We can rotate the first line onto the second. But even there, the instruction does not specify a unique answer. We might turn through the smaller angle, turn the other way through a larger angle, or first rotate and then reflect along a suitable direction.

For two subspaces of a Hilbert space, this freedom is much larger. We can move vectors within the source subspace, and within its orthogonal complement, while still sending the source subspace onto the target.

A particular unitary transport can be constructed from the two orthogonal projections. We ask why this choice is the direct rotation, what conditions make it unique, and how its square is connected to a product of reflections.

## Begin with the planar picture

Let U be the horizontal line and V be the line tilted counterclockwise by theta degrees, with theta strictly between zero and ninety degrees.

There is an ordinary rotation through theta. There is also a rotation through theta plus one hundred eighty degrees. Both carry U onto V, because a line has no preferred orientation. But the second motion sends a horizontal unit vector to the negative of the nearest unit vector along V.

That difference appears in an inner product. The smaller rotation moves a horizontal unit vector to a vector whose inner product with it is cosine theta, which is positive. The larger one gives negative cosine theta.

So positivity can help choose between transports. But in higher dimensions, merely asking that one particular inner product be positive is not enough. We need a condition on whole diagonal blocks of the operator, and we must keep track of how the two off-diagonal blocks relate.

## Reassemble the two projections

Write P for projection onto U and Q for projection onto V. A natural transport candidate K is the sum of Q P and the product of identity minus Q with identity minus P.

It sends the U component toward V and the U-perpendicular component toward V perpendicular. Its squared modulus is identity minus the square of P minus Q.

Let C be the positive square root of that squared modulus. On a principal plane with angle theta, C multiplies each vector by cosine theta. So K acts there like cosine theta times an ordinary rotation.

If the operator gap between P and Q is strictly below one, C has a bounded inverse. Then the direct rotation W is K times C inverse. The factors give a unitary that intertwines the projections, and each principal plane rotates by its angle.

This already proves existence under the strong, uniform gap condition. But we should ask whether invertibility of C is logically necessary.

## Acuteness is weaker than a uniform gap

Call a pair acute in the intersection sense when neither subspace contains a nonzero vector perpendicular to the other. More precisely, U intersect V perpendicular is zero, and U perpendicular intersect V is zero.

For finite-dimensional pairs, this rules out right-angle principal vectors and gives a positive smallest cosine. In an infinite-dimensional Hilbert space, every individual principal angle may be strictly less than ninety degrees while a sequence approaches ninety degrees. The cosine then has no kernel, yet its inverse is unbounded.

We must not confuse these two hypotheses. A projection gap strictly below one implies the intersection-based condition. The converse can fail in infinite dimensions.

Now return to K. Its kernel consists exactly of the two crossed intersections we just named. If both vanish, K is injective. The same is true of K adjoint. For a bounded operator, injectivity of its adjoint means its range is dense. Thus K has zero kernel and dense range, although it need not have a bounded inverse.

The polar decomposition K equals W C now has an isometric polar factor W. Because K has dense range, that isometry has dense and closed range, hence it is onto. So W is unitary.

This proves existence for the weaker, intersection-based acute condition. We obtained the rotation without ever dividing by a possibly vanishing lower bound for cosine.

## How do we recognize the correct unitary?

Suppose T is any unitary that intertwines P and Q. The intertwining identity says T P equals Q T. Consequently T carries U onto V and also carries U perpendicular onto V perpendicular.

That alone allows too much freedom. We need a test involving the directions in which T moves the source decomposition.

Compress T back to U: project onto U, apply T, and project onto U again. Do the analogous operation on U perpendicular. These are called the two diagonal compressions of T.

For the canonical polar factor W, both diagonal compressions are positive operators. Positive means self-adjoint and having nonnegative quadratic form. The self-adjoint requirement is important, especially over real Hilbert spaces: a quadratic form alone may fail to detect an antisymmetric part.

On a principal plane, both compressed blocks are multiplication by cosine theta. They are positive precisely because we use the shorter turn.

There is also a relation between the crossed blocks: one is the negative adjoint of the other, after taking the appropriate source and target directions. This expresses the geometry of a rotation rather than an arbitrary unitary rearrangement.

## Prove uniqueness instead of guessing it

Let T be a unitary intertwiner whose two diagonal compressions are positive. We want to show T equals W when the crossed defects vanish.

Define B to be the sum of those two diagonal compressions. Since each is positive, B is positive. And since both are supported in orthogonal pieces, B is block diagonal relative to U and U perpendicular.

The projection intertwining identity lets us rewrite our original operator K as T times B. To see the structure, recall that Q equals T P T adjoint. Substitute that identity into both terms defining K. The two terms become T times the two diagonal blocks of T adjoint. But each diagonal block is self-adjoint by positivity, so we may replace T adjoint by T inside those compressions. Their sum is exactly B.

Therefore K equals T B.

Take the adjoint and multiply: K adjoint K equals B squared, because T adjoint T is the identity. Since B is positive, it must be the unique positive square root of K adjoint K. Thus B equals C, the modulus of K.

We have proved that T C equals K. In the acute case the kernel of C is zero. The uniqueness property of polar decomposition now forces T to be W.

Notice what we used. The uniqueness argument did not require a numerical gap below one. It required the absence of crossed defects, together with the positive diagonal blocks.

## A square made from two reflections

Every orthogonal projection determines a reflection. Reflect through U by leaving U fixed and reversing U perpendicular. As an operator, this is twice P minus the identity. Define the corresponding reflection through V using Q.

On our principal plane, reflecting through U and then reflecting through V is a rotation through twice theta. This is a familiar geometry theorem, and we can now understand it operatorially.

Let J U be reflection through U and J V reflection through V. Their product, in that order, is the unitary operator J V after J U.

The canonical direct rotation W is the half-angle motion, so on every principal plane W squared equals J V times J U. The identity is also compatible with the common and exterior pieces: both reflections agree there, and their product is the identity. The canonical rotation acts as the identity on those pieces.

For a uniformly acute complex Hilbert-space pair, this also gives a functional-calculus construction. The spectrum of the reflection product avoids negative one, so we can select the principal square-root branch continuously. Applying that branch to the reflection product gives W.

Why mention negative one? At a right angle, the reflection product is minus the identity on the corresponding two-dimensional block. The number minus one has two opposite square roots, and no continuous principal choice across the branch cut. In the nonacute case, additional choices are needed to match the crossed defect spaces; the half-angle branch alone no longer determines the transport.

## Reversing the direction

A good transport construction should behave predictably when we interchange the source and target. Rotate from U to V, then rotate back from V to U. Those two motions ought to undo each other.

Indeed, swapping P and Q replaces K by K adjoint. The positive polar factors are consequently adjoints of one another. So the canonical direct rotation from V to U is W adjoint, which equals W inverse because W is unitary.

The same observation explains why the squared reflection product reverses. Its adjoint is J U followed by J V, precisely the reflection product for the reversed pair.

We have therefore obtained more than a means of moving a subspace: we have a transport specified by the pair, positive on the diagonal, compatible with reversal, and geometrically a half-angle of two reflections.

## Reconstruction

There are four things to prove for yourself.

First, calculate the polar modulus of K and show it is the positive cosine operator.

Second, explain why vanishing crossed defects makes the polar factor unitary even when cosine has no bounded inverse.

Third, prove uniqueness: an intertwining unitary with positive diagonal blocks factors K as that unitary times a positive block-diagonal operator. Identify the latter with the modulus of K.

Fourth, verify on an actual plane that two reflections give twice the angle, and explain why the principal half-angle branch fails at minus one.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(P=P_U\), \(Q=P_V\) and \(J_U=2P-I\), \(J_V=2Q-I\). Define
\[
K=QP+(I-Q)(I-P),\qquad C=|K|=\bigl(I-(P-Q)^2\bigr)^{1/2}.
\]
The **intersection-based acute hypothesis** is
\[
U\cap V^\perp=\{0\},\qquad U^\perp\cap V=\{0\}.
\]
It makes \(K\) and \(K^*\) injective. The polar factor \(W\) of \(K\) is then unitary, satisfies \(WP=QW\), and has positive diagonal compressions \(PWP\) and \((I-P)W(I-P)\). Conversely, any unitary \(T\) with these properties obeys
\[
K=T\bigl(PTP+(I-P)T(I-P)\bigr),
\]
where the factor in parentheses is positive and equals \(|K|\). Uniqueness of the polar factor gives \(T=W\).

For the stronger \(\|P-Q\|<1\), the modulus is invertible and \(W=KC^{-1}\). In the complex case, the reflection product has spectrum disjoint from \(-1\) and
\[
W=\operatorname{principal\,sqrt}(J_VJ_U),\qquad W^2=J_VJ_U,
\qquad W(V,U)=W(U,V)^*.
\]

**Lean bridge (source excerpts).** `DavisKahan/Geometry/Polar/DirectRotationAcute.lean` proves existence and uniqueness at the weaker, intersection-based hypothesis:

```lean
theorem existsUnique_spectraCanonicalPolarFactor
    (hUV : U ⊓ Vᗮ = ⊥) (hVU : Uᗮ ⊓ V = ⊥) :
    ∃! W : H →L[𝕜] H,
      W ∈ unitary (H →L[𝕜] H) ∧
        W * U.starProjection = V.starProjection * W ∧
        (U.starProjection * W * U.starProjection).IsPositive ∧
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive := by
```

The two submodule intersections encode the crossed defects; `IsPositive` includes self-adjointness, not only nonnegative real inner products. `H →L[𝕜] H` is the bounded operator algebra. The theorem's source uses `ker_spectraCanonicalIntertwiner_eq_bot` and the polar factor's properties to obtain the witness and uniqueness.

`DavisKahan/Geometry/Polar/DirectRotationSquare.lean` supplies the principal half-phase comparison, square identity, and reversal, with the *stronger* `IsUniformlyAcute` hypothesis:

```lean
theorem spectraDirectRotation_sq
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation U V hacute * spectraDirectRotation U V hacute =
      V.reflectionOperator * U.reflectionOperator := by
```

```lean
theorem spectraDirectRotation_reversal
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation V U hacute.symm =
      star (spectraDirectRotation U V hacute) := by
```

These declarations involve complex Hilbert spaces and the principal continuous-functional-calculus branch. The broader acute polar factor is handled separately and should not be conflated with a formula requiring a bounded inverse of cosine.

**Reconstruction exercise:** prove \(K=TB\) and \(B=|K|\) for an arbitrary qualifying \(T\); then compute \(J_VJ_U\) for two lines of angle \(\theta\) and locate the first obstruction to a continuous half-angle branch.
