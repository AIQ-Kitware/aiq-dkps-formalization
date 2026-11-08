# 046000 — Positive cosine and sine operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `034000` positive square roots; `035000` modulus; `042000` principal angles; `043000` cross projections; `044000` cosine–sine decomposition; `045000` Halmos decomposition. **Next:** acute pairs and transversality.

<!-- BEGIN SPOKEN LECTURE -->

# Can an operator have a cosine?

Think back to two lines meeting at an angle. The cosine tells us how much of a unit vector along one line survives when we project it onto the other. The sine tells us how much is lost into the perpendicular direction.

A finite-dimensional pair of subspaces can have several principal angles, one for each independent principal plane. But a list of angles requires choosing principal vectors, and in infinite dimensions there may be no complete list of them. Can we encode the same geometry without first choosing any vectors at all?

Yes. We can build positive operators that behave like cosine and sine, directly from the two orthogonal projections. Today we will construct those operators, prove their central identity, and see why they are the right language on acute pairs and direct rotations.

## Start with a single tilted line

Take the ordinary plane. Call its horizontal axis U. Call the line tilted counterclockwise by angle theta V. We assume theta lies between zero and ninety degrees.

Project a horizontal unit vector onto V. Its projection has length cosine theta. The part perpendicular to V has length sine theta. Squaring the two lengths and adding them gives one, by the Pythagorean theorem.

Now remember the two projection matrices from our cosine–sine decomposition. Projection onto U keeps the horizontal coordinate and discards the vertical one. Projection onto V has cosine squared in the upper left, sine squared in the lower right, and cosine times sine in the two off-diagonal positions.

Here comes a calculation worth remembering. Subtract the two projection matrices, and then square that difference. The off-diagonal terms cancel. Both diagonal entries become sine squared theta. So the square of the difference is simply sine squared theta times the identity matrix.

That is striking: a matrix built from two projections remembers the angle between their ranges, and it does so without asking us to name any principal vector.

## From a squared difference to the sine operator

Return to a Hilbert space. Let P be the orthogonal projection onto U and Q the orthogonal projection onto V. We will assume the subspaces are closed, so their orthogonal projections exist.

Call their difference D: P minus Q. Because each projection is self-adjoint, D is self-adjoint as well. Its square is therefore positive: taking the inner product of D squared x with x gives the squared norm of D x.

We also need an upper bound. For two orthogonal projections, the norm of their difference is at most one. Here is a proof. Split x into its part in U and its part perpendicular to U. The vector D x is the sum of two perpendicular pieces: the part of P x lost outside V, and the negative of the part of the U-perpendicular component that enters V. Each piece has length at most the length of the component it came from. The squared lengths therefore add to at most the squared length of x. Consequently D squared lies between zero and the identity in quadratic-form order.

From the positive square-root theorem, D squared has a unique positive square root. We call it the modulus of D, or the ambient sine operator. On our tilted plane, it is just sine theta times the identity.

Why the word ambient? Because this operator acts on the whole Hilbert space. Later we will also study a directed sine operator that acts, in effect, on the source subspace's coordinates. The two are related, but their domains and multiplicities need not match. We should not silently identify them.

## Construct the cosine from what remains

The sine operator squared is D squared. If sine squared plus cosine squared is to equal the identity, the natural cosine squared is the identity minus D squared.

This operator is positive, since D squared is at most the identity. Take its unique positive square root. Call that the ambient cosine operator.

We have now constructed both pieces without choosing a basis. The sine is the positive square root of D squared. The cosine is the positive square root of the identity minus D squared.

Their squares add to the identity by construction. Both are positive. And they commute, because both are obtained by applying functions to the same self-adjoint operator D squared.

In the tilted-plane example, cosine is cosine theta times the identity, and sine is sine theta times the identity. Across several independent principal planes, each operator has one scalar cosine or sine for each plane, repeated on the two directions of that plane.

This is the operator version of the Pythagorean identity. It does not depend on dimensions being finite.

## Why the operators respect both subspaces

There is a second identity hiding in the projection algebra. Expand D squared. It equals P plus Q minus P Q minus Q P.

Multiply that expression by P on the left. Then multiply it by P on the right. The results are the same, because P squared equals P. The same argument works with Q.

So D squared commutes with P and Q. Functions of D squared, including its positive square roots, also commute with both projections.

This has a geometric consequence: sine and cosine preserve U and its orthogonal complement, and they also preserve V and its orthogonal complement. Each can be studied in smaller blocks, even when P and Q themselves fail to commute.

Do not conclude that P and Q commute merely because both commute with the sine operator. Our tilted-plane example is already a counterexample: the projections generally do not commute, even though the sine is a scalar multiple of the identity on that plane.

## A second cosine, seen from U

Let us now look only at vectors inside U. Take a vector x in U and project it onto V. Its squared projected length is the inner product of Q x with x.

Because P x equals x, this is also the quadratic form of P Q P restricted to U. Thus P Q P on U records the squares of the projection lengths. In a principal direction making angle theta with V, it acts by cosine squared theta.

Taking its positive square root on U produces a positive cosine operator intrinsic to U. The corresponding sine comes from the positive square root of P times the identity minus Q times P, restricted to U.

These source-side operators are useful because their singular values are indexed by directions in U. They do not automatically have the same shape as the ambient operators. For example, if U is a line and V is a different line in the plane, the source cosine acts on a one-dimensional space, while the ambient cosine acts on two dimensions.

Still, they measure the same geometric angle. The coordinate representation has changed; the geometry has not.

## Zero and right angles without guessing

The Halmos decomposition tells us exactly what the endpoint angles do.

On a direction common to U and V, P and Q agree, so D is zero. The sine operator is zero, and the cosine is the identity. That is angle zero.

On a direction belonging to U but perpendicular to V, P acts as one and Q as zero. There D has magnitude one. The sine operator acts as one and cosine as zero. That is a right angle. The same happens for a target-only defect direction.

On a direction perpendicular to both subspaces, P and Q again agree, so the ambient sine is zero and cosine is one. This is another reason to distinguish ambient and directed angle operators: the exterior directions appear in the ambient space, even though they are not directions in either subspace.

On the remaining generic part, the operators encode intermediate angles. In a finite-dimensional generic part, we can diagonalize them simultaneously and recover the individual principal planes. In an infinite-dimensional generic part, a continuous range of spectral values may replace a finite angle list.

## The actual angle operator

We can go one step further. Since the positive sine operator has spectral values between zero and one, we may apply the arcsine function by functional calculus.

The result is a self-adjoint angle operator whose spectrum lies between zero and a right angle. Applying sine to it recovers the sine operator. Applying cosine produces the positive cosine operator.

So we have an exact operator analogue of saying theta is an angle, rather than merely a number whose sine we happen to know.

The construction is especially valuable when there is no complete basis of principal-angle eigenvectors. Functional calculus still makes sense of sine, cosine, and arcsine on the operator as a whole.

## Reconstruction

There are three calculations worth doing before moving on.

First, write the two projection matrices for lines meeting at angle theta. Subtract them and square the result. Check that sine squared theta appears on both diagonal entries.

Second, use only P squared equals P and Q squared equals Q to show that the square of P minus Q commutes with P and Q. Notice that the statement does not require P and Q to commute.

Third, identify the sine and cosine actions on each of the four elementary Halmos pieces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(P=P_U\), \(Q=P_V\), and \(D=P-Q\). Define the **ambient** operators
\[
S=|D|=(D^2)^{1/2},\qquad C=(I-D^2)^{1/2}.
\]
For orthogonal projections, \(0\le D^2\le I\), hence \(S,C\ge0\), \(S^2+C^2=I\), and \(SC=CS\). Both commute with \(P,Q\), since \(D^2=P+Q-PQ-QP\) commutes with each. The angle operator is \(\Theta=\arcsin(S)\), with \(0\le\Theta\le\pi/2\) in the spectral sense.

For \(x\in U\), \(\langle PQP x,x\rangle=\|Qx\|^2\), and \(\langle P(I-Q)P x,x\rangle=\|(I-Q)x\|^2\). Their positive square roots define the **source-side** cosine and sine. Ambient and directed operators have different natural multiplicities and need not be interchangeable as operators.

**Lean bridge.** In `DavisKahan/Geometry/Angle/OperatorAngleGeneric.lean`, the scalar-generic literal angle is defined by

```lean
@[expose]
def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  cfc Real.arcsin ((Submodule.sinAngleOperator U V))
```

The theorem `cfc_sin_angleOperator` establishes the sine recovery. The directed operators in the same module record the distinct cross-projection construction:

```lean
@[expose]
def directedSinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (Vᗮ.starProjection ∘L U.starProjection)
```

```lean
@[expose]
def directedCosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (V.starProjection ∘L U.starProjection)
```

`DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean` contains `sinAngleOperatorC_sq_add_cosAngleOperatorC_sq`, as well as the complex-field commutation theorems for the angle and projections. `DavisKahan/Geometry/Angle/CosineKernel.lean` contains `section3CosAngleOperator_sq_add_sinAngleOperator_sq` for the paper's principal cosine.

Here `E →L[𝕜] E` is the type of bounded linear operators; `cfc` is continuous functional calculus; `ContinuousLinearMap.modulus` is the operator modulus; `U.starProjection` is the orthogonal projection onto `U`.

**Reconstruction exercise:** prove \(PD^2=D^2P\), compute the source and ambient sines for distinct lines in \(\mathbb R^2\), and explain why their scalar angles agree despite different operator domains.
