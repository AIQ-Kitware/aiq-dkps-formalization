# 047000 — Acute pairs and transversality

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `011000` projection theorem; `035000` modulus; `037000` polar decomposition; `042000` principal angles; `045000` Halmos decomposition; `046000` positive cosine and sine operators. **Next:** the Sz.-Nagy–Kato intertwiner.

<!-- BEGIN SPOKEN LECTURE -->

# Almost perpendicular is not perpendicular

Suppose two lines are almost at a right angle. Their cosine is positive, but extremely small. A projection from one line onto the other loses almost all of a vector's length.

Now imagine not one angle, but infinitely many independent angles, each closer to a right angle than the last. None is exactly a right angle. Nonetheless, projection can lose arbitrarily large fractions of the length of vectors chosen from farther and farther along the sequence.

That example raises today's question: what should it mean for two subspaces to be acute? Does it mean that no direction is exactly perpendicular, or that every direction stays a definite distance away from perpendicular?

The answer matters for the existence of bounded inverses, graph representations, and canonical rotations. We will develop both meanings and refuse to confuse them.

## Three ways to express an angle condition

Start with two closed subspaces U and V of a Hilbert space, and let P and Q be their orthogonal projections.

In finite dimensions, a pair of equally dimensional subspaces has a finite collection of principal angles. If all those angles are strictly less than ninety degrees, then their largest angle is less than ninety degrees by some definite margin. The smallest principal cosine is positive.

In infinite dimensions, there need not be a largest angle. A sequence of angles can approach ninety degrees without ever reaching it. Thus the sentence, no direction makes an exact right angle, is weaker than the sentence, all angles stay uniformly below a right angle.

The first condition can be expressed using crossed intersections. No nonzero vector of U lies perpendicular to V, and no nonzero vector of V lies perpendicular to U. Those are the source and target defect spaces from Halmos's decomposition. If both are zero, the pair has no exact crossed defects.

The stronger condition uses a number. Let d be the norm of P minus Q. The pair is uniformly acute when d is strictly less than one.

In finite dimensions and for equally dimensional subspaces, d is the sine of the largest principal angle. In arbitrary dimensions it also detects unmatched right-angle directions. So the condition d less than one says that all the relevant angular deviations stay a definite distance away from ninety degrees.

## Why the uniform condition gives an inverse

We just constructed a positive ambient cosine operator whose square is identity minus the square of P minus Q.

Suppose d is less than one. For every vector x, the norm of the difference applied to x is at most d times the norm of x. Therefore the squared norm of the cosine applied to x is at least one minus d squared, times the squared norm of x.

That means the cosine cannot shrink a unit vector below the positive number square root of one minus d squared. In particular it has no kernel.

But a bounded lower estimate is stronger than merely having no kernel. Since the cosine is self-adjoint, its range is dense whenever its kernel is zero. The lower estimate also makes its range closed: if its outputs converge, the corresponding inputs form a Cauchy sequence. A range that is both dense and closed is the whole Hilbert space.

Thus the cosine has an everywhere-defined bounded inverse. Its inverse norm is at most one divided by the square root of one minus d squared.

Notice what we used. Positivity by itself was not enough. Kernel zero by itself was not enough. The positive lower bound was the decisive ingredient.

## Viewing V as a graph over U

Now for a more geometric consequence. If U and V are close enough, we ought to be able to describe V by starting with a point in U and adding a perpendicular correction.

A graph over U has precisely this form: take each u in U and attach an element L of u in U perpendicular. The resulting vectors, u plus L of u, make up a subspace of the ambient direct sum of U and its perpendicular complement.

We want to prove that the uniformly acute V really is such a graph, with L bounded.

First, take v in V. Since Q v equals v, the part of v perpendicular to U is exactly the difference between Q and P applied to v. Its norm is at most d times the norm of v.

By Pythagoras, the length of the U component of v is at least the square root of one minus d squared times the length of v.

So projecting V onto U cannot send a nonzero vector to zero. More than that, its inverse, if it covers U, will be bounded by the same lower estimate.

Why should it cover U? Look at the map that sends u in U first into V by Q, then back into U by P. This is the compressed operator P Q P on U. Its quadratic form on a vector u is the squared length of Q u. Applying the same gap argument, its value is bounded below by one minus d squared times the squared length of u.

A bounded, positive self-adjoint operator with such a lower bound is invertible on U, by the argument we just used for the cosine. Therefore every u in U can be written as P Q w for some w in U. The vector Q w belongs to V and projects back to u.

We have proved that projection from V to U is both injective and onto. Define the graph correction L by taking its inverse and then extracting the perpendicular component. Linearity and boundedness follow from the projection maps and the lower bound.

More quantitatively, the norm of L is at most d divided by the square root of one minus d squared. As d approaches one, that bound becomes arbitrarily large. A near-right-angle subspace may still be a graph, but the graph becomes steep.

## The two-line example again

Return to the plane, with U horizontal and V tilted through theta. A point on V can be written as a horizontal coordinate together with a vertical coordinate. The vertical coordinate equals tangent theta times the horizontal coordinate.

So the graph map is multiplication by tangent theta. This matches our bound exactly: sine theta divided by cosine theta equals tangent theta.

The sine controls how far a vector strays perpendicular to U. The cosine tells us how reliably we can recover its U coordinate. The tangent measures the correction relative to that coordinate.

This is why tangent bounds arise naturally in perturbation theory. They are estimates on graph slopes, not merely alternate ways of writing sine bounds.

## A counterexample in an infinite Hilbert space

We now build the promised distinction. Take countably many mutually orthogonal two-dimensional planes. In the nth plane choose a horizontal unit vector e number n and a vertical unit vector f number n.

Let U be the closed subspace generated by all the horizontal vectors. Let V be the closed subspace generated by one tilted unit vector in each plane.

Choose its horizontal component to have length one divided by n plus one. Its vertical component is the positive square root of one minus that number squared.

Every horizontal component is positive. Thus no nonzero vector of V is perpendicular to U. Likewise no nonzero vector of U is perpendicular to V. There are no crossed defect vectors.

But those horizontal components approach zero. The corresponding angles approach ninety degrees, and the sines approach one. Hence the norm of P minus Q is one: the pair is not uniformly acute.

If we tried to write V as the graph of a bounded operator from U into U perpendicular, its action on e number n would have slope equal to the ratio of the vertical component to the horizontal component. That ratio grows without bound.

No bounded graph map can represent this V over all of U. The obstruction is not an actual perpendicular vector. It is a sequence of increasingly perpendicular directions.

The exact-crossed-defect criterion and the uniform-gap criterion are therefore different in infinite dimensions.

## Why this matters for rotations

Suppose we want a unitary map that carries U onto V. An arbitrary unitary transporter might rotate unrelated directions unnecessarily. The direct rotation is a special choice tied to the relative geometry of the two projections.

In the uniformly acute case, the positive cosine is invertible, and that will make an explicit algebraic construction possible. But we should not treat uniform acuteness as the only setting where a canonical polar factor can exist. The weaker, no-crossed-defect case deserves separate analysis, and right-angle defects require yet another discussion.

Those are the subjects.

## Reconstruction

First, prove that norm of P minus Q less than one forces both crossed intersections to vanish.

Second, show why an operator bounded below by a positive constant has closed range, and why a self-adjoint operator with zero kernel has dense range.

Third, reconstruct the graph argument: find the compression P Q P, prove it invertible on U, and use it to recover one vector of V for every coordinate in U.

Finally, explain why the infinite sequence of angles approaching ninety degrees defeats a bounded graph representation without creating a single exact right-angle vector.

The distinction is between having no direction with complete information loss and having a uniform positive lower bound on the cosine operator. Only the latter guarantees a bounded inverse on the relevant range.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For closed \(U,V\subseteq H\), put \(P=P_U\), \(Q=P_V\), and \(d=\|P-Q\|\). **Uniform acuteness** is \(d<1\). It implies \(U\cap V^\perp=\{0\}=U^\perp\cap V\). The converse fails in infinite dimensions.

With \(C=(I-(P-Q)^2)^{1/2}\), one has \(C^2\ge(1-d^2)I\), hence \(C^{-1}\) exists boundedly and \(\|C^{-1}\|\le(1-d^2)^{-1/2}\).

The restricted map \(P|_V:V\to U\) is bijective when \(d<1\). Its inverse followed by \((I-P)\) gives \(L:U\to U^\perp\) with
\[
V=\{u+Lu:u\in U\},\qquad \|L\|\le \frac{d}{\sqrt{1-d^2}}.
\]
The construction uses \(PQP|_U\ge(1-d^2)I\).

**Lean bridge.** `DavisKahan/Geometry/Angle/AcuteCosine.lean` proves the crucial infinite-dimensional inverse statement:

```lean
theorem isUnit_section3CosAngleOperator_of_isUniformlyAcute
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute K L) : IsUnit (section3CosAngleOperator K L) := by
  rw [section3CosAngleOperator_eq_canonicalAbsoluteValue]
  exact isUnit_spectraCanonicalAbsoluteValue K L hacute
```

And the resulting injectivity:

```lean
theorem section3CosAngleOperator_injective_of_isUniformlyAcute
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute K L) : Function.Injective (section3CosAngleOperator K L) :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp
    (isUnit_section3CosAngleOperator_of_isUniformlyAcute K L hacute)).injective
```

The `IsUniformlyAcute` hypothesis is the projection-gap condition. `IsUnit` expresses invertibility in the bounded operator algebra; the proof connects the principal cosine with the modulus of the canonical intertwiner developed in `DavisKahan/Geometry/Polar/DirectRotation.lean`.

For the weaker condition, `DavisKahan/Geometry/Halmos/GenericPosition.lean` establishes trivial intersections on the generic part without asserting a uniform spectral bound. These two conditions must not be collapsed in the mathematical course or the Lean bridge.

**Reconstruction exercise:** verify the graph bound and build the direct-sum sequence example with \(\cos\theta_n=1/(n+1)\). Show that its crossed defects vanish while \(\|P-Q\|=1\).
