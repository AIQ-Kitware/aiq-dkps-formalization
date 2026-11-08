# Resolvents and invertibility

<!-- BEGIN SPOKEN LECTURE -->

Consider the quarter-turn operator on the real plane, sending x comma y to negative y comma x. No nonzero real vector is an eigenvector, since the operator rotates every direction by ninety degrees. Over the complex numbers it has eigenvalues i and negative i. Those are exactly the scalar values for which the shifted operator A minus lambda times the identity fails to be invertible.

Today we will turn that second question into a definition. This is the beginning of spectral theory in its general form. Our goal is to understand what a spectrum is, why it is more than a list of eigenvalues, and why an inverse called the resolvent tells us so much about an operator.

We can do most of this using only what we already know: Banach spaces, bounded operators, inverse maps, and geometric series.

## Start with a diagonal matrix

Take a map on the ordinary two-dimensional complex vector space. It doubles the first coordinate and multiplies the second by five. If we write it as a diagonal matrix, its diagonal entries are two and five.

Now choose a complex number z. Form the operator z times the identity minus A. On the first coordinate it multiplies by z minus two. On the second it multiplies by z minus five.

When can we undo this operation? Exactly when neither multiplier is zero. In that case the inverse simply divides the first coordinate by z minus two, and divides the second by z minus five.

At z equal to two, this inverse fails because the first coordinate gets collapsed to zero. At z equal to five, the second coordinate gets collapsed. These are precisely the eigenvalues of A.

So for this example, the values where z times the identity minus A fails to have an inverse form the set containing two and five. That set is the spectrum of A.

Notice that we are describing the operator through a family of inverses. For each z outside the spectrum, there is an operator that undoes z times the identity minus A. We call that inverse the resolvent at z.

## The general definition

Let E be a complex Banach space, and let A be a bounded complex-linear operator from E to itself.

We say that z is in the resolvent set of A if z times the identity minus A has a two-sided inverse that is also bounded and linear. Two-sided means we can compose the two operators in either order and obtain the identity.

The spectrum is the set of complex numbers not in the resolvent set.

There are two requirements in that definition. The map must have a two-sided inverse, and that inverse must respect the norm through a boundedness estimate. In finite dimensions, linear inverses are automatically bounded. There is also a deep theorem, called the bounded inverse theorem, which says that a bijective bounded linear map between Banach spaces has a bounded inverse. We have not proved it yet, so today we keep boundedness visible in the definition. The distinction becomes even more important when we study operators defined only on part of a space.

The resolvent operator, when it exists, will be denoted by the letter R with the chosen scalar z as its input. More explicitly, R at z means the inverse of z times the identity minus A.

For a diagonal matrix, this is the diagonal inverse we just computed. But the definition works even when there is no preferred basis, and even when there is no matrix consisting of finitely many entries.

## Why an eigenvalue belongs to the spectrum

Suppose A has an eigenvector v with eigenvalue z. That means v is nonzero and A of v equals z times v.

Subtract. The operator z times the identity minus A sends v to zero. A map that sends a nonzero vector to zero cannot have an inverse: if it did, applying the inverse to both sides would imply that v equals zero.

Therefore every eigenvalue belongs to the spectrum.

This proves one direction. It does not prove that every spectral value is an eigenvalue. That reverse statement holds for matrices over the complex numbers, but it fails in general for infinite-dimensional operators.

Let's construct a counterexample without introducing Hilbert spaces yet.

## A spectral value with no eigenvector

Consider the Banach space of continuous complex-valued functions on the interval from zero to one. We measure a function by its maximum absolute value. This space is complete in the maximum norm: a uniformly Cauchy sequence of continuous functions converges uniformly, and a uniform limit of continuous functions is continuous.

Define the operator M by multiplying a function by its input coordinate. In other words, M of f is the function whose value at t is t times the value of f at t.

This operator is linear. It is bounded, because t always lies between zero and one. Multiplication by t cannot make the maximum absolute value larger. In fact, its operator norm is one: apply M to the constant function one, and the output reaches one at the right endpoint.

Now ask whether zero is an eigenvalue. An eigenvector at zero would be a continuous function f, not identically zero, such that t times f of t is zero for every t.

For every positive t, that condition forces f of t to be zero. Continuity then forces f at zero to be zero too. So the only function sent to zero is the zero function. Zero is not an eigenvalue.

But is M invertible? No. If there were a continuous function f satisfying M of f equals the constant function one, then at t equal to zero we would require zero times f of zero to equal one. That is impossible. M is not onto the entire function space.

Thus zero belongs to the spectrum even though it is not an eigenvalue. The failure is surjectivity, not the existence of a nonzero vector in the kernel.

There is an even more revealing way to see the difficulty. Choose a continuous triangular spike that has height one at zero and falls linearly to zero by t equal to one over n. Call this function f sub n. Its maximum norm is one. But multiplying it by t produces a function whose maximum norm is at most one over n.

So we have unit-sized inputs whose outputs become arbitrarily small. No bounded inverse could recover the input from such tiny outputs: a bounded inverse would have to amplify the output by a factor growing without bound.

This example gives us two independent reasons for concern: the operator is not onto, and the inverse estimate cannot hold. Later, in Hilbert spaces, we will classify several different ways a spectral value can fail to be a resolvent point.

## Why the resolvent set is open

A standard Neumann-series argument shows that an operator close enough to the identity has an inverse, supplied by a Neumann series. That fact makes the resolvent set robust.

Suppose z is a resolvent point and let R be the inverse of z times the identity minus A. Now move from z to a nearby complex number w.

The operator w times the identity minus A can be factored into the original invertible operator, multiplied by an identity plus a scalar multiple of R. The size of that correction is at most the distance from w to z, multiplied by the norm of R.

If that product is less than one, the correction has a Neumann-series inverse. The original operator is invertible, and so is the correction. Their product is therefore invertible.

This proves that every resolvent point has a small disk around it containing only resolvent points. The resolvent set is open. Its complement, the spectrum, is closed.

There is also a quantitative lesson. If the norm of the resolvent at z is very large, the argument only guarantees a small disk of safe nearby values. The resolvent norm is telling us how sensitive inversion is near z, even before we discuss perturbing the operator itself.

## A relation between two resolvents

There is a simple algebraic identity that will be useful repeatedly.

Suppose z and w are both resolvent points. Write R at z and R at w for their inverses. Subtract these two inverses.

We can insert their defining inverse equations and rearrange the result. For our convention, where R at z is the inverse of z times the identity minus A, the difference R at z minus R at w equals w minus z, multiplied by R at z followed by R at w.

Let's check the sign on an ordinary number. One over z minus a, minus one over w minus a, has numerator w minus z. That is exactly the sign we claimed.

The operator identity is a noncommutative version of that familiar fraction calculation. It also shows why the resolvent varies continuously with z throughout the resolvent set: nearby scalar values lead to nearby inverse operators, with a bound supplied by the product of their norms.

## Far from the operator

For one last application of the geometric series, take a complex number z whose absolute value is greater than the operator norm of A.

Factor z times the identity minus A as z times the identity multiplied by the identity minus A divided by z. The operator A divided by z has norm less than one. Therefore the second factor has an inverse given by a convergent geometric series.

So every z with absolute value greater than the norm of A is in the resolvent set. Equivalently, the spectrum lies inside the closed disk centered at zero with radius equal to the operator norm.

That does not tell us where the spectral values actually are. It gives a guaranteed region outside which they cannot be. This is our first general spectral bound, obtained entirely from Banach-space methods.

## Check your understanding

Here are three things to reconstruct.

First, for a diagonal operator with entries two and five, find the resolvent at z equal to three and explain why it does not exist at z equal to two.

Second, explain why multiplication by t on continuous functions has zero in its spectrum but no nonzero eigenvector with eigenvalue zero.

Third, derive the safe-disk condition around a resolvent point using the Neumann series. What role does the norm of the resolvent play?

We now have a definition of spectrum that survives beyond matrices. We also have a warning: spectral values need not be eigenvalues.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For a complex Banach space \(E\) and bounded \(A\in\mathcal B(E)\), use the narration convention
\[
R_A(z)=(zI-A)^{-1},\quad
\rho(A)=\{z\in\mathbb C:zI-A\text{ has a bounded inverse}\},\quad
\sigma(A)=\mathbb C\setminus\rho(A).
\]
For \(z,w\in\rho(A)\),
\[
R_A(z)-R_A(w)=(w-z)R_A(z)R_A(w).
\]
If \(|z|>\|A\|\), then \(z\in\rho(A)\), by the Neumann series. In the continuous-function example \((Mf)(t)=t f(t)\) on \(C([0,1],\mathbb C)\), the value zero lies in \(\sigma(M)\) but is not an eigenvalue.

**Lean bridge.** `DavisKahan/SpectralTheory/ResolventOperator.lean` contains source-defined resolvent predicates and a resolvent identity. **Its sign convention is the opposite of the spoken convention**: its `resolventOperator A z` is \((A-zI)^{-1}=-R_A(z)\), and its exact declaration is:

```lean
def InResolventSet (A : E →L[𝕜] E) (z : 𝕜) : Prop :=
  ∃ R : E →L[𝕜] E,
    R ∘L (A - z • ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E ∧
    (A - z • ContinuousLinearMap.id 𝕜 E) ∘L R = ContinuousLinearMap.id 𝕜 E
```

The file also contains:

```lean
theorem resolvent_identity
    (A : E →L[𝕜] E) {z w : 𝕜}
    (hz : InResolventSet A z) (hw : InResolventSet A w) :
    resolventOperator A z - resolventOperator A w =
      (z - w) • (resolventOperator A z ∘L resolventOperator A w) := by
```

The excerpted theorem header is followed by its proof in the source; the trailing `:= by` here marks an excerpt, not an independently compilable declaration. Since both resolvents gain a minus sign under the change of convention, the corresponding formulas agree. `∘L` is bounded-operator composition; a two-sided inverse is explicitly part of `InResolventSet`.

**Source and provenance.** Both declarations were found in the supplied DKPS snapshot. The file develops paper-related bounded-operator resolvent infrastructure using the real-or-complex `RCLike` interface and records additional planned contour work. The general spectrum and Banach-algebra mechanisms are not claimed to originate in this file. No new Lean code was compiled.
