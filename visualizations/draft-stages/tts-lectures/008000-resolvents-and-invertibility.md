# Resolvents and invertibility

<!-- BEGIN SPOKEN LECTURE -->

# Resolvents and invertibility

Suppose a linear transformation takes a vector and produces an output. If we know the output, can we recover the input?

For an invertible matrix, the answer is easy: apply its inverse. But if the matrix sends some nonzero vector to zero, information has been lost. No inverse can undo that transformation for every output.

There is a useful way to investigate this failure. Choose a number, subtract that number times the identity from the operator, and try to invert the result. By changing the number, we discover where inversion works and where it breaks down. The inverses that do exist are called resolvents.

The aim of this lecture is to understand that construction first with a tiny matrix, then with an infinite-dimensional operator, and finally to see two important facts about the resulting family: resolvents persist under small changes of the shift, and their size tells us something about the stability of inversion.

## A matrix we can invert by hand

Consider a matrix A that doubles the first coordinate of a vector and multiplies the second coordinate by five. In standard coordinates it is diagonal, with entries two and five.

Pick the number three. Subtract three times the identity from A. The new matrix multiplies the first coordinate by negative one and the second coordinate by two. We can invert it: divide the first output coordinate by negative one, and the second by two.

So the inverse of A minus three times the identity multiplies the first coordinate by negative one and the second by one half.

Now change the shift from three to two. The first multiplier becomes zero. Every vector pointing along the first coordinate axis is sent to zero, so the shifted matrix cannot be inverted.

A shift of five causes the same problem along the second axis.

These numbers are familiar. Two and five are the eigenvalues of A. When we subtract an eigenvalue, the corresponding eigenvector goes into the kernel of the shifted operator.

We have already found two sets of numbers. There are shifts where the inverse exists, such as three. And there are shifts where the inverse fails, such as two and five.

In finite-dimensional complex linear algebra, the second set consists exactly of the eigenvalues. In infinite dimensions, the second set can be larger. That is why we give it its own name: the spectrum.

## Name the construction

For the moment, take A to be a bounded linear operator on a complex Banach space. A Banach space is a normed vector space in which Cauchy sequences converge; it gives us a setting where continuity of the inverse makes sense.

A number z belongs to the resolvent set of A when A minus z times the identity has a bounded inverse defined on the whole space. We call that inverse the resolvent of A at z.

The spectrum is the collection of shifts where that bounded, everywhere-defined inverse does not exist.

There are several ways inversion can fail. Two different inputs might produce the same output. Some outputs might not be produced at all. Or, in infinite dimensions, recovering an input might require arbitrarily large amplification of small changes in the output.

For bounded operators on Banach spaces, a bijective shift automatically has a bounded inverse, by the bounded inverse theorem. Still, boundedness belongs in the definition because it expresses the stability we want.

One convention writes the resolvent as the inverse of A minus z times the identity. That is the convention used throughout this recording. The inverse of z times the identity minus A is also frequently called the resolvent; the two operators differ by a minus sign. The spectrum is the same under either convention.

## What happens as we approach an eigenvalue?

Return to our diagonal matrix with eigenvalues two and five. If we choose a shift of two point one, the first entry of the shifted matrix is negative zero point one. Its inverse multiplies the first coordinate by negative ten.

A shift of two point zero one produces a factor of negative one hundred. A shift of two point zero zero one produces negative one thousand.

The inverse exists at each of those shifts. But it takes a tiny change in an output coordinate and turns it into a much larger change in the recovered input.

This is why the size of the resolvent is informative. In our diagonal example, the operator norm is the larger of the absolute values of its two inverse diagonal entries. The largest entry comes from whichever eigenvalue is nearest the shift.

For a self-adjoint operator, this becomes an exact statement: the resolvent norm is one divided by the distance from the shift to the spectrum. A self-adjoint operator is an operator equal to its adjoint; real symmetric matrices are the familiar finite-dimensional examples. The sharp distance formula belongs to self-adjoint, and more generally normal, operators. For an arbitrary operator, the inverse can be very large even when the shift is relatively far from the spectrum.

For now, the central observation is that failure of invertibility has a neighborhood. Inverses get harder to control as we move toward certain spectral values.

## Spectrum without an eigenvector

The matrix example might suggest that every point of the spectrum must have an eigenvector. Let's test that idea on an operator whose inputs are functions.

Consider all continuous complex-valued functions on the interval from zero to one. Measure the size of a function by its largest absolute value. This is a Banach space.

Define an operator M that multiplies a function by its input coordinate. At a number t between zero and one, the output is t times the original function's value at t.

The operator is bounded. Multiplication by a number between zero and one never increases the maximum absolute value.

Can zero be an eigenvalue? That would require a nonzero continuous function f for which t times f of t equals zero at every point. For every positive t, the equation forces f of t to be zero. Continuity then forces its value at zero to vanish as well. So there is no nonzero eigenvector with eigenvalue zero.

Yet M has no inverse on the whole function space. Think of trying to produce the constant function one. At t equal to zero, the output of M is always zero, no matter what input function we choose. The constant function one can never be an output.

Therefore zero is in the spectrum, even though zero is not an eigenvalue.

There is also a stability problem. Imagine a tall triangular function, one at t equal to zero, dropping steadily to zero at t equal to one over n, and vanishing beyond that point. Its maximum size is one. After multiplication by t, its maximum size is no greater than one over n.

As n grows, the output gets arbitrarily small while the input remains size one. Any attempt to invert M would have to turn these tiny outputs back into unit-sized inputs. No bounded inverse can do that.

This is the reason the spectrum is defined through bounded inversion rather than only through exact eigenvectors. In infinite-dimensional spaces, approximate eigenvectors and failures of surjectivity can reveal spectral points that ordinary eigenvectors miss.

## Why resolvents survive small changes

Now suppose z is a shift where the resolvent exists. Could an arbitrarily tiny change of z immediately destroy invertibility?

The answer is no. To see why, call the inverse at z simply R. If we replace z by a nearby number w, the new shifted operator is the old one minus w minus z times the identity.

We can factor it into the old shifted operator, which is invertible, and a correction of the form identity minus w minus z times R.

Here we use a familiar fact about geometric series. If a bounded operator T has norm less than one, then identity minus T is invertible. Its inverse is the sum of the identity, T, T squared, T cubed, and so on. This is the Neumann series, the operator version of a convergent geometric series.

For our correction, the norm is at most the distance between w and z, multiplied by the norm of R. If that product is less than one, the Neumann series supplies an inverse.

So every resolvent point has a whole disk of nearby resolvent points around it. The resolvent set is open, and the spectrum is closed.

Notice the quantitative detail. A large resolvent norm makes the guaranteed safe disk smaller. That matches what we observed in the diagonal example as the shift approached two.

## Two other useful consequences

There is a compact algebraic relation between resolvents at two shifts. If z and w are both resolvent points, the resolvent at z minus the resolvent at w equals z minus w, multiplied by the resolvent at z and then the resolvent at w.

We can check the sign with ordinary fractions. One divided by a minus z, minus one divided by a minus w, has numerator z minus w. The operator version follows by multiplying out the inverse equations.

This is called the resolvent identity. It lets us compare how the inverse changes as the shift moves.

One more consequence comes from looking very far away. Suppose A is bounded and we choose z whose absolute value exceeds the operator norm of A. Factor A minus z times the identity into two pieces. The first is the scalar negative z. The second is the operator identity minus A divided by z. The norm of A divided by z is less than one, so another Neumann series gives an inverse.

Therefore the spectrum of a bounded operator must lie inside the closed disk whose radius is the operator norm of A. We have obtained a spectral bound without computing an eigenvalue.

## What the family of inverses tells us

There is one question worth holding onto: when can we solve the shifted equation stably?

A resolvent is the operator that solves it. The spectrum records the shifts where such a bounded inverse cannot be formed. An eigenvector gives one reason for failure, but the continuous-function example showed another. And the Neumann-series argument showed that resolvent points occur in open regions, not as isolated accidents.

Try reconstructing two calculations. For our diagonal matrix, why does the resolvent at three have entries negative one and one half? And for multiplication by t on continuous functions, why does zero belong to the spectrum even though it is not an eigenvalue?

Those two examples capture the essential distinction between eigenvalues and spectrum, and why a family of shifted inverses is a productive way to study an operator.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For a complex Banach space \(E\) and bounded \(A\in\mathcal B(E)\), use the narration convention
\[
R_A(z)=(A-zI)^{-1},\quad
\rho(A)=\{z\in\mathbb C:A-zI\text{ has a bounded inverse}\},\quad
\sigma(A)=\mathbb C\setminus\rho(A).
\]
For \(z,w\in\rho(A)\),
\[
R_A(z)-R_A(w)=(z-w)R_A(z)R_A(w).
\]
If \(|z|>\|A\|\), then \(z\in\rho(A)\), by the Neumann series. In the continuous-function example \((Mf)(t)=t f(t)\) on \(C([0,1],\mathbb C)\), the value zero lies in \(\sigma(M)\) but is not an eigenvalue.

**Lean bridge.** `DavisKahan/SpectralTheory/ResolventOperator.lean` contains source-defined resolvent predicates and a resolvent identity. **Its resolvent sign convention agrees with the spoken lecture**: `resolventOperator A z` is \((A-zI)^{-1}=R_A(z)\), and its exact declaration is:

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

The excerpted theorem header is followed by its proof in the source; the trailing `:= by` here marks an excerpt, not an independently compilable declaration. The displayed resolvent identity uses exactly the sign determined by the \(A-zI\) convention. `∘L` is bounded-operator composition; a two-sided inverse is explicitly part of `InResolventSet`.

**Source and provenance.** Both declarations were found in the supplied DKPS snapshot. The file develops paper-related bounded-operator resolvent infrastructure using the real-or-complex `RCLike` interface and records additional planned contour work. The general spectrum and Banach-algebra mechanisms are not claimed to originate in this file. No new Lean code was compiled.
