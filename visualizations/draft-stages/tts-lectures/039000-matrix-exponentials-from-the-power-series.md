# 039000 — Matrix exponentials from the power series

**Draft status:** audio-first mathematical lecture. **Prerequisites:** power series and elementary calculus, bounded operators, matrix multiplication, adjoints, skew-adjoint operators. **Next:** continuous orthogonal/unitary motions and direct rotations.

<!-- BEGIN SPOKEN LECTURE -->

# What does it mean to rotate continuously?

Until now our operators have usually described a transformation in one step. A matrix acts on a vector, and we compare the input with the output.

But suppose we want to describe a transformation that unfolds over time. Start at the identity, move a tiny amount, then move again, and keep doing so. We want a family of operators for which the transformation over two successive time intervals agrees with the transformation over their combined duration.

For ordinary numbers, the exponential function has exactly that property. It converts addition into multiplication. Today we will build its matrix analogue from the same power series and see what survives—and what changes—when multiplication no longer commutes.

## Start with a scalar differential equation

Consider the simplest possible growth rule. A quantity changes at a rate proportional to its present value. The solution is an exponential. If the growth rate is a constant number a, and the initial quantity is one, the result at time t is the exponential of a times t.

Why? The derivative is a times the function, and at time zero the value is one.

Now replace the number a with a square matrix B. Ask for a time-dependent vector whose derivative is B applied to the current vector. We expect the same idea to work, but now multiplication is matrix multiplication.

The expression we want is the exponential of t B. We will not define it entry by entry. We will build a new matrix out of powers of the entire matrix.

## Construct the exponential

Recall the scalar power series for the exponential: one plus the argument, plus its square divided by two factorial, plus its cube divided by three factorial, and so on.

For a square matrix B, use the same pattern. The constant term is the identity matrix. The first-order term is B. The second-order term is B squared divided by two factorial. The next is B cubed divided by three factorial.

Multiply B by the time t before putting it into the series. That is the definition of the matrix exponential at time t.

Why does this infinite sum converge? Choose the operator norm. The norm of B to the power n is at most the norm of B raised to the power n. This follows by repeatedly applying the bound for a product of operators.

Consequently, the norm of the n-th matrix-series term is bounded above by the corresponding term of the ordinary numerical exponential series, with absolute t times the operator norm of B as its argument.

That scalar series converges. So the matrix series converges absolutely in operator norm. In finite dimensions the space of matrices is complete, giving a well-defined limit.

The factorials make the large powers manageable. Without them, the sum might fail to converge.

## A matrix whose square is zero

Let N be the two-by-two matrix with a one above the diagonal and zeros elsewhere. It sends the vector with coordinates x and y to y and zero.

Apply it twice. The first application puts everything on the horizontal axis. The second application kills that axis. So N squared is zero.

That makes its exponential easy. Every term beyond the linear term vanishes. The exponential of t N is simply the identity plus t N.

Acting on x and y, it produces x plus t y as the first coordinate, and y as the second. It shears the plane.

This example proves something worth remembering: exponentiating a matrix is not the same as exponentiating each entry. The off-diagonal one creates a time-dependent shear, not an unrelated collection of scalar exponentials.

## Verify the differential equation

Differentiate the series for the exponential of t B, term by term. In finite dimensions, its absolute convergence is uniform when t stays in a bounded interval, so the differentiation can be justified by the usual power-series argument.

The derivative of the n-th nonconstant term brings down n and cancels part of the factorial. When we reindex what remains, we get B multiplied by the original exponential series.

Because B commutes with every power of B, the same derivative also equals the exponential multiplied by B.

So the time derivative of the exponential of t B is B times the exponential of t B. At time zero, the exponential is the identity. That is precisely the matrix version of our original growth equation.

There is also a geometric interpretation. For a very small time step h, the exponential of h B is approximately the identity plus h B. Thus B specifies the *instantaneous direction of motion* at every vector. The exponential combines all these infinitesimal motions into a finite transformation.

## Combining time intervals

If we run the flow for time s and then time t, do we get the flow for time s plus t?

Yes, because both operators are exponentials of scalar multiples of the *same* B. Those multiples commute.

The power series can be multiplied and regrouped using the binomial theorem for commuting factors. We obtain the exponential of s B times the exponential of t B equals the exponential of the sum of their arguments, which is the exponential of open parenthesis s plus t close parenthesis B.

In particular, taking s equal to negative t shows that the exponential of t B is always invertible. Its inverse is the exponential of negative t B.

But do not generalize this to arbitrary matrices A and B. In general, exponential of A plus B is *not* exponential of A times exponential of B. The rearrangement uses commutativity.

For a concrete counterexample, take A to be our upper shear generator and B to be its transpose. Their products AB and BA are different. Their exponentials are identity plus A and identity plus B, so the product has trace three. The exponential of A plus B has trace greater than three: because A plus B squares to the identity, its even powers contribute additional positive terms. The two matrices cannot be equal.

## Which generators preserve length?

A particularly important case occurs when B adjoint equals negative B. Such an operator is called *skew-adjoint*. Over the real numbers, we also say skew-symmetric.

Let Q of t be the exponential of t B. We can compute its adjoint by taking the adjoint of the power series term by term. The adjoint of a power of B is the same power of B adjoint. Therefore the adjoint of Q of t is the exponential of t times B adjoint.

If B is skew-adjoint, that is the exponential of negative t B, which is the inverse of Q of t.

Thus Q adjoint times Q equals the identity, and Q times Q adjoint equals the identity as well. The exponential is unitary—or orthogonal in the real case.

We have found a systematic way to turn an instantaneous, skew-adjoint generator into a continuous length-preserving motion.

## Recover the ordinary rotation matrix

Take the real two-by-two operator J that sends x and y to negative y and x. It rotates every vector by a quarter turn counterclockwise.

J squared is negative the identity. Its adjoint equals negative J, so it is skew-symmetric.

Now examine the exponential of t J. The even powers of J alternate between the identity and its negative. The odd powers alternate between J and its negative.

If we group the even powers of the exponential series, we get cosine of t times the identity. If we group the odd powers, we get sine of t times J.

So the exponential of t J equals cosine t times the identity, plus sine t times J. Applied to a vector, this is the ordinary rotation through angle t.

That is a remarkable connection: the trigonometric rotation formula emerges from the operator exponential without assuming it as the definition of a rotation.

And if we change the generator to a times J, the rotation angle after time t is a times t. The generator controls angular speed.

## Why the course needs this construction

Later we will build rotations that act on several perpendicular principal planes at once. Each plane can rotate through a different angle. We will also encounter skew-adjoint operators built from angle data.

Matrix exponentials give us a language for combining those infinitesimal rotations into a single canonical motion. The link between exponential, cosine, and sine will then appear inside direct-rotation formulas.

The same construction extends to bounded operators on a Banach space. Unbounded generators require a different analytic treatment, which we will develop in later parts of the course.

For your final reconstruction, start with the exponential power series. Explain why it converges in operator norm. Differentiate it to recover the flow equation. Then prove that a skew-adjoint generator produces a unitary family.

And if you want one concrete calculation to keep in mind, work out the even and odd powers of J until you can derive the sine-and-cosine rotation formula without looking it up.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For a square matrix or bounded operator \(B\), the exponential is the norm-convergent series

\[
e^{tB}=\sum_{n=0}^\infty\frac{t^n B^n}{n!},\qquad
\frac{d}{dt}e^{tB}=Be^{tB}=e^{tB}B.
\]

One-parameter group law: \(e^{sB}e^{tB}=e^{(s+t)B}\), with inverse \(e^{-tB}\). More generally \(e^{A+B}=e^Ae^B\) is guaranteed when \(AB=BA\), not for arbitrary matrices. If \(B^*=-B\) then \((e^{tB})^*=e^{-tB}\), hence \(e^{tB}\) is unitary. For \(J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\), \(J^2=-I\) and \(e^{tJ}=\cos(t)I+\sin(t)J\).

**Lean bridge.** `ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean` defines the time-parametrized exponential on a complex Hilbert space, using the established exponential of a Banach algebra:

```lean
noncomputable def expTime (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  exp (t • B)
```

It provides the derivative statement in the same module:

```lean
theorem hasDerivAt_expTime (B : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (expTime B) (expTime B t * B) t :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) B t
```

The declaration `norm_expTime_I_smul` proves length preservation for the exponential of imaginary times a self-adjoint operator. That is the complex counterpart of the spoken skew-symmetric rotation argument. For the trigonometric connection, `ForTauCeti/Analysis/Normed/Algebra/TrigonometricSeries.lean` proves `exp_mul_eq_cosSeries_add_mul_sinSeries` under an explicit commutation hypothesis and a square-minus-one condition on the relevant support.

`expTime` and the trigonometric-series results are part of the DKPS/TauCeti mathematical dependency story, including upstreamed foundations; their current import location does not determine where the mathematics originated.

**Reconstruction:** Show \(\|B^n\|\le\|B\|^n\), derive the exponential derivative from the series, compute \(e^{tN}\) for \(N^2=0\), and use \(B^*=-B\) to prove \(e^{tB}\) is unitary. Explain where commutativity enters the addition law.
