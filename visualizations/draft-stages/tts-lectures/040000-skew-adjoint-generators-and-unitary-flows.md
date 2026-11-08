# 040000 — Skew-adjoint generators and unitary flows

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `009000` inner products; `012000` adjoints; `013000` operator classes; `039000` matrix exponentials. **Next:** operator trigonometric functions and principal-plane geometry.

<!-- BEGIN SPOKEN LECTURE -->

# When does a motion preserve lengths?

A real skew-symmetric two-by-two matrix K with first row zero, negative one and second row one, zero generates rotations. Its exponential at time t is the rotation matrix through angle t. The identity follows from the power series, because K squared is negative identity.

Today we will reverse the question. Suppose we are given a motion that preserves lengths and angles at every moment. What must its instantaneous generator look like? And if we start with a generator of that kind, can we prove that the motion preserves geometry for all time?

The proof combines the identity for an adjoint, differentiation of a matrix exponential, and the algebra of its power series. These ingredients also describe continuous rotations between subspaces.

## Begin with an observable quantity

Imagine a vector moving through a real Euclidean space. Its position at time t is called x of t. A length-preserving motion should keep the square of the vector's length constant.

Why square the length? Because it is an inner product of the vector with itself, and differentiating an inner product is straightforward.

Suppose the velocity is given by a linear rule: the derivative of x equals K applied to x, for some fixed matrix K.

Differentiate the square of the length. The product rule gives two terms: the inner product of K x with x, and the inner product of x with K x.

Use the adjoint in the first term to move K to the other side. The derivative becomes the inner product of x with K adjoint plus K, applied to x.

So if K adjoint equals negative K, the two terms cancel. The length cannot change.

Such a generator is called skew-adjoint. Over real coordinates, its matrix is skew-symmetric: transposing the matrix changes its sign. Over complex coordinates, transposition is replaced by conjugate transposition.

We did not have to solve the differential equation to discover the condition. Conservation of length was visible directly in the rate of change.

## A concrete two-dimensional calculation

Take the operator J that sends a vector with coordinates x and y to negative y and x. Its matrix has zero diagonal entries, negative one in the top-right corner, and positive one in the bottom-left.

Because its transpose is negative J, it is skew-symmetric. The differential equation says that the horizontal velocity is negative the vertical coordinate, and the vertical velocity is the horizontal coordinate.

If the moving vector begins at one and zero, we can guess that the solution is cosine t and sine t. Differentiate those coordinates. The derivatives are negative sine t and cosine t, exactly what J prescribes.

The trajectory is a unit circle. But our conservation argument proves much more than this example. Every initial vector moves on a circle of its original radius, even when we do not explicitly solve for its coordinates.

Now multiply J by a real number, say three. The same orbit is traversed three times as fast. The generator controls speed and orientation. Skew-adjointness controls whether length is preserved.

## From one vector to an operator-valued flow

Instead of following one starting vector, package all solutions into a single operator Q of t. For each starting vector x, Q of t sends x to its position at time t.

The differential equation for Q is: its derivative equals K times Q, and Q at time zero is the identity.

The matrix exponential supplies a solution: by its power-series definition, the derivative of the exponential of t K is K times that exponential. Q of t is the exponential of t K. Differentiating its power series gives the required differential equation, and plugging in zero gives the identity.

To prove Q is length-preserving, we have two routes. The first applies our derivative-of-length calculation to every starting vector.

The second is entirely algebraic. The adjoint of the exponential of t K is the exponential of t times K adjoint. When K is skew-adjoint, this becomes the exponential of negative t K. But that is also the inverse of the exponential of t K.

Therefore Q adjoint times Q equals the identity. In fact Q times Q adjoint equals the identity as well. In a real Hilbert space we call such an operator orthogonal; over complex scalars we call it unitary.

Notice that both identities matter. Preserving lengths gives Q adjoint Q equals the identity. In infinite dimensions, this by itself does not force Q to be onto. Having the inverse from the exponential establishes the stronger, two-sided condition.

## Can we reverse the argument?

Suppose now that we start with a differentiable family of unitary operators Q of t. It begins at the identity, and it satisfies the flow law: doing the motion for time s, then time t, is equivalent to doing it once for time s plus t.

Call the derivative at time zero K.

Because Q adjoint Q is always the identity, differentiating at zero gives K adjoint plus K equals zero. So K must be skew-adjoint.

This is not a coincidence limited to rotations in the plane. Every differentiable unitary one-parameter group in a finite-dimensional space has a skew-adjoint infinitesimal generator. The group law also tells us the derivative at any other time: it is K times Q of t. That differential equation has the exponential solution.

In finite dimensions, then, we get a clean correspondence: skew-adjoint generators produce smooth unitary flows, and smooth unitary flows that obey the time-addition law come from skew-adjoint generators.

The qualifier about the time-addition law is essential. An arbitrary path through unitary matrices can speed up or slow down in a changing way, and need not be the exponential of one fixed generator times t.

## What changes in three dimensions?

In the plane, every rotation around the origin is determined by one angle. In three dimensions, we can rotate around different axes.

Imagine first rotating a cube about the vertical axis, then rotating it about a horizontal axis. Reverse the order and its final orientation generally changes.

That is a failure of commutativity. The two infinitesimal generators need not commute either. Consequently, the exponential of t times K one plus K two need not equal the product of the two separate exponentials.

If the generator varies with time, there is a related warning. A skew-adjoint K of t still guarantees length preservation for solutions of the time-dependent differential equation, as long as a sufficiently regular solution exists. The same derivative-of-length argument works at every time.

But the resulting motion is not generally the exponential of the integral of K of t. That shortcut would forget the order in which noncommuting transformations occur.

So we have separated two ideas: skew-adjointness is what preserves geometry; commutation is what simplifies the formula for combining motions.

## The complex viewpoint

Over a complex Hilbert space, there is another convenient description. Start with a self-adjoint operator H. Multiply it by the imaginary unit and a minus sign. That gives a skew-adjoint generator.

The resulting unitary flow is the exponential of negative imaginary t H. If x evolves by this flow, its squared norm remains constant.

This is the operator structure behind the time-evolution equation in quantum mechanics. We do not need quantum mechanics to prove the statement. The proof rests on the identity between a self-adjoint operator and the negative adjoint of its imaginary multiple.

The spectrum of H also gives a way to read the motion. In an eigenvector direction with real eigenvalue lambda, the flow multiplies that vector by the complex number whose angle is negative lambda times t. The magnitude stays one. Different eigenspaces can acquire different phases, all without changing the total norm.

There is an important boundary to our proof. Everything we just argued using norm-convergent exponentials applies directly to bounded generators, including all finite matrices. For unbounded generators on an infinite-dimensional Hilbert space, defining the flow and controlling its domain require more theory. We will return to that rather than silently extending the bounded proof.

## A reconstruction challenge

Let us collect the reasoning without relying on a memorized theorem.

Start with the equation saying velocity equals K applied to position. Differentiate the squared length and rewrite the result using the adjoint. That tells you exactly why K adjoint equals negative K makes length constant.

Next, construct the full flow as the exponential of t K. Show that its adjoint is its inverse. That proves the motion is unitary, not merely an isometric embedding.

Finally, run the reasoning backward. Differentiate Q adjoint Q equals the identity at time zero. You will recover the skew-adjoint generator.

That is the central idea of this lecture. A unitary flow is not just a sequence of unrelated matrices. It is continuous motion whose instantaneous rule is constrained by geometry. When we later rotate one spectral subspace toward another, these generators will let us say not only where the subspace ends up, but how the rotation is constructed.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a fixed bounded operator \(K\) on a real or complex Hilbert space,
\[
K^*=-K,\quad Q(t)=e^{tK},\quad Q(t)^*=Q(-t)=Q(t)^{-1},\quad Q(t)^*Q(t)=Q(t)Q(t)^*=I.
\]
For a differentiable \(x\) with \(x'=Kx\),
\[
\frac{d}{dt}\|x(t)\|^2=\langle Kx,x\rangle+\langle x,Kx\rangle=0.
\]
Conversely, if a differentiable one-parameter unitary group starts at the identity, differentiating \(Q(t)^*Q(t)=I\) at zero gives \(K^*=-K\), for \(K=Q'(0)\). These arguments do not assert the unbounded-generator theorem.

**Lean bridge.** In `ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean` (namespace `TauCeti`, with complex Hilbert-space parameters), the project's bounded complex version makes the adjoint condition explicit:

```lean
def IsSkewAdjointCLM (B : H →L[ℂ] H) : Prop :=
  ContinuousLinearMap.adjoint B = -B
```

The time-dependent exponential and its derivative are declared as:

```lean
noncomputable def expTime (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  exp (t • B)
```

```lean
theorem hasDerivAt_expTime (B : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (expTime B) (expTime B t * B) t :=
  hasDerivAt_exp_smul_const (𝕂 := ℝ) B t
```

The theorem `norm_expTime_I_smul` then proves preservation of the norm of each vector for an imaginary multiple of a self-adjoint operator. The letter `I` there is the complex imaginary unit, **not** the identity operator. The statements are quoted from the available DKPS snapshot; this overlay does not introduce or compile new Lean declarations.

**Reconstruction:** Differentiate a squared norm using adjoints; compute the exponential of the planar quarter-turn generator; derive skew-adjointness from a differentiable unitary group; explain why time-dependent noncommuting generators cannot simply be combined by addition inside one exponential.
