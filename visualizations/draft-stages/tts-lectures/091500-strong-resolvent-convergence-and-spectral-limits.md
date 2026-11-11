# 091500 — Strong resolvent convergence and spectral limits

**Draft status:** audio-first mathematical lecture. **Recommended background:** `081000` resolvents, `088000` spectral calculus, `091000` bounded regularization, `091250` resolvent approximants.

<!-- BEGIN SPOKEN LECTURE -->

# How can operators converge when their high frequencies disagree?

Suppose an infinite diagonal operator multiplies coordinate number N by N. Now replace it by a bounded operator whose first several multipliers are close to the originals, but whose very high multipliers are drastically different.

Does the bounded approximation converge to the unbounded operator?

There cannot be convergence in the ordinary operator norm. The original operator is unbounded, and the approximants are bounded. But that does not mean the approximations are useless. A fixed square-summable vector has very little total mass far enough out in its coordinate tail. The approximations may therefore behave correctly on that fixed vector even while they behave badly on a high coordinate chosen after seeing the approximation.

This distinction motivates strong resolvent convergence. Rather than compare unbounded operators directly, we compare bounded inverses of their shifted versions.

## A diagonal approximation that exposes the problem

Work on ell two. Define A to multiply coordinate N by N, with domain consisting of the sequences for which N times the N-th coordinate remains square summable.

For a positive number R, define A sub R by replacing N with R squared times N divided by R squared plus N squared. Every A sub R is bounded and self-adjoint.

Fix coordinate five. As R grows, its multiplier approaches five. The same is true for coordinate a thousand or a million, as long as that coordinate is held fixed while R increases.

But for any one chosen R, go far enough into the sequence. When N is far greater than R squared, the regularized multiplier becomes very small, while the original multiplier N becomes enormous.

So the approximants do not become uniformly accurate on all directions at once.

This is the difference between two common kinds of convergence. Operator-norm convergence controls the worst error over every unit vector. Strong operator convergence controls the error on each vector separately. It allows a bad direction to move farther out as the approximation improves.

For unbounded A, even the difference between A sub R and A is not an operator defined on all of ell two. We need a comparison that stays meaningful on the whole Hilbert space.

## Compare shifted inverses instead

Self-adjoint operators have a useful property: their spectrum is real. If we subtract the imaginary unit times identity, the resulting operator has a bounded inverse defined on the entire Hilbert space.

The resolvent at imaginary one takes an arbitrary input vector and returns a vector in the operator's domain. Its norm is at most one.

So define the resolvent of A sub R at imaginary one, and compare it with the resolvent of A at the same point. Both maps are bounded on ell two, even though A itself is unbounded.

Strong resolvent convergence means that these two bounded inverses approach one another on every fixed vector. We do not require their operator norms of difference to approach zero.

For self-adjoint operators it is enough to check one nonreal shift. The resolvent identities and uniform bounds let us move the convergence to other nonreal shifts.

This is a way to talk about convergence without demanding that the approximating operators have the same domains or finite operator norms.

## Verify it in the running example

On coordinate N, the resolvent of A at imaginary one multiplies by one divided by N minus imaginary one.

The resolvent of A sub R multiplies by one divided by the regularized multiplier minus imaginary one.

For each fixed N, the second denominator approaches the first, so the multipliers converge.

More importantly, both resolvent multipliers have magnitude at most one. Their difference therefore has magnitude at most two.

Apply the difference to a fixed ell-two sequence x. The squared length of the result is a sum of coordinate errors. Each error approaches zero, and the squared error is at most four times the squared magnitude of the corresponding coordinate of x.

Those dominating terms have a finite sum because x belongs to ell two. Dominated convergence for series proves convergence of the whole resolvent output.

Now test operator-norm convergence. Keep R fixed and choose an extremely high coordinate N. The regularized eigenvalue there is nearly zero, so its resolvent multiplier is nearly one divided by negative imaginary one, a number of magnitude one. The original resolvent multiplier is nearly zero.

The difference is nearly one on that unit basis vector. Thus the operator norm of the resolvent difference stays large, no matter how far R has grown.

We have proved two facts from the same example: strong resolvent convergence holds, and norm-resolvent convergence fails.

## What the resolvent says about domains

A closed operator is encoded by its graph: all pairs consisting of an allowed input and its output. For an unbounded operator, the graph keeps track of the domain as well as the values.

Take an arbitrary vector x in our Hilbert space. Apply the resolvent of A at imaginary one and call the answer y. By the resolvent equation, y lies in the domain of A, and A applied to y equals x plus imaginary y.

Now do the same with A sub R. Call that answer y sub R. Strong resolvent convergence gives y sub R approaching y.

It also gives convergence of the operator images. A sub R applied to y sub R equals x plus imaginary y sub R, which approaches x plus imaginary y, or A applied to y.

So we have produced points on the graphs of the approximating operators that converge in both coordinates to a point on the graph of A.

Notice what this does not say. We selected the inputs y sub R using the resolvents. We did not assume that a single fixed vector lies in every domain, or that applying every A sub R to that fixed vector reproduces its image under A.

That is why resolvent convergence is well suited to families of operators with changing domains.

## What carries over to time evolution

For self-adjoint A, the spectral theorem also defines unitary motion by multiplying each spectral component by the complex exponential of imaginary time times its spectral value.

In the diagonal example, coordinate N rotates at angular speed N. The approximating group rotates it at the regularized speed.

For any fixed vector and time, the phases converge coordinate by coordinate. Their magnitudes are always one, so dominated convergence proves that the evolved vectors converge in norm. In fact, convergence is uniform over a fixed bounded interval of times.

The general strong-resolvent theorem gives this conclusion for self-adjoint operators: the associated unitary groups converge strongly, uniformly on compact time intervals. More generally, bounded continuous functions of the operators converge strongly through the functional calculus.

Again, uniformity in time on each fixed vector is different from uniformity over every unit vector. For example, at time pi the original diagonal group changes the sign of every odd coordinate. For one fixed regularization scale, sufficiently high coordinates barely rotate at all. Testing a high odd basis vector gives a difference close to two.

So there is no corresponding operator-norm convergence of the unitary groups.

## A sharp spectral cutoff can still fail

One more distinction is essential. A spectral projection is built from an indicator function: keep spectral values on one side of a boundary and discard the others. An indicator function jumps at its boundary.

Consider a one-dimensional example. Let A sub N be multiplication by one divided by N, and let A be multiplication by zero. These operators converge in ordinary operator norm, so their resolvents converge even in resolvent norm.

Now ask for the spectral projection onto values less than or equal to zero. For every A sub N, the projection is zero, because its only spectral value is positive. For the limit A, the projection is the identity, because its only spectral value is zero.

The projections do not converge.

The failure happens exactly at the boundary, where the limiting operator has spectral mass. Under strong resolvent convergence, projections for a spectral interval do converge strongly when the limiting spectral measure assigns no mass to the interval's boundary. Without a boundary condition, sharp cutoffs can jump even when the underlying operators converge very well.

## The useful hierarchy

Operator-norm convergence controls every direction at once. Strong convergence controls each fixed vector. Strong resolvent convergence compares bounded shifted inverses and remains meaningful for unbounded operators and changing domains.

It is strong enough to control bounded continuous spectral functions and unitary time evolution, but a discontinuous spectral selection needs an additional boundary assumption.

The central lesson is that convergence must be matched to the question. To understand unbounded generators and their flows, strong resolvent convergence often preserves exactly the information we need, without imposing a uniform estimate that the high-frequency example shows cannot hold.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and source correspondence (display only)

For self-adjoint \(A_n,A\), strong resolvent convergence is
\[
(A_n-iI)^{-1}x\to(A-iI)^{-1}x\quad\text{for all }x\in H.
\]
For \(y_n=(A_n-iI)^{-1}x\), both \(y_n\to y\) and \(A_n y_n=x+i y_n\to x+i y=Ay\). The diagonal regularizer \(f_R(n)=R^2n/(R^2+n^2)\) has strong resolvent but not norm-resolvent convergence to \(\operatorname{diag}(n)\). Strong resolvent convergence of self-adjoint operators implies strong convergence of \(g(A_n)\) for bounded continuous \(g\); spectral projection convergence requires an appropriate boundary-null condition.

**Checked source map.** `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` includes `expApprox`, `cauchySeq_expApprox`, and `expLimit`, with convergence of the unitary approximations. `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralCutOperator.lean` and `.../SpectralMeasure.lean` supply adjacent spectral-cutoff and spectral-measure infrastructure. The strong-resolvent and spectral-projection convergence principles here are classical mathematical context; the identified declarations do not assert the full general convergence theorems.
