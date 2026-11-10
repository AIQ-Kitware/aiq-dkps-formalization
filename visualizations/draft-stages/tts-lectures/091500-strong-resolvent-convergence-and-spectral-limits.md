# 091500 — Strong resolvent convergence and spectral limits

**Draft status:** audio-first mathematical lecture. **Recommended background:** `081000` resolvents, `088000` spectral calculus, `091000` bounded regularization, `091250` resolvent approximants.

<!-- BEGIN SPOKEN LECTURE -->

# When converging operators do not converge in norm

An unbounded self-adjoint operator can be approximated by bounded self-adjoint operators, but their operator norms cannot converge to the norm of the unbounded operator. How should we describe convergence in a way that still controls spectral calculations and time evolution?

The answer is to compare resolvents at a fixed nonreal point. This gives strong resolvent convergence, a topology designed for self-adjoint operators with different or changing domains.

## Three different kinds of convergence

For bounded operators T n and T, operator-norm convergence means the norm of their difference approaches zero. Strong operator convergence only asks that T n x approach T x for every fixed vector x. Strong convergence permits large errors on vectors that move with n.

For self-adjoint operators A n and A, which may be unbounded, strong resolvent convergence means that the inverse of A n minus imaginary identity, applied to each fixed vector x, converges to the inverse of A minus imaginary identity applied to x.

These resolvents are bounded. Indeed, every self-adjoint operator has a resolvent at nonreal spectral parameters, and the norm of the resolvent at imaginary one is at most one. Comparing these bounded inverses avoids subtracting operators whose domains differ.

For self-adjoint operators, testing at one nonreal point is sufficient for this notion; the resolvent identities and uniform bounds transfer the result to other nonreal points. But the topology is still weaker than norm-resolvent convergence, which asks for convergence in operator norm.

## The regularized multiplication example

Let A act on square-summable sequences by multiplying coordinate n by n. Its domain consists of sequences x for which n x n is square summable. Define A R by multiplying coordinate n by R squared n divided by R squared plus n squared.

Each A R is bounded and self-adjoint. For a fixed coordinate n, its multiplier tends to n as R grows. It follows that the resolvent multiplier one divided by the regularized eigenvalue minus imaginary one tends to one divided by n minus imaginary one.

Every such resolvent multiplier has absolute value at most one. So for a fixed square-summable vector x, the squared norm of the difference is a sum of terms dominated by four times the squared coordinate magnitudes of x. Dominated convergence for series proves that the resolvents converge strongly.

They do not converge in resolvent operator norm. For a fixed R, go far enough into the sequence that n is much larger than R squared. The regularized eigenvalue is then nearly zero, so its resolvent at imaginary one is nearly imaginary one. The original resolvent is nearly zero. The difference has magnitude nearly one on those high coordinate vectors.

Thus the supremum over unit vectors does not tend to zero, even though the resolvent difference tends to zero on each fixed vector.

## Graphs explain what the resolvent remembers

The graph of a closed operator A is the set of pairs consisting of a domain vector y and its image A y. Convergence of resolvents carries a concrete graph statement. Given an arbitrary vector x, define y n to be the resolvent of A n at imaginary one applied to x, and y to be the resolvent of A at the same point applied to x.

Then y n tends to y. Moreover, because A n y n equals x plus imaginary y n, the second graph coordinate also converges: A n y n tends to A y. So the resolvent comparison constructs approximating points in the graphs, including their operator values.

Notice the quantifiers. We choose y n from the resolvent; we have not proved that applying A n to every fixed domain vector x is meaningful or convergent. For unbounded operators, moving-domain graph convergence is often the right statement.

## What happens to time evolution

For the same diagonal example, exponentiating imaginary t times A gives a unitary flow that multiplies coordinate n by the complex phase with angle t n. Exponentiating A R gives the corresponding bounded unitary flow with regularized angle.

For every fixed vector and fixed time, the regularized phases converge coordinatewise, and their absolute values are one. Dominated convergence proves strong convergence of the flows. In fact, it is uniform when time is restricted to a bounded interval: on a domain vector, the phase difference is bounded by the time interval length times the difference of the generators; arbitrary vectors follow by density and unitarity.

But operator-norm convergence fails. For instance at time pi, very high odd coordinates have original phase negative one, while the regularized phase is near positive one. The difference approaches two in norm along those coordinates for each fixed cutoff parameter.

## Spectral projections need boundary conditions

Strong resolvent convergence supports convergence of continuous bounded functions of self-adjoint operators. A spectral projection, however, is associated to an indicator function, which jumps at the boundary of the chosen spectral set.

Here is a one-dimensional counterexample. Let A n be multiplication by one over n, and let A be zero. Their resolvents converge even in operator norm. Yet the spectral projection for the interval from negative infinity through zero is zero for every A n, and it is the identity for A. The projection does not converge.

The issue is an eigenvalue arriving exactly at the boundary. When the limiting spectral measure assigns no mass to a set's boundary, one can recover strong convergence of the corresponding spectral projections under suitable continuity hypotheses. Without that condition, even norm-resolvent convergence does not force convergence of the sharp cutoff.

## What the topology buys us

Strong resolvent convergence is well adapted to bounded approximations of unbounded self-adjoint operators. It controls their spectral actions on fixed vectors and, for bounded continuous scalar functions, their functional calculus. It also explains convergence of unitary evolutions while allowing high frequencies to behave differently on different approximants.

The important lesson is that strong convergence, norm convergence, and sharp spectral cutoff convergence answer different questions. Domain and spectral-boundary hypotheses decide which one is available.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and source correspondence (display only)

For self-adjoint \(A_n,A\), strong resolvent convergence is
\[
(A_n-iI)^{-1}x\to(A-iI)^{-1}x\quad\text{for all }x\in H.
\]
For \(y_n=(A_n-iI)^{-1}x\), both \(y_n\to y\) and \(A_n y_n=x+i y_n\to x+i y=Ay\). The diagonal regularizer \(f_R(n)=R^2n/(R^2+n^2)\) has strong resolvent but not norm-resolvent convergence to \(\operatorname{diag}(n)\). Strong resolvent convergence of self-adjoint operators implies strong convergence of \(g(A_n)\) for bounded continuous \(g\); spectral projection convergence requires an appropriate boundary-null condition.

**Checked source map.** `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` includes `expApprox`, `cauchySeq_expApprox`, and `expLimit`, with convergence of the unitary approximations. `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralCutOperator.lean` and `.../SpectralMeasure.lean` supply adjacent spectral-cutoff and spectral-measure infrastructure. The strong-resolvent and spectral-projection convergence principles here are classical mathematical context; the identified declarations do not assert the full general convergence theorems.
