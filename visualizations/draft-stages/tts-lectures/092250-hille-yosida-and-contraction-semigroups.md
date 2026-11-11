# 092250 — Hille–Yosida and contraction semigroups

**Draft status:** audio-first mathematical lecture. **Recommended background:** `083000` closed operators, `086000` resolvents, `091250` Yosida regularization, `092000` unitary groups.

<!-- BEGIN SPOKEN LECTURE -->

# Why some evolutions run only forward

Think about heat spreading along a metal rod. A sharp temperature pattern smooths out. Its fine-scale oscillations disappear faster than its broad, slowly varying features.

Mathematically, it is tempting to say: take a differential operator, exponentiate it, and let the exponential move the temperature forward in time.

But that is not automatically legitimate. Differential operators are typically unbounded, and exponentiating the wrong one can magnify high-frequency components without limit. We need a condition that guarantees a well-defined bounded evolution for every starting state.

The Hille–Yosida theorem, together with the Hilbert-space Lumer–Phillips criterion, gives such conditions. Its central ingredients are energy dissipation and the ability to solve a shifted operator equation.

We'll start with an explicit heat-like model.

## An infinite set of decaying modes

Work on ell two. Define an operator G to multiply coordinate N by negative N squared.

The first coordinate has decay rate one. The second has decay rate four. The third has decay rate nine. The higher the coordinate number, the faster the corresponding mode should decay.

G is unbounded. Its domain consists of sequences for which N squared times the N-th coordinate is still square summable.

Now define S of t for nonnegative time by multiplying coordinate N by the exponential of negative N squared times t.

Every multiplier lies between zero and one. So S of t cannot increase the length of any vector. We call such an operator a contraction.

At time zero, every multiplier is one and S of zero is the identity. Evolving for time s and then for time t is the same as evolving for time s plus t. These are the semigroup laws.

The word semigroup means that we only require nonnegative time. The evolution has a forward direction.

## Continuity does not mean differentiability everywhere

For each fixed ell-two vector, S of t x approaches x as time approaches zero from above.

You can prove this as in the case of rotations: control a finite number of coordinates using ordinary scalar continuity, then use the small squared length of the tail. Contractivity ensures the tail never grows.

This is strong continuity. It is the continuity required in a strongly continuous contraction semigroup.

It is not operator-norm continuity. At any fixed positive time, sufficiently high modes have decayed almost completely. If we test the difference between S of t and the identity on one such basis vector, its norm is almost one, however close t may be to zero. Yet every fixed vector still has a small tail and moves continuously.

Now ask whether the trajectory has a derivative at time zero. On coordinate N, the derivative of the exponential factor is negative N squared. So the candidate derivative is G applied to x.

Take a vector whose N-th coordinate is one divided by N squared. It belongs to ell two. But G would turn it into the sequence of negative ones, which does not belong to ell two.

The evolution S of t x exists and is continuous for this vector, but its derivative at time zero does not exist in ell-two norm.

If we restrict x to the domain of G, the derivative does exist and equals G x.

That is how a semigroup can be defined everywhere while its generator remains an unbounded, domain-restricted operator.

## Why negative growth is the right condition

In our example, every spectral value of G is nonpositive. But we want a condition that still makes sense for operators without an eigenvector basis.

Take an allowed vector x. The real part of the inner product of G x with x measures the instantaneous tendency of its squared length to change. If this quantity is nonpositive for every allowed x, we call G dissipative.

To see the connection, suppose a trajectory x of t is differentiable and satisfies the evolution equation: its derivative equals G applied to x of t. Differentiate its squared length. The result is twice the real part of the inner product of G x of t with x of t.

If G is dissipative, this derivative is nonpositive. The motion cannot increase the norm along such trajectories.

So dissipativity is the infinitesimal version of contractivity.

But it is not enough by itself to build a semigroup. An operator may be dissipative while having a domain too small to provide the solutions needed for a well-defined evolution on the whole Hilbert space.

We need one more condition.

## The missing condition is solvability

Choose a positive number lambda and consider the equation lambda times y minus G y equals x.

If y is a solution, take its inner product with y and then take the real part. Dissipativity gives a lower bound of lambda times squared length of y. Cauchy–Schwarz gives an upper bound of the length of x times the length of y.

Thus the length of y is at most the length of x divided by lambda. The solution, if it exists, is unique and depends continuously on x.

But an estimate on a possible solution does not guarantee that every x has one. We must require the shifted operator lambda identity minus G to map its domain onto the whole Hilbert space.

For a densely defined, closed, dissipative operator on a Hilbert space, surjectivity at one positive lambda is enough. Such an operator is called maximally dissipative. The Lumer–Phillips theorem says that it generates a strongly continuous contraction semigroup.

The same theorem gives the converse: the generator of any strongly continuous contraction semigroup is maximally dissipative.

This is a characterization, not just a convenient sufficient condition.

## How the resolvent constructs the motion

When lambda identity minus G is onto, its inverse is the resolvent at lambda. The estimate we just proved says that the resolvent norm is at most one over lambda.

Multiply it by lambda to obtain a bounded contraction J sub lambda. Then take lambda times J sub lambda minus lambda times identity. This is a bounded Yosida approximation G sub lambda of the generator.

The approximate generator is dissipative. Therefore its ordinary exponential, at any nonnegative time t, is a contraction. Everything here is bounded, so the exponential can be defined by a norm-convergent power series.

As lambda grows, G sub lambda x approaches G x for every vector in the original domain. Comparing the bounded exponentials shows that, on domain vectors, their trajectories become close over each fixed bounded time interval.

Because the domain is dense and every approximating evolution is a contraction, this convergence extends to arbitrary starting vectors. The resulting limit is a strongly continuous contraction semigroup with generator G.

That is the constructive idea behind the generation theorem: solve shifted equations, build bounded generators, exponentiate, and pass to a strong limit.

The Hille–Yosida theorem expresses the conditions in resolvent language. For a densely defined closed contraction generator, every positive lambda belongs to the resolvent set of lambda identity minus G, and the norm of the N-th power of the resolvent is at most one divided by lambda to the N-th power, for every positive integer N.

In a Hilbert space, maximal dissipativity provides the one-resolvent estimate and surjectivity; the higher-power bounds then follow by multiplying the bounded resolvent operators.

## Return to the heat equation

The diagonal model is exactly what appears when the heat equation on an interval is written in its sine-wave coordinates.

Take square-integrable functions on the interval from zero to pi, with temperature fixed at zero at both endpoints. The spatial second-derivative operator, with its Dirichlet boundary conditions, sends the N-th sine wave to negative N squared times that sine wave.

So a temperature profile can be expanded into sine waves, and each coefficient decays at the rate from our diagonal model. Broad modes decay slowly; fine-scale modes disappear quickly.

The evolution is contractive because no coefficient grows. It is strongly continuous on the entire square-integrable space. But taking a derivative at time zero requires additional regularity of the initial temperature profile, exactly the condition that places it in the domain of the Laplacian.

Now imagine reversing the sign of the Laplacian. Each sine coefficient would grow like the exponential of positive N squared times time. For any positive time, these multipliers are unbounded as N grows. That formula does not define a bounded evolution on every square-integrable initial state.

The sign and the solvability conditions really do determine whether an evolution is well-posed on the chosen Hilbert space.

## Forward semigroups and reversible groups

A unitary group preserves lengths and allows both positive and negative times. For a self-adjoint A, multiplying A by the imaginary unit gives the skew-adjoint generator of such a group.

A contraction semigroup allows loss of length and requires only forward time. Its generator is maximally dissipative, and it need not permit a bounded inverse evolution for negative time.

Heat diffusion illustrates the difference. Forward time suppresses high-frequency information. Reversing time would require restoring those modes by arbitrarily large amplification.

The general lesson is that an unbounded operator can generate a bounded evolution, but the operator must have enough domain and resolvent structure to support it. Dissipativity controls growth; surjectivity of a shifted operator supplies solvability; Yosida approximation turns both ingredients into a constructive family of bounded evolutions.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and source correspondence (display only)

On a complex Hilbert space, a densely defined closed operator \(G\) generates a strongly continuous contraction semigroup exactly when it is maximally dissipative:
\[
\Re\langle Gx,x\rangle\le0\ (x\in D(G)),\qquad
\operatorname{ran}(\lambda I-G)=H\quad\text{for some }\lambda>0.
\]
A standard Hille–Yosida form assumes every \(\lambda>0\) is in the resolvent set and \(\|(\lambda I-G)^{-n}\|\le\lambda^{-n}\) for integers \(n\ge1\). Define \(J_\lambda=\lambda(\lambda I-G)^{-1}\) and \(G_\lambda=\lambda(J_\lambda-I)\). Then \(e^{tG_\lambda}\) are contractions for \(t\ge0\); their strong limit constructs the semigroup.

**Source correspondence and scope.** `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` defines self-adjoint symmetric resolvent approximants and bounded unitary exponentials (`yosidaApproximantSymSA`, `expApprox`) and proves a strong unitary-group limit (`expLimit`). The general contraction-semigroup and Lumer–Phillips statements in this lesson are broader classical mathematics; they are not claimed as formalized by those declarations. The example uses the self-adjoint Dirichlet Laplacian, with standard domain \(H^2\cap H_0^1\) on a finite interval.
