# 092250 — Hille–Yosida and contraction semigroups

**Draft status:** audio-first mathematical lecture. **Recommended background:** `083000` closed operators, `086000` resolvents, `091250` Yosida regularization, `092000` unitary groups.

<!-- BEGIN SPOKEN LECTURE -->

# When an unbounded operator generates time evolution

The heat equation evolves forward in time and loses energy. The Schrödinger equation, in its unitary formulation, preserves energy and evolves in both time directions. Both involve differential operators that are typically unbounded on their Hilbert spaces. What operator conditions guarantee that such equations define a continuous family of bounded evolutions?

A contraction semigroup is a family S of t, defined for nonnegative time, with three properties. S of zero is the identity. Evolution through time s followed by time t is evolution through s plus t. And the norm of S of t is at most one. We also require strong continuity: for every fixed input vector x, S of t x depends continuously on t in Hilbert-space norm.

The generator G is the right derivative at time zero, on precisely the vectors for which that derivative exists. That domain may be proper and dense. The Hille–Yosida and Lumer–Phillips theorems explain how resolvent and dissipativity conditions characterize these generators.

## Dissipativity as an energy inequality

Suppose x is in the domain of G, and the trajectory is differentiable. Differentiating the squared length of the trajectory at time zero gives twice the real part of the inner product of G x with x. If S is contractive, that derivative cannot be positive. Thus every contraction generator satisfies the dissipativity inequality: the real part of the inner product of G x with x is nonpositive.

The converse is more demanding. A densely defined dissipative operator might fail to have enough solutions to the equation lambda y minus G y equals x. The additional requirement is that this shifted operator map its domain onto the whole Hilbert space for at least one positive lambda.

For a densely defined operator, dissipativity together with that range condition makes G maximally dissipative. The Lumer–Phillips theorem says that its closure, when appropriate, generates a strongly continuous contraction semigroup. In the common closed, densely defined setting, the two conditions are exactly what we need.

Why does surjectivity matter? Dissipativity controls the norm of a solution if it exists, but only the range condition guarantees that every input has one. We need the resolvent on the entire space to construct an everywhere-defined evolution.

## Resolvent bounds

Take a positive lambda and solve lambda y minus G y equals x. Taking the real part of the inner product with y and using dissipativity gives lambda times the squared norm of y no greater than the norm of x times the norm of y.

So the resolvent has norm at most one divided by lambda. A resolvent identity then extends appropriate range information across the positive half-line, and each positive lambda has a bounded resolvent with this estimate.

The Hille–Yosida theorem provides a parallel formulation. A densely defined closed G generates a contraction semigroup precisely when the positive real half-line lies in its resolvent set and every positive integer power of the resolvent has norm at most lambda to the negative power. The one-power estimate and full-range condition in a Hilbert space arise naturally from maximal dissipativity, and then the higher power bounds follow by submultiplicativity.

## Approximate G by bounded generators

Define J lambda as lambda times the resolvent of lambda minus G. The resolvent estimate makes J lambda a contraction. Define the bounded Yosida generator G lambda as lambda times J lambda minus lambda times identity.

G lambda is dissipative: for any x, the real part of its inner product with x is at most lambda times the norm of J lambda x times the norm of x, minus lambda times the squared norm of x, which is nonpositive.

Because G lambda is bounded, the ordinary exponential series defines S lambda of t as the exponential of t G lambda. Differentiating the squared norm of its action on a vector shows that S lambda of t is contractive for every nonnegative t.

On every vector in the domain of G, the bounded generators G lambda converge to G. Their resolvent origins also make these approximants commute with each other, so a Duhamel comparison controls differences between their exponentials on domain vectors. On a bounded time interval, these differences approach zero uniformly for each fixed domain vector.

Now approximate an arbitrary vector by domain vectors. Contractivity prevents the approximation error from growing. Completeness gives a limiting family of contractions on the whole Hilbert space, and the estimates give strong continuity and the semigroup law.

This is the constructive content behind the generation theorem: the infinite-dimensional evolution is obtained as the strong limit of ordinary bounded exponentials.

## The heat equation as a model

Let the Hilbert space be square-integrable functions on an interval with zero boundary values. The Laplacian with Dirichlet boundary conditions has eigenfunctions given by sines and negative eigenvalues proportional to n squared.

Take G to be this Laplacian. It is dissipative because integration by parts gives the inner product of G f with f equal to minus the squared norm of the derivative, for functions satisfying the boundary conditions. Its spectrum is negative and its positive resolvents exist.

The generated semigroup multiplies the n-th sine coefficient by an exponential with exponent negative n squared times time, up to the interval's geometric scale. Every mode contracts, and high-frequency modes decay faster. At time zero, the semigroup is strongly continuous on the whole square-integrable space, even though the initial derivative exists only for functions in the operator domain.

Contrast this with the multiplication operator whose eigenvalues are positive n squared. Its exponential grows without bound across high frequencies for positive time and does not define a bounded evolution on the entire Hilbert space. The sign of the generator's spectrum is essential to contractivity.

## Groups, semigroups, and reversible motion

If the generator is skew-adjoint, its evolution is unitary and extends to positive and negative times. That is the setting of Stone's theorem. A maximally dissipative generator generally gives only forward contractive motion. Diffusion loses information, and the backwards heat evolution is not bounded on all square-integrable initial data.

The distinction is mathematical, not terminological. Self-adjointness supports phase-preserving unitary flows after multiplication by the imaginary unit. Maximal dissipativity supports one-sided contraction semigroups. Yosida resolvent approximants provide a common route from an unbounded generator to bounded exponentials in both settings.

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
