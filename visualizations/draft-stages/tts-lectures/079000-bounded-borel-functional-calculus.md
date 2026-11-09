# 079000 - Bounded Borel functional calculus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `032000` finite functional calculus, `075000` continuous calculus, `076000-078000` spectral measures and cyclic models. **Next:** `080000` measurable spectral restrictions.

<!-- BEGIN SPOKEN LECTURE -->

# Applying a measurable function to a self-adjoint operator

We know how to evaluate a continuous function at a bounded self-adjoint operator. We also know that an operator can be represented as multiplication by the spectral coordinate on a suitable collection of L two spaces. Now we will combine these ideas to handle a much larger class of functions: every bounded Borel measurable function.

This extension is needed for perturbation theory. A spectral region such as an interval is selected by an indicator function, and indicators are typically discontinuous. Continuous functional calculus alone does not produce the required projection when the spectral boundary passes through the spectrum.

Our objective today is to define f of A rigorously and prove its algebraic, geometric, and convergence properties.

## Begin with simple functions

A simple function takes finitely many values. Write it as a sum of scalar coefficients times indicators of pairwise disjoint Borel sets.

For each indicator of B, we already have a projection E of B. Define the operator assigned to the simple function as the corresponding finite linear combination of these projections.

We should check that the answer does not depend on the representation of the simple function. If we divide the underlying sets into a common finite partition, both expressions agree cell by cell. The finite additivity of E then gives the same operator.

Multiplication is similarly concrete. Two simple functions multiply by multiplying their values on the intersections of their level sets. The projection identity E of B times E of C equals E of their intersection shows that the corresponding operators multiply in exactly the same way.

Taking complex conjugates of coefficients gives the adjoint operator because the projections are self-adjoint. The constant-one function gives the identity.

The norm of the operator is at most the largest absolute value of the simple function on the spectral support. To see this, decompose any vector into its orthogonal components on the level sets. The squared norm of the resulting vector is the sum of the squared coefficient magnitudes times the squared component lengths. Each coefficient magnitude is bounded by the maximum.

## Extend to bounded Borel functions

Every bounded Borel complex-valued function admits a sequence of simple Borel functions converging uniformly to it. One explicit construction partitions a bounded square in the complex plane into progressively finer cells and replaces each function value by a representative of its cell. The preimage of each cell is Borel, and the approximation error decreases uniformly.

Let f-n be such simple functions. By the norm estimate, the operator difference between f-n of A and f-m of A is bounded by the uniform difference of the symbols. The sequence of operators is therefore Cauchy in operator norm and converges to a bounded operator. Define that limit to be f of A.

Different simple approximations give the same operator, by comparing their uniform errors to f. This provides one direct construction of the bounded Borel calculus from a projection-valued measure.

It is useful to distinguish this step from the construction of the projection-valued measure itself. If we started only with continuous functional calculus, we had to build the scalar measures and projections first. Once E is available, uniform simple-function approximation of a bounded Borel symbol is straightforward.

## The algebraic laws

Addition, multiplication, scalar multiplication, and taking adjoints all commute with the operator-norm limits just used. Their identities for simple functions therefore extend to bounded Borel functions.

Thus the constant-one symbol yields the identity. The product of two symbols yields the composition of their operators. Complex conjugation yields the adjoint. If the symbols are real-valued, their operators are self-adjoint.

Every two operators obtained from the same Borel calculus commute, because their scalar symbols commute pointwise. In particular, every f of A commutes with A itself.

For a nonnegative real symbol f, its square root is again bounded and Borel. If g is that square root, then f of A equals g of A adjoint times g of A. Consequently f of A is a positive operator.

All these facts preserve the intuitive picture of multiplication operators: doing something to the spectral variable before entering the model is the same as doing it to the operator afterward.

## A norm estimate and what it does not say

If the absolute value of f is everywhere bounded by M, then the norm of f of A is at most M. For multiplication operators this follows immediately from integrating the squared magnitude of f times a vector.

There is a sharper statement: the norm is the essential supremum of f relative to the projection-valued measure. That means we ignore sets B for which E of B is zero. We must not automatically use the ordinary pointwise maximum of a Borel function on the entire spectrum.

Consider multiplication by t on L two of the unit interval. Let f be zero everywhere except at t equal to one half, where f equals a million. As a pointwise function on the spectrum its supremum is a million. But the set containing that single point has zero spectral projection. Therefore f of A is the zero operator.

By contrast, if A has an eigenvector with eigenvalue one half, the same symbol acts by a million on that eigenspace. There is no contradiction. The two operators have different spectral measures.

This distinction is absent for continuous functions: a continuous function that is large at a spectral point is large nearby, and a genuine spectral point cannot have every small neighborhood carry zero projection. For discontinuous symbols, the difference matters.

## Strong convergence under bounded pointwise limits

Suppose f-n are Borel functions bounded in magnitude by the same constant M, and f-n converges pointwise to f. Do their operators converge in operator norm? Generally, no. But they do converge strongly.

Fix a vector x. The squared norm of the difference, f-n of A minus f of A, applied to x equals the integral of the squared absolute difference between f-n and f against mu sub x.

That integrand converges pointwise to zero and is bounded by four M squared. The scalar measure mu sub x is finite. Dominated convergence therefore shows that this squared norm tends to zero.

Since x was arbitrary, the operators converge strongly.

For example, on L two of the unit interval let f-n be the indicator of the interval from zero through one over n. These functions approach zero almost everywhere, and their multiplication operators converge strongly to zero. Yet each operator has norm one, so operator-norm convergence fails.

An endpoint convention can make the symbols fail to converge at the point zero; that point has zero spectral measure in this example. Alternatively, use open intervals to obtain pointwise convergence everywhere while retaining the same phenomenon. Either way, strong convergence is the correct operator topology.

## Indicators and spectral projections

The indicator of a Borel set B yields precisely E of B. Hence every spectral projection belongs to the Borel calculus. The indicator of an intersection yields the product of the projections, and the complement yields the identity minus the original projection.

This gives a precise language for selecting a spectral cluster. Suppose A has spectrum in two separated closed intervals, one below zero and the other above two. Choosing the indicator of the lower interval gives the orthogonal projection onto the lower spectral subspace. That selection does not require selecting eigenvectors or assuming finite-dimensionality.

In later perturbation estimates we will compare the spectral projections of two different operators. Those projections need not commute because they come from different functional calculi. The commuting property applies only to projections belonging to the same P V M.

## Bounded and unbounded symbols

We have restricted f to be bounded. A bounded self-adjoint A has bounded spectral support, so the coordinate function itself is bounded there. But even for bounded A, a measurable scalar function may be unbounded near some point of the spectrum.

Its multiplication operator may then be unbounded and have a proper domain. One cannot assign it a bounded operator simply by using the same notation.

The theory of unbounded measurable functions requires explicit domains and graph-closedness. A Borel function that is not bounded may therefore define an unbounded operator with a proper domain; the bounded functional calculus alone does not authorize that operation. For now, every operator produced by the bounded Borel calculus acts on all of H and is bounded.

## The theorem assembled

We have constructed bounded Borel functional calculus using simple spectral integrals and uniform approximation. We proved the unit, product, adjoint, positivity, and uniform norm bound. We also proved strong convergence under uniformly bounded pointwise limits by reducing it to dominated convergence for scalar spectral measures.

These properties are exactly what we need to restrict an operator to a measurable spectral region.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For bounded self-adjoint `A` with PVM `E`, bounded Borel `f` gives `f(A) = integral f(lambda) dE(lambda)`, first for simple functions and then by uniform simple approximation. The calculus is a unital star-homomorphism and satisfies `||f(A)|| <= sup |f|`. Uniformly bounded pointwise convergence of symbols implies strong operator convergence by dominated convergence for each scalar spectral measure. Source declarations below use a more general normal operator `a` and symbols on `spectrum C a`; the self-adjoint real-spectrum API pulls back along the real coordinate.

**Lean bridge (verbatim source declaration headers).**

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean` - `borelCalculus`:

```lean
noncomputable def borelCalculus (hf : IsBddMeasurable f) : H →L[ℂ] H :=
```

The bounded operator is constructed through the Riesz vector representing the polarized diagonal integrals, rather than by starting from a PVM.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Multiplicative.lean` - `borelCalculus_mul`:

```lean
theorem borelCalculus_mul (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    borelCalculus ha (hf.mul hg) = borelCalculus ha hf * borelCalculus ha hg :=
```

The normal-operator Borel calculus is multiplicative for bounded measurable symbols.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Multiplicative.lean` - `borelCalculus_conj`:

```lean
theorem borelCalculus_conj (hf : IsBddMeasurable f) :
    borelCalculus ha hf.conj = ContinuousLinearMap.adjoint (borelCalculus ha hf) :=
```

Complex conjugation of the scalar symbol corresponds to the Hilbert-space adjoint.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Multiplicative.lean` - `norm_borelCalculus_apply_le`:

```lean
theorem norm_borelCalculus_apply_le (hf : IsBddMeasurable f) {M : ℝ} (hM : 0 ≤ M)
    (hfb : ∀ x, ‖f x‖ ≤ M) (ξ : H) :
    ‖borelCalculus ha hf ξ‖ ≤ M * ‖ξ‖ :=
```

The source provides the sharp pointwise symbol-bound inequality acting on each vector; it improves the preliminary bound present in the defining construction.

**Scope:** The excerpts are declaration headers, not complete proof bodies. Their enclosing modules supply scalar types, normality/self-adjointness assumptions, and typeclass instances. The prose derives the mathematical statements and does not claim that all of the pedagogical arguments have separate local Lean theorems.
