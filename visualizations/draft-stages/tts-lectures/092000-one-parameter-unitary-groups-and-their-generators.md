# 092000 — One-parameter unitary groups and their generators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `039000` bounded exponentials, `040000` unitary flows, `088000` unbounded spectral calculus, `091000` Yosida approximation. **Next:** `093000` domain-aware Sylvester identities.

<!-- BEGIN SPOKEN LECTURE -->

# A unitary group can exist where its derivative does not

In finite dimensions a self-adjoint matrix A produces a unitary motion by exponentiating imaginary t times A. Every vector has a derivative, because A acts on every vector.

For an unbounded self-adjoint operator, the unitary motion still acts on every vector, but the infinitesimal derivative exists only on a particular dense domain. That difference is the core of Stone's theorem and a major tool for unbounded perturbation theory.

Today we will construct the group, prove strong continuity, identify the generator and its domain, and explain why an operator-norm notion of continuity would be too restrictive.

## The definition of a unitary group

A one-parameter unitary group is a family U of t, indexed by all real times, satisfying three properties.

Each U of t is a unitary operator, so it preserves inner products and has inverse equal to its adjoint. The group law says U of s plus t equals U of s followed by U of t. And U of zero is the identity.

We also require strong continuity: for every fixed vector x, U of t x approaches x as t approaches zero.

Because the operators are unitary, continuity at zero implies continuity at every time. The difference between U of t x and U of s x has the same length as the difference between U of t minus s applied to x and x.

Notice that continuity is imposed after applying the operator to a vector. It does not say that the operator norm of U of t minus the identity approaches zero.

## Building the group from a spectral measure

Let A be self-adjoint. Its spectral theorem defines bounded functions of A. For each real t, the scalar function lambda mapped to the complex exponential of imaginary t times lambda has absolute value one.

Therefore its spectral integral defines a bounded unitary operator U of t. We can call it the exponential of imaginary t A, provided we remember that this notation comes from functional calculus, not from an operator-norm power series in an unbounded A.

The group law follows by multiplying the scalar spectral functions. The product of the exponentials at times s and t is the exponential at time s plus t. The value at time zero is one.

The inverse is the exponential at negative t, and its product with U of t is the identity. Hence every U of t is unitary.

To prove strong continuity, fix x. The squared length of U of t x minus x is the integral of the squared magnitude of the scalar exponential minus one against the finite spectral measure of x.

At each spectral value lambda, the scalar exponential approaches one as t tends to zero. Its difference from one is bounded in magnitude by two. Dominated convergence applies because the scalar spectral measure of x has finite total mass. The integral therefore tends to zero.

No moment condition on x was needed. Strong continuity holds on the entire Hilbert space.

## The derivative selects the operator domain

Now take x in D of A. We can divide the difference U of t x minus x by imaginary t.

At a fixed spectral value lambda, the scalar quotient converges to lambda. Its magnitude is at most the absolute value of lambda, using the elementary inequality that the distance from the complex exponential of imaginary u to one is at most the absolute value of u.

The domain condition for A is exactly the integrability of lambda squared against the spectral measure of x. Dominated convergence thus proves that the difference quotient converges in H to A x.

So every vector in D of A admits the derivative, and its generator value is A x.

For the converse, suppose the difference quotient has a norm limit for some x. Then its norms remain bounded near zero. The squared norm is the integral of the squared magnitude of the scalar quotient.

Fatou's lemma says that the integral of the pointwise limit of these nonnegative functions is at most the limit inferior of their integrals. The pointwise limit is lambda squared. Since the quotient norms were bounded, the second spectral moment is finite.

That proves x belongs to D of A. The derivative-domain equality is exact, rather than merely an inclusion.

This is a strong conclusion: one can recover the domain of an unbounded generator solely from the differentiability of its unitary flow.

## A fast-rotation example

Return to ell two with A acting diagonally by N on the N-th coordinate. The unitary group multiplies that coordinate by the complex exponential of imaginary t times N.

For any fixed square-summable sequence x, the motion is strongly continuous. To check it without integrals, split x into its first finitely many coordinates and a tail. The finite part is continuous in t. The tail stays small, because each coordinate receives a phase of modulus one.

But the group is not continuous in operator norm at zero. Set t equal to pi divided by N and test the N-th basis vector. Its phase is negative one, so the output is the negative of the original vector. Their distance is two.

These times approach zero as N increases. Thus the operator norm of U of t minus identity can remain two at arbitrarily small nonzero times.

This example explains why demanding norm continuity would exclude the most basic unbounded self-adjoint generators.

## The generator and its sign

There are two common sign conventions. One writes U of t as the exponential of imaginary t A. With that choice, the quotient of U of t x minus x by imaginary t converges to A x.

Another convention writes U of t as the exponential of negative imaginary t A and inserts the opposite sign in the generator definition. Both are legitimate. We must keep the definition of the generator synchronized with the exponential used to construct the group.

With the convention U of t equals the exponential of positive i times t A, the generator is recovered using division by i. Reversing the sign in the exponential reverses the corresponding generator convention.

## The converse direction of Stone's theorem

Suppose now that we start with an abstract strongly continuous unitary group, not with a self-adjoint operator. We can define its infinitesimal generator using the vectors for which the appropriate difference quotient converges.

One proves that this operator is symmetric by differentiating the inner-product preservation identity. The harder step is self-adjointness. Symmetry alone would not be sufficient.

The group itself provides the missing resolvents. Consider an exponentially damped integral of U of t over positive times. Its norm is bounded by the integral of the damping exponential. By differentiating suitable orbits and integrating by parts, this integral becomes an inverse for a nonreal shift of the generator. A corresponding integral over negative times supplies the other shift.

Surjectivity at both nonreal shifts is the self-adjointness criterion we met in the domain lecture. It completes the converse and establishes a one-to-one correspondence between self-adjoint generators and strongly continuous unitary groups, once the sign convention is fixed.

## Why the group helps with Sylvester equations

Unitary groups make it possible to compare two self-adjoint operators through bounded, everywhere-defined motions, even when the generators themselves are unbounded.

An expression such as U A of t, followed by a bounded operator C, followed by U B of negative t is always a bounded operator. We can integrate this expression against a suitable scalar kernel to build a candidate solution of a Sylvester equation.

But when we differentiate such an expression to recover A X minus X B, the domains return.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For self-adjoint \(A\), the Borel calculus defines \(U_A(t)=\int e^{it\lambda}\,dE_A(\lambda)\). Then \(U_A(s+t)=U_A(s)U_A(t)\), \(U_A(t)^*=U_A(-t)\), and \(t\mapsto U_A(t)x\) is norm-continuous for every \(x\in H\). Its generator, with the convention \((U_A(t)x-x)/(it)\), is \(A\) on precisely \(D(A)\). The forward derivative-domain implication uses dominated convergence; the converse uses Fatou's lemma. Stone's converse reconstructs a self-adjoint generator from a strongly continuous unitary group, using nonreal resolvents.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` — `expLimit_add`:

```lean
theorem expLimit_add (hA : IsSelfAdjoint A) (s t : ℝ) :
    expLimit hA (s + t) = (expLimit hA s).comp (expLimit hA t) := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` — `continuous_expLimit`:

```lean
theorem continuous_expLimit (hA : IsSelfAdjoint A) (ψ : H) :
    Continuous (fun t : ℝ => expLimit hA t ψ) := by
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` — `genToGroup`:

```lean
noncomputable def genToGroup (hA : IsSelfAdjoint A) : TauCeti.OneParameterUnitaryGroup H where
  U := expLimit hA
  unitary := inner_expLimit hA
  group_law := expLimit_add hA
  identity := by
    rw [expLimit_zero]
    rfl
  strong_continuous := continuous_expLimit hA
```

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/StoneUniqueness.lean` — `generator_genToGroup`:

```lean
theorem generator_genToGroup (hA : IsSelfAdjoint A) :
    TauCeti.OneParameterUnitaryGroup.generator (genToGroup hA) = A := by
```


**Type and hypothesis map.** `expLimit hA t : H →L[ℂ] H` is the bounded limit flow at time `t`. `expLimit_add` provides its composition law, while `continuous_expLimit` has the essential pointwise formulation `Continuous (fun t => ... ψ)`. `genToGroup` packages these facts as a `OneParameterUnitaryGroup` and also records unitarity and identity. Finally, `generator_genToGroup` identifies the partially defined generator with `A`, including domain equality; this is stronger than convergence of derivatives merely for a chosen set of test vectors.

**Scope:** The selected Lean source exposes the approximation limit, strong continuity, its one-parameter unitary group structure, and identification of the generator. The full abstract converse resides in the `OneParameterUnitaryGroup.Stone` import; excerpts below identify the construction/uniqueness path in the supplied snapshot. The operator-norm discontinuity example is an independent calculation in the spoken proof, not a claim about a particular Lean theorem.
