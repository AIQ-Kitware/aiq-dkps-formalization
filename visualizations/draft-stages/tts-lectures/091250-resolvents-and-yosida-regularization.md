# 091250 — Resolvents and Yosida regularization

**Draft status:** audio-first mathematical lecture. **Recommended background:** `081000` resolvents, `083000` domains and closed graphs, `088000` self-adjoint spectral theorem, `091000` bounded approximations. **Companion:** classical resolvent construction and its relation to symmetric self-adjoint regularization.

<!-- BEGIN SPOKEN LECTURE -->

# Approximating an unbounded operator with its resolvent

The derivative operator on a space of functions, or multiplication by an unbounded real variable, cannot be treated as an ordinary bounded matrix. We can nevertheless replace such an operator by a sequence of bounded operators that preserve important geometric properties. The tool is the resolvent: the inverse of a suitable scalar shift of the operator.

There are two closely related regularizations. The classical Yosida approximant is natural for generators of contraction semigroups. A symmetric version is natural for self-adjoint operators and unitary groups. Their formulas are different, and their common idea is more informative than memorizing either formula.

## The resolvent of a closed operator

Let G be a densely defined closed linear operator on a complex Hilbert space. Its domain is a linear subspace, often proper, while its resolvent at a positive real number lambda is the bounded inverse of lambda times the identity minus G, when this inverse exists on the whole space.

Write R lambda for that inverse. Solving for a vector y means solving the equation lambda y minus G y equals x. The solution y must lie in the domain of G even when the input x does not. Thus the resolvent maps arbitrary vectors into legal domain vectors.

Suppose G is dissipative: the real part of the inner product of G y with y is nonpositive for every domain vector y. Take the real part of the inner product of lambda y minus G y with y. It is at least lambda times the squared norm of y. Cauchy–Schwarz gives lambda times the norm of y at most the norm of lambda y minus G y.

When the shifted operator is onto, this yields a resolvent norm bound of one over lambda. It also proves uniqueness of the solution. Surjectivity is essential: the estimate alone does not establish that the inverse exists everywhere.

## Build the classical approximant

Multiply the resolvent by lambda, and call the result J lambda. It is a bounded contraction. The classical Yosida approximant is lambda times J lambda minus lambda times the identity. Although this operator is bounded, it agrees with G increasingly well on the domain of G as lambda grows.

To see this without a formal power series, take x in the domain of G. Substituting the equation defining the resolvent shows that J lambda x minus x is R lambda applied to G x. Its norm is at most the norm of G x divided by lambda, so J lambda x tends to x.

The same resolvent identity gives G lambda x equals J lambda applied to G x. Since J lambda converges strongly to the identity, G lambda x tends to G x for every x in the domain.

That final qualification is crucial. Each G lambda acts on the whole Hilbert space, but G itself may not. The theorem asserts convergence of the generators on the vectors for which G is defined.

## A diagonal example with a negative generator

Work on square-summable sequences. Let G multiply coordinate n by negative n. Its domain consists of sequences x for which the sequence of n times x n is square summable. It is self-adjoint and dissipative, but unbounded.

The resolvent of lambda minus G multiplies coordinate n by one divided by lambda plus n. Consequently J lambda multiplies that coordinate by lambda divided by lambda plus n. The Yosida approximant multiplies it by negative lambda n divided by lambda plus n.

For each fixed coordinate, this approaches negative n. But the approximating eigenvalues never have magnitude greater than lambda, so the operator is bounded for every fixed lambda. The exact semigroup acts on coordinate n by exponential decay at rate n. The bounded approximants replace arbitrarily fast decay rates by rates capped near lambda.

Choose x n equal to one over n squared. Then x is in the domain because n x n equals one over n, which is square summable. The convergence of G lambda x to G x follows from the same dominated-sum argument as in the general theorem. If x n equals one over n, the original generator is undefined at x, even though every bounded approximant acts there.

## A symmetric construction for self-adjoint operators

Now take a self-adjoint operator A whose spectrum can extend in both positive and negative directions. Its evolution by complex phases should be unitary, not contractive decay. A convenient symmetric regularizer uses the scalar function R squared times s divided by R squared plus s squared.

This function is real, is bounded in magnitude by R divided by two, and approaches s for each fixed real spectral value s. Through the spectral calculus it defines a bounded self-adjoint operator A R. For x in the domain of A, dominated convergence proves that A R x tends to A x.

The connection to resolvents is explicit. Half the sum of the resolvents at positive and negative imaginary R, multiplied by R squared, is exactly this symmetric regularizer. In scalar terms, the two denominators s minus imaginary R and s plus imaginary R add to twice s divided by s squared plus R squared.

These two constructions solve related but different problems. The classical Yosida approximant preserves dissipativity and is adapted to contraction semigroups. The symmetric self-adjoint approximant preserves self-adjointness and is adapted to unitary groups.

## A convergence boundary

Strong convergence on the operator domain does not mean the bounded approximants converge in operator norm. The diagonal example makes the reason plain: no uniform bound on the norms of the approximants can approach an actually unbounded generator. Nor should convergence on an arbitrary vector outside the domain be asserted.

The payoff is precise: resolvents turn a domain-restricted operator into bounded approximations; dissipativity or self-adjointness passes to those approximations in the appropriate construction; and convergence recovers the original action exactly where that action is defined.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and source correspondence (display only)

For a densely defined closed dissipative generator G with range(λI−G)=H and λ>0,

\[
R_\lambda=(\lambda I-G)^{-1},\quad J_\lambda=\lambda R_\lambda,\quad G_\lambda=\lambda(J_\lambda-I)=GJ_\lambda,
\qquad \|R_\lambda\|\le \lambda^{-1}.
\]

On \(D(G)\): \(J_\lambda x-x=R_\lambda Gx\), \(G_\lambda x=J_\lambda Gx\); hence \(J_\lambda x\to x\) and \(G_\lambda x\to Gx\). The uniform estimate first gives strong convergence of J on the dense domain and then extends it to H. For self-adjoint A, the symmetric Yosida approximant is

\[
A_R=\frac{R^2}{2}\bigl((A-iRI)^{-1}+(A+iRI)^{-1}\bigr)
=f_R(A),\qquad f_R(s)=\frac{R^2s}{R^2+s^2}.
\]

**Checked source map.** `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` defines `yosidaApproximantSymSA` from `A.symmetricYosidaApproximation` and `expApprox`. Its provenance notes identify the original symmetric resolvent construction. These declarations cover the self-adjoint/unitary specialization. The general dissipative-generator construction above is classical semigroup theory and is not represented by these source declarations.
