# Self-adjoint, normal, and unitary maps

<!-- BEGIN SPOKEN LECTURE -->

For a bounded operator T between Hilbert spaces, its adjoint T star is the unique operator satisfying the inner-product identity: pairing T x with y equals pairing x with T star y. If T sends vectors from one Hilbert space to another, T star sends measuring directions backward. It is defined so that measuring T of x against y gives the same answer as measuring x against T star of y.

Today we will use that construction to distinguish three classes of operators: self-adjoint, normal, and unitary. They all involve the adjoint, but they make different claims. By the end, you should be able to test the claims on a simple matrix, explain why the classes overlap without being identical, and see what each claim gives us geometrically.

## What it means to equal your adjoint

For the moment, let T map a Hilbert space into itself. Its adjoint then has the same source and target, so we can ask whether T and T star are equal.

If they are, T is called self-adjoint. The defining inner-product identity now says that the inner product of T of x with y can be moved to the other side without changing the operator. That is an algebraic form of symmetry.

Consider the real two-by-two matrix that doubles the first coordinate and triples the second. Its transpose is itself, so it is self-adjoint. It stretches the two coordinate directions by different amounts, but it never mixes them.

Here is a slightly less obvious example. Take the real matrix whose first row is two, one and whose second row is one, two. It mixes the coordinates, yet it is symmetric across its diagonal, and is therefore self-adjoint. Self-adjoint does not mean diagonal in the coordinates we happen to have chosen.

For a complex matrix, we take the conjugate transpose rather than merely the transpose. A matrix may look symmetric as an array and still fail to be self-adjoint if complex conjugation changes its entries.

Why should we care about this particular condition? We can already prove something about eigenvalues, even before studying the spectral theorem.

Suppose T of v equals lambda times v, for some nonzero eigenvector v. Take the inner product of v with T of v. Substituting the eigenvalue equation shows that this quantity equals lambda times the squared length of v. But self-adjointness also says that the inner product of v with T of v equals the inner product of T of v with v. One expression has lambda, and the other has the complex conjugate of lambda. Since v has positive squared length, lambda equals its own conjugate. Therefore lambda is real.

This is a first theorem, not simply a definition: every eigenvalue of a self-adjoint operator is real.

We can also see why eigenvectors for distinct eigenvalues are orthogonal. Let v and w be eigenvectors with eigenvalues lambda and mu. Move T between the two slots of their inner product. The result says that lambda times their inner product equals mu times their inner product, because both eigenvalues are real. If lambda differs from mu, their inner product must be zero.

We have not yet shown that a self-adjoint operator has enough eigenvectors to make a basis. That is the subject of the finite spectral theorem later. Today we have established two consequences that any eigenvectors it does possess must satisfy.

## Normality asks for commutation

Now consider a weaker condition. Instead of requiring T to equal T star, ask that T followed by T star give the same operator as T star followed by T. We call T normal when these two compositions agree.

Why does the order matter? Matrix multiplication is not generally commutative. If T first sends a vector somewhere and T star then acts, the outcome can differ from the reversed order.

Normality says that this particular pair of operators commutes. It has a direct interpretation using lengths. The squared length of T of x equals the inner product of x with T star T applied to x. The squared length of T star of x equals the inner product of x with T T star applied to x. Hence a normal operator satisfies: T and its adjoint give outputs of equal length for every input vector.

Conversely, if those lengths agree for every x, the two resulting quadratic forms agree. Their difference is self-adjoint, and polarization tells us that a self-adjoint operator with zero quadratic form is zero. So the length condition also characterizes normality. This is a useful way to remember what the equation means, rather than only remembering the order of its symbols.

Every self-adjoint operator is normal. If T equals T star, the two products in the definition are automatically the same. But not every normal operator is self-adjoint.

Take the quarter-turn rotation in the real plane: it sends the vector with coordinates a and b to the vector with coordinates negative b and a. Its adjoint rotates backward by a quarter turn. A forward turn followed by a backward turn is the identity, and so is the reverse order. It is normal. But the forward rotation is not equal to the backward rotation. It is not self-adjoint.

We can also exhibit a map that is not normal. Send a vector with coordinates a and b to the vector with coordinates b and zero. Its matrix has a one above the diagonal and zero elsewhere. Its adjoint sends a and b to zero and a. If you compose the two maps in opposite orders, one keeps the first coordinate and the other keeps the second. The compositions are not equal, so this operator is not normal.

This example will matter when we later compare diagonalizable matrices, self-adjoint matrices, and matrices that can have nontrivial Jordan blocks. Those distinctions are not just terminology. They constrain how an operator can act.

## Unitary means reversible without changing lengths

Now strengthen the requirement in a different direction. An operator U is unitary when U star U and U U star are both the identity.

The first identity says that U preserves inner products. Move U from one side of an inner product to the other; U star U disappears, leaving the original inner product. In particular U preserves lengths and angles.

The second identity says that U star reverses U everywhere, including on its output space. Thus U is invertible and its inverse is U star.

A quarter-turn rotation is unitary. So are reflections in lines and planes. Over complex coordinates, multiplying a single coordinate by a complex number of absolute value one is also unitary: it changes phase but not length.

Every unitary is normal, because its two adjoint products are both the identity. A unitary need not be self-adjoint, as the quarter-turn shows. A self-adjoint operator need not be unitary, as the doubling map shows. Some operators are both; a reflection is an example. Its inverse equals itself, and therefore its adjoint equals itself.

Notice how different the questions are. Self-adjointness asks whether a map equals the operation that pulls back measurements. Normality asks whether this map commutes with that pullback. Unitarity asks whether the pullback is a two-sided inverse.

## A subtle distinction in infinite dimensions

Here is a warning that will become the main subject. An operator can preserve every vector's length without being onto.

Consider the space of square-summable sequences. Move every coordinate one place to the right, inserting zero at the beginning. The new sequence has exactly the same sum of squared coordinate magnitudes, so its length is unchanged. Yet no input can produce a sequence whose first coordinate is one. The map misses part of the space.

For this right-shift operator, the equation U star U equals the identity holds, but U U star is not the identity. It is the projection that erases the first coordinate. The shift is an isometry, but not a unitary operator.

We have therefore earned the two-sided definition of unitarity. In finite-dimensional spaces of the same dimension, length preservation forces surjectivity. In infinite dimensions, it need not.

## Why these distinctions prepare us for spectral theory

Self-adjoint operators will lead us to real spectra and orthogonal spectral projections. Normal operators will provide a larger class with strong geometric structure. Unitary operators will become our language for exact changes of orthonormal coordinates and rotations of Hilbert space.

When we later say that two operators are unitarily equivalent, we will mean that one is obtained from the other by a reversible change of coordinates that preserves inner products. The geometry is the same even though the displayed matrix may change.

For now, reconstruct three arguments. Why must an eigenvalue of a self-adjoint operator be real? Why does equality of the lengths of T of x and T star of x, for every x, capture normality? And why is the right shift length-preserving but not unitary?


<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

Let \(H\) be a real or complex Hilbert space and \(T\in\mathcal B(H)\). Then
\[
\text{self-adjoint: }T^*=T,\qquad
\text{normal: }T^*T=TT^*,\qquad
\text{unitary: }T^*T=TT^*=I.
\]
A bounded operator is normal exactly when \(\|Tx\|=\|T^*x\|\) for every \(x\). For a self-adjoint operator, any eigenvalue has to be real; eigenvectors for distinct eigenvalues are orthogonal. Finite-dimensional diagonalization is established later, not assumed here.

**Lean bridge.** The snapshot contains this definition and theorem in `ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean`:

```lean
/-- `B` is skew-adjoint: `B⋆ = -B`. -/
def IsSkewAdjointCLM (B : H →L[ℂ] H) : Prop :=
  ContinuousLinearMap.adjoint B = -B

/-- `I • S` is skew-adjoint when `S` is self-adjoint. -/
theorem isSkewAdjointCLM_I_smul {S : H →L[ℂ] H} (hS : IsSelfAdjoint S) :
    IsSkewAdjointCLM (I • S) := by
  have : ContinuousLinearMap.adjoint (I • S) = (starRingEnd ℂ) I • ContinuousLinearMap.adjoint S :=
    ContinuousLinearMap.adjoint.map_smulₛₗ I S
  rw [IsSkewAdjointCLM, this, Complex.conj_I,
    (ContinuousLinearMap.isSelfAdjoint_iff'.mp hS), neg_smul]
```

Here `H →L[ℂ] H` is a bounded complex-linear operator, `ContinuousLinearMap.adjoint` is the adjoint, and `IsSelfAdjoint S` is the self-adjointness assumption. Multiplication by the imaginary unit turns a self-adjoint operator into a **skew**-adjoint one; the complex conjugation in the adjoint explains the sign. The module later studies exponentials of these operators, which we will derive after learning power series and positive operator calculus. The file documents adaptation from a Spectra source, so its lineage should not be recast as an original DKPS result. The excerpt was checked against the supplied source snapshot; no new Lean code was compiled.
