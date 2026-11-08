# 035000 — The operator modulus |A|

**Draft status:** audio-first mathematical lecture. **Prerequisites:** adjoints, Gram operators, positivity, finite spectral calculus, positive square roots. **Next:** singular-value decomposition and polar decomposition.

<!-- BEGIN SPOKEN LECTURE -->

# How much does an operator stretch?

A linear map can do several things at once. It can stretch some vectors, shrink others, rotate directions, or send a space into a higher-dimensional one. Sometimes it sends a nonzero vector to zero.

What if we want to separate the information about *length change* from everything else?

For a real number a, its absolute value tells us how much multiplication by a changes length. Multiplying by negative three reverses a direction and triples its length; the absolute value, three, remembers only the length change.

There is an operator construction with the same purpose. It is called the *modulus* of A, written as vertical bars around A. But it is not the matrix obtained by taking the absolute value of each entry.

We will build it from the Gram operator and the positive square root of the positive Gram matrix.

## Start with the length of an output

Let A map one finite-dimensional inner-product space E into another space F. The two spaces do not have to have the same dimension.

Choose a vector x in E. We know that the squared length of A x is the inner product of A x with itself.

By the defining identity of the adjoint, this is also the inner product of x with A adjoint A x. So the squared output length is determined entirely by the source Gram operator, A adjoint A.

That is an important observation. The expression A adjoint A acts on the *input* space E, even though A x lives in the output space F. This lets us measure the stretching without moving into the output space.

The operator A adjoint A is positive semidefinite, since pairing A adjoint A x with x gives the squared norm of A x. So it has a unique positive square root.

**Definition:** the modulus of A is the positive square root of A adjoint A.

It acts on E, not on F. Its square is A adjoint A.

## Why the modulus preserves the output lengths

Call the modulus M for a moment. Since M is positive, it is self-adjoint. And by construction, M squared is A adjoint A.

Now compute the squared length of M x. Using the adjoint identity, this equals the inner product of x with M adjoint M x. But M adjoint is M, so M adjoint M is M squared, which is A adjoint A.

We are back to the squared length of A x.

Thus M x and A x always have the same length. In spoken terms: *the modulus of A stretches every input vector by exactly the same amount as A does.*

This does not mean they produce the same output vector. They may not even live in the same space. A x lies in F, while M x lies in E.

Nor does it mean M and A have the same effect on angles relative to a fixed output coordinate system. The modulus retains the positive, self-adjoint part of the length-change geometry. Later, polar decomposition will describe the remaining isometric motion.

## A two-dimensional example

Let A take the vector with coordinates x and y and output the vector whose first coordinate is x plus y and whose second coordinate is zero.

The matrix of A has first row one, one and second row zero, zero.

What happens to lengths? The output has length equal to the absolute value of x plus y. The input direction with equal coordinates survives and gets stretched. The direction with opposite coordinates disappears completely.

Compute A adjoint A. Because we are using real coordinates, adjoint means transpose. The result is the two-by-two matrix with every entry equal to one.

That Gram operator has eigenvalue two on the equal-coordinate direction and eigenvalue zero on the opposite-coordinate direction.

Its positive square root therefore has eigenvalue square root of two on the first direction and zero on the second. In ordinary coordinates, its matrix has every entry equal to one divided by square root of two.

Check the length identity. Applied to x and y, this modulus produces two equal coordinates, each equal to x plus y divided by square root of two. Their squared lengths add to the square of x plus y. Exactly the same squared length as A's output.

But the modulus produces an output along the diagonal of the input plane. A produces an output along the horizontal axis. The length changes agree; the directions do not.

That is the separation we wanted.

## Three examples that test the definition

First, suppose A is itself a positive operator on E. It is already the unique positive square root of A squared. Because A adjoint equals A, the modulus of A equals A. A positive operator has no sign or orientation change for the modulus to remove.

Second, suppose A is a unitary operator, or more generally an isometric embedding. Every input length is preserved. The defining adjoint identity for an isometry is A adjoint A equals the identity on E. The positive square root of the identity is the identity. Therefore the modulus of any isometry is simply the identity on its input space.

Third, suppose A is self-adjoint but has both positive and negative eigenvalues. Its adjoint equals itself, so A adjoint A equals A squared. On an eigenvector of A with eigenvalue lambda, its modulus acts by the absolute value of lambda.

For instance, a diagonal operator with entries negative three and two has modulus with diagonal entries three and two. Here the operator modulus really does behave like taking absolute values—but it does so on the *eigenvalues*, not on an arbitrary table of matrix entries.

## Kernels and directions that disappear

We can now prove a useful kernel identity.

If A kills x, its output length is zero. The modulus produces an output of exactly the same length, so the modulus also kills x.

Conversely, if the modulus kills x, the output length of A x must also be zero. Thus A kills x.

So A and its modulus have precisely the same kernel.

The kernel marks the input directions that disappear. The orthogonal complement of the kernel consists of directions on which there is no complete collapse. Later, the partial isometry in the polar decomposition will preserve lengths on that orthogonal complement and vanish on the kernel.

Notice that none of this required A to be invertible. The modulus is defined even when A maps a higher-dimensional space into a lower-dimensional one and must therefore have a nontrivial kernel.

## Modulus and the operator norm

Recall that the operator norm of A is the largest output length among inputs of length one.

Because A and its modulus produce equal lengths on every input, their operator norms are equal.

The modulus has an extra advantage: it is positive and self-adjoint, so the finite spectral theorem applies. Its operator norm is its largest eigenvalue.

Consequently, the largest possible stretching factor of A can be found by inspecting the eigenvalues of its modulus.

The complete ordered list of these nonnegative eigenvalues will become the singular values of A. So singular values are not mysterious numbers attached to an arbitrary rectangular matrix. They are the spectral data of an explicitly constructed positive operator that measures length change.

## What we have and what is still missing

We now know how to construct a canonical positive operator that captures the lengths produced by A. We know its square, its kernel, and its largest eigenvalue interpretation.

What we do not yet know is how to match each input stretching direction with its corresponding direction in the output space. That relationship is what singular-value decomposition will provide.

Try to reconstruct the chain before moving on: squared length of A x, then the Gram operator A adjoint A, then the positive square root, then equality of output lengths. Explain why the modulus lives on the source space even for a rectangular map. And check the example where A maps x and y to x plus y and zero.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For finite-dimensional real or complex inner-product spaces \(E,F\) and \(A:E\to F\),

\[
|A|=(A^*A)^{1/2}:E\to E,\qquad |A|^2=A^*A,
\]
\[
\|Ax\|=\||A|x\|,\quad \ker|A|=\ker A,\quad \||A|\|_{\mathrm{op}}=\|A\|_{\mathrm{op}}.
\]

For self-adjoint \(A\), \(|A|\) acts on the \(\lambda\)-eigenspace by \(|\lambda|\). For an isometry \(A\), \(|A|=I_E\).

**Lean bridge.** The bounded Hilbert-space modulus is imported from `TauCeti.Analysis.InnerProductSpace.Modulus` by `ForTauCeti/Analysis/InnerProductSpace/ModulusTransport.lean`. The latter uses the exact defining identity:

```lean
  have hsq : A.modulus * A.modulus = A.adjoint ∘L A := A.modulus_comp_modulus
```

`A.modulus` lives on the source Hilbert space; `A.adjoint ∘L A` is the source Gram operator. The same file proves compatibility with real complexification, extending the coordinate-independent idea to scalar transport:

```lean
@[simp] theorem complexify_modulus (T : E →L[ℝ] E) :
    complexify T.modulus = (complexify T).modulus := by
```

This second statement is a later application of the modulus theory, not a prerequisite for understanding its finite-dimensional definition. The source currently refers to the accepted TauCeti modulus API; its present location is not evidence that the underlying mathematical work originated independently of DKPS.

`ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean` also records the identity relating Gram and modulus invertibility:

```lean
theorem isUnit_modulus_iff (M : E →L[ℂ] F) :
    IsUnit M.modulus ↔ IsUnit (M.adjoint ∘L M) := by
```

The lecture does not require invertibility; the theorem describes a useful additional property under the stated bounded complex-Hilbert-space assumptions.

**Reconstruction:** Prove equality of output lengths and equality of kernels. Compute \(|A|\) for \(A=\begin{pmatrix}1&1\\0&0\end{pmatrix}\). Show that \(|A|=A\) for positive \(A\) and \(|A|=I\) for isometric \(A\).
