# 037000 — Polar decomposition

**Draft status:** audio-first mathematical lecture. **Prerequisites:** adjoints, kernels and orthogonal complements, positive square roots, operator modulus, singular-value decomposition. **Next:** partial-isometry uniqueness and unitary completion.

<!-- BEGIN SPOKEN LECTURE -->

# Separate stretching from motion

Imagine pulling a rubber sheet over a table. You stretch it more in one direction than another, and then turn it. If I tell you only where each point ends up, can you separate the stretching from the motion that carries the stretched sheet to its final position?

For a linear map, this is exactly what polar decomposition does. And we already have most of its ingredients. The modulus of a map tells us its stretching, and the singular-value decomposition tells us which input and output directions correspond. Today we will assemble those ideas into one factorization, and prove why it works even when directions get crushed to zero.

## Review what the modulus knows

Let A be a linear map from one finite-dimensional inner-product space, E, to another, F. The spaces may have different dimensions.

The modulus of A is the positive square root of A adjoint times A. We proved that the modulus and A give the same output length for every input. We also proved that they have the same kernel: a vector is killed by A exactly when it is killed by the modulus.

So the modulus tells us *how much* the map stretches a vector. It does not tell us *where the output points*. We want a second operator, call it U, that restores that missing directional information.

Our goal is to apply the modulus first, then U, and obtain A. In symbols, A equals U composed with the modulus of A.

Why should U preserve lengths? The modulus has already accounted for the length change. All that remains should be a length-preserving transformation wherever there was some nonzero length to preserve.

The qualification at the end is important: where the modulus sends a vector to zero, no output direction remains to be recovered.

## Construct U where its action is determined

Start with a vector of the form modulus of A applied to x. Define U on that vector by declaring that its output is A applied to x.

There are two things to check before this is a legitimate definition. First, could the same vector be written as modulus of A applied to two different inputs? If so, must the proposed output agree?

Suppose the modulus sends x and y to the same vector. Then it kills their difference. The kernels of A and its modulus agree, so A also kills their difference. Thus A x and A y are equal. Good: our proposed U does not depend on which input we chose.

Second, does U preserve length? Yes. We proved in the preceding modulus lecture that the length of A x equals the length of modulus of A applied to x. Therefore the proposed U sends every vector in the range of the modulus to a vector with exactly the same length.

It is also linear. The range of a linear map is a subspace, and the rule respects sums and scalar multiples because A and the modulus are linear.

We have constructed a length-preserving linear map from the range of the modulus into F. It carries that range onto the range of A.

## What happens to the kernel?

Here is the step that makes the construction canonical.

The range of the positive self-adjoint modulus is the orthogonal complement of its kernel, in finite dimensions. And that kernel is the kernel of A. So the input space splits into two perpendicular pieces: the directions that survive, and the directions that A kills.

On the surviving directions, U has already been determined. On the kernel, define U to be zero.

For any input vector, split it into a surviving component and a kernel component. Apply the length-preserving rule to the first, and zero to the second. That gives a linear map U from E to F.

It is not necessarily an isometry on the *whole* input space: a nonzero vector in the kernel still gets sent to zero. Instead, it is an isometry on the orthogonal complement of the kernel, and zero on the kernel. This kind of map is called a *partial isometry*.

Now check the desired factorization. The modulus of x belongs to the surviving subspace. By the definition of U there, U applied to modulus of x is exactly A x. That is polar decomposition.

We have proved it constructively, not just named it.

## A two-dimensional example

Take a map on the real plane that sends the vector with coordinates x and y to the vector with coordinates two y and zero.

It ignores the first coordinate. It doubles the second coordinate and places the result on the horizontal axis.

Its matrix has first row zero, two, and second row zero, zero. The adjoint-times-A matrix is diagonal, with entries zero and four. Its positive square root is diagonal with entries zero and two.

So the modulus leaves the first direction collapsed and doubles the vertical direction. The missing step is to take that stretched vertical direction and lay it along the horizontal axis.

Our polar factor U sends the vector with coordinates x and y to the vector with coordinates y and zero. In matrix language, its first row is zero, one, and its second row is zero, zero.

Check the composition. The modulus sends x and y to zero and two y. U then sends that to two y and zero. This is exactly A.

Notice the zero in U. U does not rotate the whole plane rigidly. It kills the horizontal input direction because that is the kernel of A. On the vertical input line, however, it preserves lengths perfectly.

Its input support and output range can be different subspaces of the same plane.

## Relation to singular-value decomposition

The singular-value decomposition chooses perpendicular input directions, one for each singular value. For a positive singular value, A sends its input direction to the associated output direction, multiplied by that singular value.

The modulus performs the multiplication by the singular value while staying in the input space. U then carries that input direction to its corresponding output direction, without additional stretching.

For a zero singular value, the modulus kills the input direction, and the canonical U kills it too. Thus polar decomposition is what remains of the singular-value decomposition after we stop insisting on choosing complete coordinate bases.

That is a conceptual advantage: the polar factor and modulus are intrinsic to A. The choice of singular vectors within repeated singular-value spaces is not.

## A nonsingular example

Consider a diagonal map that multiplies the first coordinate by negative three and the second by two.

Its modulus multiplies the first coordinate by three and the second by two. Its polar factor reverses the first coordinate and leaves the second alone.

Here U preserves lengths on the whole plane. It is an orthogonal transformation: a reflection. The original operator is a reflection followed by positive stretching.

When A has no kernel, the polar factor is an isometric embedding of its entire input space. If A is an invertible square matrix, that factor is actually unitary—or orthogonal in the real case.

But if A is rectangular, even an injective map need not have an onto unitary factor. It may embed a two-dimensional space in a three-dimensional one.

## Why this matters later

Polar decomposition is not only a way to simplify matrices. It gives us a canonical method for aligning subspaces. When we build direct rotations, we will need to compare coordinate systems without letting arbitrary basis choices dictate the answer.

It also separates two quantities that appear throughout operator theory: the positive operator that records singular values, and the partial isometry that records where surviving vectors go. This separation remains meaningful for bounded operators on Hilbert spaces, although infinite dimensions require closure arguments that we will develop later.

One last reconstruction. Without looking at a formula, explain how to define U on the range of the modulus. Explain why that definition is unambiguous. Explain why it preserves length there. Then explain what happens on the kernel.

If you can give those four arguments, you can recover the polar decomposition on your own. Next we will examine precisely how unique the factor is, and why the word *partial* matters.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For finite-dimensional real or complex inner-product spaces and any linear map \(A:E\to F\), put \(|A|=(A^*A)^{1/2}\). There is a canonical partial isometry \(U:E\to F\) such that

\[
A=U|A|,\qquad \ker U=\ker A,\qquad
U^*U=P_{(\ker A)^\perp},\qquad UU^*=P_{\operatorname{ran}A}.
\]

Construct \(U\) on \(\operatorname{ran}|A|\) via \(U(|A|x)=Ax\), then extend by zero on \(\ker A\). Well-definedness follows from \(\ker |A|=\ker A\), and isometry follows from \(\||A|x\|=\|Ax\|\).

**Lean bridge.** The DKPS-derived source `ForTauCeti/Analysis/InnerProductSpace/Polar/Decomposition.lean` records that `LinearMap.operatorAbs` and `LinearMap.polarFactor` are now supplied by TauCeti, retaining the original DKPS donor history. It also gives a selected **unitary completion for square finite-dimensional maps**, a stronger but less canonical choice:

```lean
noncomputable def choosePolarUnitary (A : E →ₗ[𝕜] E) : E ≃ₗᵢ[𝕜] E :=
  (A.exists_linearIsometryEquiv_eqOn_polarFactor rfl).choose
```

The equation connecting the chosen completion to the modulus is explicit:

```lean
@[simp]
theorem choosePolarUnitary_apply_operatorAbs_apply (A : E →ₗ[𝕜] E) (x : E) :
    choosePolarUnitary A (A.operatorAbs x) = A x := by
```

`operatorAbs` corresponds to \(|A|\). `polarFactor` is the canonical partial isometry. `E ≃ₗᵢ[𝕜] E` is a linear isometric equivalence of the whole space; the selected completion is not the canonical polar factor on the kernel. Its nonuniqueness is the subject of the next lesson.

**Reconstruction:** Build the polar factor for \(A(x,y)=(2y,0)\); calculate both support projections; and verify \(A=U|A|\) directly. Identify exactly where finite-dimensionality enters the range/complement argument.
