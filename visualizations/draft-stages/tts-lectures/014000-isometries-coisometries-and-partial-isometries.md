# Isometries, coisometries, and partial isometries

<!-- BEGIN SPOKEN LECTURE -->

A linear map that preserves every vector length is an isometry, but it need not be onto. Its adjoint describes how the preserved geometry sits inside the target Hilbert space. Related identities distinguish isometries, coisometries, and partial isometries.

There are three names to learn: isometry, coisometry, and partial isometry. We will not just attach names to equations. We will work out what each map does, why the adjoint matters, and how these maps let us transport geometry between spaces of different dimensions.

## A map that keeps lengths

Start in the ordinary plane. Take the map that sends a point with coordinates a and b to the point with coordinates a, b, and zero in three-dimensional space. Nothing about the lengths changes. The vector that used to lie in a plane now lies in a plane inside three-dimensional space.

This map is an isometry: a linear map T for which the length of T of x equals the length of x for every x. Since it is linear, it also preserves distances between any two vectors. The distance between T of x and T of y is the length of T applied to their difference, which is the same as the length of the original difference.

It also preserves inner products. In real spaces, the polarization identity reconstructs the inner product from lengths. In complex spaces, the complex polarization identity does the same job. Therefore length preservation, together with linearity, gives inner-product preservation.

There is a short adjoint test. The inner product of T of x with T of y equals the inner product of x with T star T applied to y. So an isometry satisfies T star T equals the identity. Conversely, that identity forces the inner products, and therefore the lengths, to agree.

Notice what this equation does **not** say. It does not say T T star equals the identity on the output space. Our plane can sit inside three-dimensional space without filling all of it. An isometry is injective, but it need not be surjective.

## Why the two compositions are different

Return to the map that inserts a zero as the third coordinate. Its adjoint takes a three-dimensional vector and discards that third coordinate. If we first insert a zero and then discard the last coordinate, we recover our original plane vector. That is T star T equals the identity.

But suppose we start with a three-dimensional vector that already has a nonzero third coordinate. Discarding it and then inserting zero does not recover the original vector. The operator T T star returns the part of the vector lying in the embedded plane. It is an orthogonal projection, not the identity on all of three-dimensional space.

In finite dimension, the same picture also explains what happens to an isometry from a space to itself. If domain and codomain have the same finite dimension, an injective linear map is surjective. So a square finite-dimensional isometry is automatically unitary.

That statement fails in infinite dimensions. Think of ell two, the space of square-summable sequences. The right shift inserts a zero before every coordinate and moves all the old coordinates one place right. It preserves their squared sum, so it is an isometry. But its image contains only sequences with first coordinate zero. It never reaches the first coordinate direction. The right shift is not unitary.

Its adjoint is the left shift, which discards the first coordinate and moves the rest left. You can check directly that the left shift after the right shift is the identity, while the right shift after the left shift erases the first coordinate.

## A coisometry looks backward

A coisometry is an operator T for which T T star equals the identity on its output space. Equivalently, its adjoint is an isometry. The term is meant to point to the adjoint direction: the map preserves lengths when viewed backward through its adjoint.

Our coordinate-dropping map from three-dimensional space to the plane is a coisometry. It is onto: every plane vector comes from a three-dimensional vector. But it is not injective, because it sends the vertical direction to zero.

This is the mirror image of the original embedding. The embedding was injective but not onto. Its adjoint is onto but not injective.

The left shift on ell two is another coisometry. It can produce any square-summable sequence by inserting an arbitrary first coordinate into a suitable input. But it loses information: different input sequences with different first coordinates lead to the same output.

A unitary operator is both an isometry and a coisometry. That is why its adjoint is a two-sided inverse rather than only a one-sided inverse.

## An operator that is isometric on only part of its input

Now consider a map from the plane to the plane that takes the first coordinate and places it in the second position, while throwing away the original second coordinate. In words, it sends a, b to zero, a.

What does it do to lengths? On the horizontal axis, it preserves length exactly. On the vertical axis, it sends every vector to zero. On a general vector, it neither preserves the whole length nor vanishes.

This is the basic example of a partial isometry. A partial isometry is isometric on the orthogonal complement of its kernel, and zero on its kernel. Recall that the kernel contains the vectors that the operator sends to zero. In our example it is the vertical axis, and its orthogonal complement is the horizontal axis.

Because the domain is a Hilbert space, every vector can be uniquely decomposed into a component in the kernel and a component perpendicular to the kernel. The map discards the first component and transports the second component without changing its length.

The perpendicular part of the kernel is called the *initial space*. The range of the operator is called the *final space*. For a partial isometry, that range is closed. One way to see this is to take a convergent sequence of output vectors. Their unique initial-space preimages are Cauchy, because distances are preserved there. The initial space is closed, so the preimages converge inside it. Their images converge to the desired output, which therefore lies in the range.

Our example carries the horizontal initial space onto the vertical final space. Its adjoint carries the vertical axis back to the horizontal axis.

## The adjoint products become projections

Let P be the orthogonal projection onto the initial space, and Q the projection onto the final space. A partial isometry satisfies T star T equals P and T T star equals Q.

Let's understand the first identity. If x lies in the kernel, both T of x and P of x vanish. If x lies in the initial space, T preserves its inner products with other initial-space vectors. Moving T through the inner product shows that T star T acts as the identity on that space. Thus T star T is exactly the projection that keeps the initial component and erases the kernel component.

The second identity follows in the same way after exchanging T with its adjoint. On the final space, T T star acts as the identity; on its orthogonal complement, it vanishes.

These projection identities also give a convenient test for partial isometries. In particular, if T star T is an orthogonal projection, then T acts isometrically on that projection's range and vanishes on its orthogonal complement. So it is a partial isometry.

Orthogonal projections themselves are partial isometries: they are the identity on the selected subspace and zero on its orthogonal complement. Ordinary isometries are partial isometries whose initial space is the entire input space. Coisometries are partial isometries whose final space is the entire output space.

## One more example: reflection

Take a closed subspace and split any vector into its component inside the subspace and its perpendicular component. Keep the first component and reverse the second. That operation is reflection through the subspace.

Pythagoras shows immediately that reflection preserves length. Reflecting twice returns the original vector. So reflection is a unitary operator, and because it is its own inverse, it is also self-adjoint.

The reflection can be written as twice the orthogonal projection onto the subspace, minus the identity. This formula will be useful when we later compare operators by how they act on a subspace and its complement.

## Where these maps lead

When we develop Gram operators, analysis maps, and synthesis maps, one side of an adjoint composition will measure which directions are preserved or lost. When we construct polar decomposition, partial isometries will separate geometry-preserving transport from stretching. Neither construction should feel like a trick once you understand initial and final spaces.

To reconstruct today's lesson, explain the difference between the two equations T star T equals identity and T T star equals identity. Then show, for the map sending a, b to zero, a, that T star T and T T star are different projections. Finally, explain why an orthogonal projection is a partial isometry even though it usually is not an isometry on the whole space.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

For bounded maps \(T:E\to F\) between Hilbert spaces:
\[
\begin{aligned}
T\text{ is an isometry} &\iff T^*T=I_E,\\
T\text{ is a coisometry} &\iff TT^*=I_F,\\
T\text{ is a partial isometry} &\iff T|_{(\ker T)^\perp}\text{ is an isometry}.
\end{aligned}
\]
For partial isometries, \(T^*T\) is the orthogonal projection onto \((\ker T)^\perp\), and \(TT^*\) onto \(\operatorname{ran}T\). The second is a projection onto a closed range. A reflection across a closed subspace \(M\), with orthogonal projector \(P_M\), is \(J_M=2P_M-I\) and satisfies \(J_M^2=I\).

**Lean bridge.** In `ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean` the reflection operator and its norm-preserving and involutive properties appear as:

```lean
noncomputable def reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.reflection.toLinearIsometry.toContinuousLinearMap
```

```lean
/-- Reflection is involutive. -/
theorem reflectionOperator_involutive (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    U.reflectionOperator ∘L U.reflectionOperator =
      ContinuousLinearMap.id 𝕜 E := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.reflection (U.reflection x) = x
  exact U.reflection_reflection x
```

```lean
/-- Reflection preserves norms. -/
theorem reflectionOperator_norm_map (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    ‖U.reflectionOperator x‖ = ‖x‖ := by
  -- names the application so the norm bound applies to it directly.
  change ‖U.reflection x‖ = ‖x‖
  exact U.reflection.norm_map x
```

The type `E →L[𝕜] E` denotes a bounded linear operator, and `HasOrthogonalProjection` supplies the projection used to define reflection. `toLinearIsometry` records norm preservation in the type of the underlying map. The file's provenance identifies the reflection/block work as DKPS-authored staging mathematics. The `polarFactor` API in `ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean` is a later application, not a prerequisite for this lecture. These excerpts were checked against the uploaded source snapshot; no new Lean code was compiled.
