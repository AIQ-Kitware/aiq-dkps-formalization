# 038000 — Partial isometries and polar uniqueness

**Draft status:** audio-first mathematical lecture. **Prerequisites:** Hilbert-space projections, adjoints, isometries, operator modulus, polar decomposition. **Next:** operator exponentials and continuous rotations.

<!-- BEGIN SPOKEN LECTURE -->

# How much of a rotation is determined?

Suppose I take a sheet of paper, draw a short arrow on it, and ask you to move that arrow onto another arrow of the same length. You can decide exactly what happens to that arrow. But have I told you how to move every other direction in the plane? Not necessarily.

A similar ambiguity appears in polar decomposition. Yesterday we constructed the part of a linear map that preserves lengths along the directions that survive. Today we will ask which parts of that construction are forced, which parts are choices, and how the adjoint identifies the initial and final spaces of the motion.

This matters later when we compare spectral subspaces: a canonical motion on the relevant subspace need not specify a unique motion everywhere else.

## An isometry on only part of a space

Recall the definition. A partial isometry is a linear map U that preserves lengths on the orthogonal complement of its kernel, and vanishes on its kernel.

The orthogonal complement of the kernel is called its *initial space*. The range is called its *final space*.

Think of the initial space as the part of the input on which genuine motion takes place. The kernel is not moved elsewhere; it is collapsed to zero. The final space is where the surviving part lands.

If there is no kernel, U is an isometry on the whole input. But it still might not be onto. An isometric embedding of a plane into three-dimensional space is not a unitary equivalence between those spaces.

If U also maps onto the entire output space, then it is a unitary map, or orthogonal in real coordinates.

So these words describe different promises. An isometry promises no change of length. A unitary promises that, and also that every output direction is reached. A partial isometry promises no change of length only on its initial space.

## Use the adjoint to locate the initial space

We can detect these spaces algebraically.

Take an input vector and split it into an initial-space part and a kernel part. U discards the second part and preserves the first part's inner products.

Apply U adjoint after U. On an initial-space vector, this composition returns the original vector. On a kernel vector, it returns zero.

That is precisely the orthogonal projection onto the initial space. In symbols, U adjoint U is that projection.

Likewise, U U adjoint is the orthogonal projection onto the final space. On the final space it acts as the identity, and outside that space it acts as zero.

These are two distinct projections, generally acting on two distinct Hilbert spaces. They tell us where the operator starts and where it lands.

For the real map A sending the vector x comma y to y comma zero, its polar factor U sends x and y to y and zero. Its initial space is the vertical axis. Its final space is the horizontal axis. Consequently U adjoint U projects onto the vertical axis, while U U adjoint projects onto the horizontal axis.

The two products are not equal, but each is a projection. This is a useful warning: a partial isometry need not be normal.

## The uniqueness question

Recall that the polar decomposition of A takes the form A equals U times the modulus of A.

Could some other operator W produce the same factorization?

Of course. The equation only asks W to act on vectors that occur as outputs of the modulus. If a direction never appears as an output of the modulus, the factorization cannot constrain W there.

But we built U with an extra requirement: U is zero on the kernel of A.

I claim that these two conditions uniquely determine U among linear maps: first, U applied after the modulus gives A; second, U kills the kernel of A.

To see why, suppose V satisfies the same two requirements. Every vector in the range of the modulus has the form modulus of A applied to x. On such a vector, both U and V must equal A x. So they agree on the range of the modulus.

They also agree on the kernel, because both vanish there. In finite dimensions the range of the modulus and the kernel are perpendicular complements and together span the entire input space. Therefore U and V agree everywhere.

That is the canonical uniqueness theorem for the polar factor. It does not depend on choosing an orthonormal basis or completing any missing directions.

## A factorization that is not canonical

Now remove the rule about vanishing on the kernel, and ask instead for a full unitary factor in a square-matrix factorization.

Take the two-by-two diagonal matrix whose first diagonal entry is two and whose second diagonal entry is zero. This A is already positive, so its modulus is A itself.

The identity matrix gives a factorization: A is identity times its modulus.

But the reflection that keeps the horizontal axis fixed and reverses the vertical axis gives the same factorization. Why? Because the modulus sends every input into the horizontal axis. The reflection agrees with the identity on that axis. What it does to the vertical axis is never tested.

Both factors are orthogonal maps of the whole plane. Neither is the canonical partial isometry: the canonical factor is the projection onto the horizontal axis, which kills the vertical direction.

There is no contradiction. We are discussing two different optimization criteria for the missing part: either demand zero on the kernel, giving the unique partial isometry, or demand a unitary extension, which may allow choices.

## When can we complete the motion?

For a square matrix in finite dimensions, the kernel and the orthogonal complement of the range have the same dimension. That is a consequence of rank-nullity.

The canonical polar factor already provides an isometry from the complement of the kernel onto the range. Choose any isometry from the kernel onto the complement of the range and combine the two pieces. The result is a full unitary, or orthogonal, map of the whole space.

When the kernel is nonzero, that second piece is a choice. In fact, different choices generally give different unitary completions.

When A is invertible, the kernel is zero. There is no missing piece, so the polar factor is already a unitary map and is uniquely determined. You can also express it as A followed by the inverse of its modulus.

Do not transfer the finite-dimensional completion claim without checking its hypotheses. A rectangular map between spaces of different dimensions does not have a unitary equivalence between the entire spaces. In infinite dimensions, even a square bounded operator can have unequal dimensions of these missing pieces, preventing a unitary completion. The canonical partial isometry still makes sense.

## Why negative signs and symmetry are informative

Take any operator A and negate it. Negation reverses every output direction but leaves every output length unchanged. The modulus of negative A is therefore the same as the modulus of A.

The canonical polar factor, on the other hand, changes sign. On the surviving input directions, it must send the stretched vector to negative A's output. On the kernel it remains zero. Uniqueness then forces the whole canonical factor to be the negative of the original factor.

This illustrates how the two factors divide the work: the modulus remembers stretching, while the polar factor remembers orientation and alignment of surviving directions.

## Looking ahead to direct rotations

When we later construct a direct rotation between subspaces, we will use a related principle: determine a canonical motion on the directions that matter, and identify the freedom or obstruction on complementary directions.

If those directions are silently ignored, one can claim a rotation is uniquely determined when it is not, or claim a transformation is unitary when it only preserves length on a subspace. The mathematical distinction affects theorems about existence, uniqueness, and optimality.

Try reconstructing the argument in reverse. Starting with a partial isometry U, show that U adjoint U projects onto its initial space. Starting with a polar factorization, show why the modulus determines the factor only on the modulus's range. Finally, work through the rank-one diagonal example and exhibit two different full orthogonal factors.

The question is not just whether a factorization exists. It is exactly *which part of the factorization the data determine*.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

For finite-dimensional \(A:E\to F\), the canonical polar factor \(U\) satisfies \(A=U|A|\) and \(\ker U=\ker A\). It is the **unique** linear map meeting those two conditions; equivalently it is the unique partial isometry with that factorization and the canonical kernel. Its support identities are

\[
U^*U=P_{(\ker A)^\perp},\qquad UU^*=P_{\operatorname{ran}A}.
\]

In the square finite-dimensional case, a unitary extension of \(U|_{(\ker A)^\perp}\) exists because \(\dim\ker A=\dim(\operatorname{ran}A)^\perp\). The extension need not equal the canonical partial isometry on \(\ker A\), and need not be unique. For example, with \(A=\operatorname{diag}(2,0)\), both \(W=I\) and \(W=\operatorname{diag}(1,-1)\) satisfy \(A=W|A|\), while the canonical polar factor is \(U=\operatorname{diag}(1,0)\).

**Lean bridge.** In `ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean`, the DKPS-staged development uses the accepted canonical uniqueness API in an exact proof that negation negates the polar factor:

```lean
@[simp]
theorem polarFactor_neg (M : E →L[𝕜] F) : (-M).polarFactor = -M.polarFactor := by
  symm
  apply (-M).eq_polarFactor
```

The subsequent proof establishes the composition condition and vanishing on the kernel. `ContinuousLinearMap.polarFactor` is the canonical operator. The imported `eq_polarFactor` theorem is used to establish equality from the characterizing equations; it is not a statement about arbitrary unitary completions.

The square finite-dimensional completion is separately realized by the exact source declaration in `ForTauCeti/Analysis/InnerProductSpace/Polar/Decomposition.lean`:

```lean
theorem polar_decomposition_choosePolarUnitary (A : E →ₗ[𝕜] E) :
    A = (choosePolarUnitary A : E →ₗ[𝕜] E) ∘ₗ A.operatorAbs := by
```

Note the distinct Lean types: `E →L[𝕜] F` is a bounded map on complete spaces; `E →ₗ[𝕜] E` is a finite-dimensional linear map in this source context; `E ≃ₗᵢ[𝕜] E` denotes a full linear isometric equivalence.

**Reconstruction:** Prove polar-factor uniqueness using \(E=\operatorname{ran}|A|\oplus\ker A\). Explain why the unitary completion is nonunique for \(\operatorname{diag}(2,0)\), and why the completion exists for all square finite matrices but not for every square bounded Hilbert-space operator.
