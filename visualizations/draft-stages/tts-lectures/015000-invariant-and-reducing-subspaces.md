# Invariant and reducing subspaces

<!-- BEGIN SPOKEN LECTURE -->

A closed subspace U of a Hilbert space has an orthogonal projection P. An operator A may preserve U, meaning A maps every vector of U back into U. The stronger reducing condition asks for the orthogonal complement to be preserved as well. These conditions control the block structure of A.

Suppose we choose a subspace M of a Hilbert space and apply an operator T to a vector in M. Does the output stay in M, or can it escape into directions perpendicular to M? That question introduces an invariant subspace.

There is a second question that sounds similar but is stronger: can T mix vectors from the perpendicular complement back into M? If the answer is also no, we have a reducing subspace.

These two conditions have different consequences. The distinction will eventually let us describe an operator in blocks, separate spectral pieces, and state exactly what it means for an operator to respect a chosen spectral subspace.

## First, a subspace that stays put

In the ordinary plane, let M be the horizontal axis. Consider the map that sends a vector with coordinates a and b to the vector with coordinates a plus b, and b. In matrix language, its two rows are one, one and zero, one.

Feed it a horizontal vector. Such a vector has second coordinate zero. The output still has second coordinate zero, so it remains horizontal. Therefore M is invariant under T.

But what happens to a vertical vector, one with first coordinate zero? It gets sent to a vector whose coordinates are b and b. That vector has a horizontal part as well as a vertical part. So the vertical axis is not invariant.

This is our first important example: M can be invariant even though its orthogonal complement is not.

Invariance means that T of every vector in M belongs to M. It says nothing about how T acts on vectors outside M. The word invariant describes preservation of a set of directions under the action of a map, not preservation of each vector individually.

For example, a rotation through half a turn leaves the horizontal axis invariant, though it sends most horizontal vectors to their negatives. Invariance of a subspace does not mean that T acts as the identity there.

## Why invariant subspaces let us restrict an operator

If M is invariant, we can regard T as an operator on M alone: take a vector of M, apply T, and regard the output as another vector of M. This is called restricting T to M.

A noninvariant subspace does not allow that construction directly, because some outputs would live outside the proposed codomain.

Take our shear example. On the horizontal axis, T simply leaves vectors unchanged. So the restricted operator is the identity on that one-dimensional space, even though T on the whole plane is not the identity.

This is an important reason to study invariant subspaces. An operator may be complicated on its full space but simple on an invariant part. If we can identify several such parts, we may be able to understand the operator by studying smaller pieces.

However, knowing that M is invariant does not yet say that the whole operator splits into two independent pieces. To see why, we need to look at the perpendicular complement.

## Reducing means no mixing in either direction

Call M reducing for T when both M and M perp are invariant under T.

If we decompose a vector x into its part m in M and its part n in M perp, then T of x is T of m plus T of n. When M reduces T, T of m stays in M and T of n stays in M perp. The two parts evolve independently under the operator.

In our shear example, a vector on the vertical axis gains a horizontal component. The vertical-to-horizontal mixing makes M nonreducing, even though the horizontal axis is invariant.

Compare that with a diagonal matrix that doubles horizontal vectors and triples vertical vectors. Each axis is invariant. The operator is reducing with respect to either axis. The two coordinate directions may stretch differently, but they do not mix.

A reducing decomposition is more than a convenient picture. It is an algebraic way of expressing that the operator has two independent blocks.

## The block-matrix calculation

Let P denote the orthogonal projection onto M, and let Q denote the projection onto M perp. Because every vector splits uniquely into these components, P plus Q is the identity.

Any operator can be decomposed according to where its inputs come from and where its outputs go. There are four pieces. One maps M back into M. One maps M into M perp. One maps M perp into M. And one maps M perp back into M perp.

These are the four blocks of the operator relative to the decomposition M plus M perp.

Now inspect invariance. If M is invariant, there is no flow from M into M perp. The block that sends an M input into M perp must be zero. But the opposite off-diagonal block can remain nonzero, just as in our shear.

If M is reducing, both off-diagonal blocks vanish. Only the two diagonal blocks remain. This is the exact mathematical sense in which the two components evolve independently.

Later, when we say that a perturbation is off-diagonal relative to a spectral subspace, we mean that its diagonal blocks vanish. That is a different condition from reducing: a reducing operator has zero off-diagonal blocks, while an off-diagonal operator has zero diagonal blocks. It is worth keeping those opposite ideas separate.

## The commutation test

There is a remarkably compact way to express reducing. The subspace M reduces T exactly when T commutes with the orthogonal projection P onto M. In symbols read aloud: T after P equals P after T.

Let's prove this in both directions.

First assume M reduces T. Split an arbitrary input x into m plus n, with m in M and n perpendicular to M. If we project first, P keeps m and discards n. Applying T afterward gives T of m.

If we apply T first, we get T of m plus T of n. Because M is reducing, the first term lies in M and the second lies in M perp. Projecting afterward keeps exactly T of m. Both orders give the same output, so P and T commute.

For the converse, suppose P and T commute. Take a vector m in M. Its projection is itself. Therefore projecting T of m gives T of m, which means T of m lies in M.

Next take a vector n in M perp. Its projection is zero. Commutation says the projection of T of n is also zero, so T of n lies in M perp. Both pieces are invariant, and M reduces T.

That proof is useful because it turns a geometric condition involving every vector in two subspaces into one operator identity. It is also why commuting projections will appear repeatedly in the later spectral theory.

## Self-adjoint operators make invariance stronger

We can now derive a consequence of the adjoint we built two lectures ago.

Suppose T is self-adjoint and M is invariant. Take a vector n perpendicular to M, and any vector m in M. We want to know whether T of n remains perpendicular to M.

Consider the inner product of m with T of n. Because T is self-adjoint, we may move T onto m. We get the inner product of T of m with n. But T of m is still in M, by invariance, and n is perpendicular to M. So this inner product is zero.

The argument works for every m in M. Therefore T of n is perpendicular to M. The complement is invariant as well. Thus for a bounded self-adjoint operator, every invariant subspace is reducing.

That theorem explains something structural about self-adjoint operators. They cannot have the one-way mixing exhibited by our shear. In a self-adjoint block matrix, the two off-diagonal blocks are adjoints of each other. If one is zero, the other must be zero too.

Be careful not to overgeneralize. For arbitrary operators, invariance need not imply reduction. Even for an infinite-dimensional unitary operator, one can have an invariant subspace whose complement is not invariant. Self-adjointness made the preceding proof work because we could move T across the inner product without changing it.

## Compression is not the same as restriction

There is one more distinction that becomes essential in Rayleigh–Ritz methods.

Suppose M is a closed subspace but we do not know whether it is invariant. We can still take a vector in M, apply T, and project the output back onto M. This gives an operator on M called the compression of T to M.

It is defined for any bounded operator and any closed subspace. But it may discard a real part of T of the input: the component that leaves M. That is why compression is not generally a restriction.

For the shear example, the horizontal axis is invariant, so its restriction and compression agree. But if we compress the same shear to the vertical axis, the compression keeps only the vertical component. The full operator actually sends vertical vectors partly into the horizontal direction; the compression hides that escape.

If T is self-adjoint, its compression is also self-adjoint on M, whether or not M is invariant. That follows by moving the original operator across the inner product while both test vectors are in M. This will become a foundational fact for the Rayleigh–Ritz method, where approximate eigenvectors live in a trial subspace that need not be invariant.

## From projections to reflections

Remember our reflection through M: it keeps the component in M and reverses the perpendicular component. Reflection is twice P minus the identity.

Because the identity commutes with everything, T commutes with this reflection exactly when it commutes with P. Therefore M reduces T exactly when T commutes with the reflection through M.

This gives us two equivalent pictures of reduction: one using projection, and another using a symmetry that flips the sign of perpendicular directions. That symmetry will be useful in the double-angle theorems, where reflections reveal how off-diagonal pieces behave.

## Reconstruction

Try these three tests without notes. First, use the shear matrix to exhibit a subspace that is invariant but not reducing. Second, prove that a subspace reduces T if and only if its orthogonal projection commutes with T. Third, prove that an invariant subspace of a bounded self-adjoint operator is reducing by moving the operator across an inner product.

They let us describe subspaces through collections of vectors and measure how much of a vector lies in a selected family of directions. Invariance also distinguishes when those selected directions genuinely describe an independent spectral component.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

Let \(M\subseteq H\) be a closed subspace of a Hilbert space and \(P=P_M\) its orthogonal projection. For bounded \(T:H\to H\):
\[
\begin{aligned}
M\text{ invariant} &\iff T(M)\subseteq M,\\
M\text{ reducing} &\iff T(M)\subseteq M\ \text{and}\ T(M^\perp)\subseteq M^\perp,\\
M\text{ reducing} &\iff TP=PT.
\end{aligned}
\]
Relative to \(H=M\oplus M^\perp\), invariance means the lower-left block vanishes; reduction means both off-diagonal blocks vanish. Compression \(PTP|_M\) is always an operator on \(M\); restriction \(T|_M:M\to M\) requires invariance. For self-adjoint bounded \(T\), invariance implies reduction.

**Lean bridge.** The original DKPS staging source `ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean` contains:

```lean
/-- A reducing operator commutes with the corresponding reflection. -/
theorem reflectionOperator_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Submodule.IsReducing U A) :
    U.reflectionOperator ∘L A = A ∘L U.reflectionOperator := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.reflectionOperator (A x) = A (U.reflectionOperator x)
  rw [reflectionOperator_apply, reflectionOperator_apply,
    (show ∀ x, U.starProjection (A x) = A (U.starProjection x) from
      fun x => DFunLike.congr_fun ((Submodule.isReducing_coe_iff_commute_starProjection (U := U)
        (A := A)).mp hU).eq x),
    map_sub, map_smul]
```

`Submodule.IsReducing U A` is the reduction hypothesis, `U.starProjection` the orthogonal projection, and `∘L` composition of bounded linear operators. The proof invokes a native theorem equating reduction to projection commutation, then transports the equality through the reflection formula \(2P-I\). This makes a connection between a geometric condition, an algebraic equation, and the proof assistant's types.

The finite-dimensional source `DavisKahan/FiniteDimensional/Core/OperatorBlocks.lean` also defines the diagonal compression and its complement:

```lean
noncomputable def pinch (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  U.starProjection.toLinearMap ∘ₗ H ∘ₗ U.starProjection.toLinearMap +
    Uᗮ.starProjection.toLinearMap ∘ₗ H ∘ₗ Uᗮ.starProjection.toLinearMap

/-- The off-diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def offDiagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  H - pinch U H
```

Here `→ₗ` is the algebraic linear-map type, whereas `→L` above additionally tracks bounded continuity. The files and exact excerpts were checked against the supplied source snapshot; no new Lean code was compiled. `TauCeti.*` references in these sources do not establish independent upstream authorship; the donor records are tracked separately in the provenance audit.
