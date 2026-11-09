# 123000 — Pinching through an involution

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `060000` pinching and `122000` direct-sum comparison. **Next:** `124000` ambient sine from an ambient perturbation.

<!-- BEGIN SPOKEN LECTURE -->

# Pinching through an involution

Suppose we know the size of an operator K. We insert orthogonal projections on both sides, retain two matching diagonal blocks, and discard the other two blocks. Can the remaining operator be larger than K in a unitarily invariant norm?

Davis and Kahan's Lemma six point two says no. The proof is short, but it is worth deriving carefully because it works for different projections on the input and output sides. Its key device is averaging K with its reflection through a pair of subspaces.

## Start with a two-by-two block matrix

Let the input Hilbert space be decomposed as V plus V perpendicular, and the output as U plus U perpendicular. In these coordinates, K has four rectangular blocks.

The first block maps V into U. The second maps V perpendicular into U. The third maps V into U perpendicular. The fourth maps V perpendicular into U perpendicular.

The pinched operator keeps the first and fourth blocks and replaces the two off-diagonal blocks by zero. In projection notation, it is P U times K times P V, plus P U perpendicular times K times P V perpendicular.

The projections on the two sides need not be equal. This is a two-sided pinching, designed for the cross-block geometry of comparing two different subspaces.

## Construct the reflections

Define J U to equal twice P U minus the identity. This operator acts as positive one on U and negative one on U perpendicular. Likewise define J V using V.

Each J is self-adjoint and unitary. Squaring it gives the identity, since P squared equals P. Thus each J is an involution. Its operator norm is one.

Now compute J U times K times J V in the four-block coordinates. A block whose input and output have the same sign keeps its sign. A block connecting opposite signs changes sign. Therefore the first and fourth blocks are unchanged, while the two off-diagonal blocks are negated.

Add K to J U K J V. The off-diagonal blocks cancel and the two diagonal blocks double. Dividing by two gives precisely the pinched operator.

The identity is exact: the pinching equals one half of K plus J U K J V.

## Prove norm contraction

Let N be any unitarily invariant norm for which K is in the relevant normed class. By the triangle inequality, twice the norm of the pinching is at most the norm of K plus the norm of J U K J V.

Because J U and J V are unitaries, the second norm equals the first. Therefore twice the norm of the pinching is at most twice the norm of K. Divide by two.

We have proved that the pinched operator has norm at most the original operator's norm.

Notice the strength of this argument. It did not inspect individual entries. It did not choose eigenvectors or singular vectors. It did not depend on a dimension count. It used only the reflection identity, unitary invariance, and the triangle inequality.

In a symmetric operator ideal, one must also verify the pinched operator is a member. Both K and J U K J V are members by ideal invariance, so their sum and its scalar multiple are members. This is why the formal source states membership and norm control together.

## Test the result on matrices

Take the two-by-two matrix with every entry equal to one. With U and V both the first coordinate axis, pinching removes the off-diagonal entries, leaving the identity matrix.

The original rank-one matrix has singular values two and zero. The pinched identity has singular values one and one. Its operator norm decreases from two to one, and its Frobenius norm decreases from two to the square root of two. Its nuclear norm stays two.

The example also shows why an individual singular value need not decrease. The second singular value has increased from zero to one. What is contracted is every unitarily invariant norm, or equivalently every Ky Fan prefix and the associated weak-majorization relations—not the singular-value list term by term.

For the first Ky Fan prefix, one is at most two. For the first two, two equals two. Both comparisons hold.

## Distinguish two-sided from one-sided compression

A simple compression P K P also contracts many norms, since the factors have operator norm at most one. But the two-block pinching is not merely a single compression. It keeps two separated pieces, each occupying a different diagonal corner.

Bounding them individually by the norm of K and then using the triangle inequality would give the wasteful estimate twice the norm of K. Reflection averaging recovers the sharp constant one.

This constant is important in the symmetric sine-theta proof. If we lose a factor of two here, the final perturbation estimate will not retain the expected normalization.

## Generalize to rectangular spaces

Nothing essential requires the same underlying Hilbert space on the left and right. Let the domain carry its own orthogonal decomposition and the codomain a different one. Define a sign reflection on each space. The same identity holds: diagonal block selection equals the average of K and its left-right conjugate by the two reflections.

The conjugate is not necessarily an inner conjugation by one unitary because the left and right spaces can be different. It is nonetheless a left unitary times K times a right unitary, and rectangular unitarily invariant norms are invariant under such transformations.

The ambient quadratic-form argument concerns two subspaces of one Hilbert space, while the symmetric-ideal norm comparison also applies to rectangular operators.

## Why does the Ky Fan statement follow?

For each positive integer k, the Ky Fan k norm is the sum of the first k singular values. It is unitarily invariant and obeys the triangle inequality. Applying the reflection-averaging proof at that norm gives a comparison of every finite singular-value prefix.

Consequently the singular-value sequence of the pinched operator is weakly majorized by that of K. This formulation is useful because later proofs can combine it with Lemma six point one's direct-sum comparison before passing to another symmetric gauge.

The two lemmas fit together without changing norm classes. Lemma six point one combines prefix inequalities for orthogonal blocks. Lemma six point two controls the selected pair of perturbation blocks by the original perturbation at every prefix.

## Cross-block geometry in the sine theorem

Suppose P and Q are the projections onto two spectral subspaces. The ambient difference P minus Q can be expressed using cross projections. One term measures vectors in P that land in Q perpendicular. Another measures vectors in P perpendicular that land in Q.

A Sylvester argument gives a norm estimate for each cross term separately. The right-hand sides involve corresponding off-diagonal pieces of the perturbation, which can be placed into two compatible diagonal blocks by choosing their source and target decompositions correctly.

Lemma six point one combines the left-side cross terms. Lemma six point two then pinches the perturbation on the right side and guarantees the resulting pair of perturbation blocks has no greater norm than the original perturbation.

This establishes the bridge from two directed equations to an ambient-angle inequality. Without the lemmas, it is easy to add separate estimates and introduce an extra factor or assume two singular-value lists coincide when they do not.

## The role of self-adjointness

The pinching lemma itself does not require K to be self-adjoint. It is a statement about bounded operators and unitary invariance. Self-adjointness enters elsewhere in the spectral perturbation argument, where it guarantees reducing decompositions, real spectra, and adjoint relations between the off-diagonal blocks.

Keeping those logical dependencies separate helps generalize the lemma. We can use it for arbitrary rectangular maps, even though our immediate application is to self-adjoint perturbations.

## What to remember

The pinching operator is the average of two equally sized operators: K and its reflection-transformed copy. Unitary invariance makes their norms equal, and convexity of the norm makes the average no larger.

This is the entire mechanism of Lemma six point two. Its conclusion is both an ideal-membership statement and a norm bound when ideal norms are used.

That proof will show exactly why the perturbation norm appears without an avoidable factor of two.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `P_U,P_V` be orthogonal projections and `J_U=2P_U-I`, `J_V=2P_V-I`. Define

\[\mathcal P_{U,V}(K)=P_UKP_V+(I-P_U)K(I-P_V)=\tfrac12(K+J_UKJ_V).\]

For every compatible unitarily invariant norm `N`, `N(\mathcal P_{U,V}(K))≤N(K)`. The same argument works in rectangular source/target Hilbert spaces with separate left and right reflections. In an operator ideal the source also proves `Mem K ⇒ Mem(\mathcal P_{U,V}(K))`. Individual singular values need not decrease; only their Ky Fan prefixes are bounded.

### Exact Lean declaration excerpts

`DavisKahan/Sources/DavisKahan1970/SineTheta/ProjectionBlocks.lean` — `diagonalPair` (exact declaration header; proof body omitted):

```lean
def diagonalPair (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) : E →L[𝕜] E :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/ProjectionBlocks.lean` — `two_smul_diagonalPair_eq_add_reflections` (exact declaration header; proof body omitted):

```lean
theorem two_smul_diagonalPair_eq_add_reflections
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    (2 : 𝕜) • diagonalPair U V K =
      K + U.reflectionOperator ∘L K ∘L V.reflectionOperator := by
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/ProjectionBlocks.lean` — `diagonalPair_normingGauge_le` (exact declaration header; proof body omitted):

```lean
theorem diagonalPair_normingGauge_le
    (N : SymmetricNormingFunction)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (diagonalPair U V K) ∧
      N.gauge (diagonalPair U V K) ≤ N.gauge K := by
```

**Mapping.** `diagonalPair` is the two-sided block pinching `P_U K P_V+(I-P_U)K(I-P_V)`. The reflection declaration is the exact algebraic average identity. `diagonalPair_normingGauge_le` includes both membership and the finite gauge inequality under the source `SymmetricNormingFunction` interface.

