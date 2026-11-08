# 132000 — Whole-space squared displacement and Q-norms

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `122000–123000`, `130000`, `131000`. **Next:** `133000`.

<!-- BEGIN SPOKEN LECTURE -->

# Whole-space squared displacement and Q-norms

The last two lectures studied how unitary transport moves vectors of a source subspace. Proposition four point three moves to the whole ambient space. It considers a positive operator made by squaring the displacement, and shows that the direct rotation minimizes every unitarily invariant norm of that positive operator. This result is valid, but it is easy to extract a false conclusion from it. We will derive the theorem and identify exactly which unsquared norms inherit its optimality.

## The positive displacement square

Let U and V be two closed subspaces that admit a direct rotation D. Let W be any other unitary satisfying W U equals V. Define the full displacement of W as identity minus W. Its positive displacement square is the adjoint of identity minus W multiplied by identity minus W.

For any vector x, the quadratic form of this positive operator at x is the squared length of x minus W x. It is therefore a natural measure of displacement energy. But our theorem will compare unitarily invariant **norms of the positive operator**, not simply the energy at one chosen vector.

Expand the product. Because W is unitary, the result is two times the identity minus W minus W adjoint. The same formula holds with D in place of W.

The positive square has eigenvalues equal to the squared singular values of identity minus W. This is a Gram-operator identity, and it will be the decisive link to the previous lecture.

## Why one restricted comparison is insufficient

The source-restricted theorem compared identity minus D and identity minus W on U. For the full displacement square we must control behavior on both U and U perpendicular. Those are orthogonal source blocks.

The direct rotation has a compatibility property: interchanging U with U perpendicular and V with V perpendicular gives the same direct rotation. Therefore Proposition four point one can be applied a second time, now to the complementary subspaces.

On U, the restricted displacement of D has singular values no larger than those of W. On U perpendicular, the same comparison holds for the complementary restricted maps. Squaring these values preserves the pointwise inequalities because the singular values are nonnegative.

That gives the spectral data of two diagonal blocks of the displacement square, but it does not immediately compare the entire positive operators. The competitor can have nonzero off-diagonal blocks coupling U and U perpendicular. We need to handle them without losing constants.

## Combine the squared singular values

First recall how Ky Fan sums work for a block diagonal operator. The k largest singular values of a direct sum are obtained by merging the two individual sorted lists. Thus its Ky Fan k sum is the maximum of all possible splits: take i values from the first block and k minus i from the second.

Since the direct restricted squared singular values are bounded term by term on each source block, their merged k-prefix is bounded by the merged k-prefix of the competitor's restricted squared singular values. This is exactly the direct-sum norm comparison from our earlier block-operator lectures.

Now let G be the full displacement square of W. Its diagonal blocks relative to U plus U perpendicular are the two Gram operators of the restricted displacements. The off-diagonal blocks are not generally zero.

Erase them by pinching G with respect to that decomposition. Pinching is the average of G and its conjugate by the reflection that is plus one on U and minus one on U perpendicular. A convex unitarily invariant norm cannot increase under that average. At the Ky Fan level, every prefix of the pinched operator is no greater than the corresponding prefix of G.

For the direct rotation, the displacement square is already block diagonal. Indeed, it equals two times identity minus D minus D adjoint, and the positive cosine part D plus D adjoint commutes with the source projection. Consequently pinching does not change the direct operator.

Putting these facts together gives, for every k, the Ky Fan k norm of the direct displacement square no greater than that of the competitor's displacement square. From Ky Fan dominance, every unitarily invariant norm has the same inequality.

## A warning about individual eigenvalues

The conclusion concerns cumulative prefixes, not every individual eigenvalue. A pinched positive matrix may have a smaller total of its largest k eigenvalues while some lower eigenvalue increases. We already saw this phenomenon in our pinching lecture.

In fact the direct rotation's squared displacement need not have every singular value below the corresponding competitor's value. A four-dimensional example with two equal principal angles has four equal positive eigenvalues for the direct square, while a competing rotation has two large eigenvalues and two zeros. The lower individual eigenvalues favor the competitor, even though every Ky Fan prefix sum favors the direct rotation.

If we replaced the prefix statement with an individual-eigenvalue statement, we would be claiming something stronger than Proposition four point three, and it would be false.

## Which unsquared norms follow?

Suppose we are interested in a norm of identity minus W itself. Can we take square roots of the squared-displacement inequality?

For the operator norm, yes. The norm of X adjoint X equals the square of the norm of X. Therefore minimizing the operator norm of the positive square also minimizes the operator norm of X.

For the Frobenius or Hilbert–Schmidt norm, also yes. The trace norm of X adjoint X equals the square of the Hilbert–Schmidt norm of X. Because Proposition four point three applies to the trace norm of the positive square, it gives the Frobenius comparison for unsquared displacement.

The same pattern extends to Schatten p norms with p at least two. The square of the Schatten p norm of X is the Schatten p over two norm of X adjoint X, and p over two is then at least one, so it is a genuine unitarily invariant norm. These norms belong to a class called Q-norms.

A Q-norm N is a unitarily invariant norm for which there exists another unitarily invariant norm M satisfying N of X squared equals M of X adjoint X, for every X. Once that property is established, Proposition four point three immediately gives optimality of the full displacement for N.

The trace norm of X does not satisfy this pattern. Squaring the sum of singular values introduces cross terms, while the trace of X adjoint X sums squares. There is no generally valid unitarily invariant norm of X adjoint X whose value equals the square of the trace norm of X. The source's compiled counterexample certifies that the trace norm is not a Q-norm.

## A plane example and the boundary of the result

Take two real lines meeting at angle theta. The direct rotation through theta has displacement singular values equal to two sine theta over two, repeated twice. A reflecting transporter can have displacement singular values two and zero.

Under the operator norm, the direct rotation wins because its largest chord is at most square root of two for principal theta at most a right angle. Under the Frobenius norm, its two squared chords sum to a value at most four, tying the reflection at a right angle. Under the trace norm, however, the direct rotation costs four sine theta over two, while the reflection costs two. Above sixty degrees, the reflection wins.

This example shows that even without mixing principal planes, the unsquared trace-norm optimization can differ from the squared one. In the next two lectures we will see a four-dimensional failure at angles much smaller than sixty degrees.

## Close

The proof of Proposition four point three consists of squared restricted singular-value bounds, a Ky Fan direct-sum argument, and a pinching contraction. Those operations control all unitarily invariant norms of the positive displacement square. They also control full displacement in Q-norms, including operator, Frobenius, and Schatten p norms for p at least two.

They do **not** control arbitrary unitarily invariant norms of identity minus W. That missing implication is the subject of Proposition four point four as printed. We will treat it as a mathematical claim to test rather than a conclusion to inherit automatically.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Define \(G_W=(I-W)^*(I-W)=2I-W-W^*\). Proposition 4.3 gives
\[
 \sum_{j=1}^k s_j(G_D)\le \sum_{j=1}^k s_j(G_W)\quad(k\ge1),
\]
not pointwise domination of each \(s_j\). The proof uses restricted displacement on \(U\) and \(U^\perp\), squaring through \(s_j(X^*X)=s_j(X)^2\), block-sum Ky Fan comparison, and pinching.

A Q-norm \(N\) has \(N(X)^2=M(X^*X)\) for some unitarily invariant norm \(M\). Schatten \(p\) for \(2\le p\le\infty\) satisfy this with \(M=S_{p/2}\). The source also proves full-displacement operator- and Hilbert–Schmidt-norm consequences in infinite-dimensional matched-defect scope.

## Exact Lean declaration excerpts

**`proposition4_3_squaredDisplacement_kyFan`.** A `ℂ`-Hilbert-space result comparing **every Ky Fan prefix** of positive squared displacement, which is the valid root of the invariant-norm statement.

`DavisKahan/Geometry/Polar/DisplacementSquareExtremal.lean` — `proposition4_3_squaredDisplacement_kyFan` (exact declaration header; proof body omitted):

```lean
theorem proposition4_3_squaredDisplacement_kyFan (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) (k : ℕ) :
    (((1 - star (spectraDirectRotation U V hacute)) *
          (1 - spectraDirectRotation U V hacute)).kyFanGauge k : ℝ) ≤
      (((1 - star W) * (1 - W)).kyFanGauge k : ℝ) :=
```

**`IsQNorm`.** This predicate formalizes the additional norm property `N(A)^2 = M(A⋆A)` with `M` itself unitarily invariant.

`DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean` — `IsQNorm` (exact declaration header; proof body omitted):

```lean
def IsQNorm (N : UnitarilyInvariantSeminorm 𝕜 E E) : Prop :=
```

**`directRotation_fullDisplacement_qnorm`.** `hN : IsQNorm N` is essential. The theorem allows any acute pair and any admissible isometric competitor; it does not impose the printed angle threshold.

`DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean` — `directRotation_fullDisplacement_qnorm` (exact declaration header; proof body omitted):

```lean
theorem directRotation_fullDisplacement_qnorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E) (hN : IsQNorm N)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : Submodule.IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) :=
```

**`Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_hilbertSchmidt`.** The infinite-dimensional Hilbert–Schmidt consequence is an extended-real comparison at matched-defect scope, not a claim of arbitrary unsquared invariant-norm optimality.

`DavisKahan/Sources/DavisKahan1970/Section4.lean` — `Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_hilbertSchmidt` (exact declaration header; proof body omitted):

```lean
theorem Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_hilbertSchmidt
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ((OperatorIdealFamily.hilbertSchmidt ℂ).gauge (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
      ((OperatorIdealFamily.hilbertSchmidt ℂ).gauge (1 - W)) :=
```

