# 124000 — Ambient sine from an ambient perturbation

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `110000`, `122000`, `123000`. **Next:** `125000`, non-isometric frames and unequal dimensions.

<!-- BEGIN SPOKEN LECTURE -->

# Ambient sine from an ambient perturbation

In our first sine-theta theorem, we began with a trial subspace and measured a residual. The result controlled the angle in one direction. Proposition six point one of Davis and Kahan asks for something stronger and structurally different. Suppose two self-adjoint operators differ by a perturbation, and we have chosen one reducing subspace of each operator. Can we control the entire ambient difference between those two subspaces by the perturbation itself?

The answer is yes, under spectral separation in both crossed directions. We will derive the two Sylvester equations, combine their singular values, and see exactly why the pinching lemma is needed to recover a constant of one.

## Set up the four spectral blocks

Let A and B be bounded self-adjoint operators on one Hilbert space. Write K for B minus A. Let U reduce A, and let V reduce B. Denote their orthogonal projections by P and Q.

Because U reduces A, the operator A has no blocks connecting U to its orthogonal complement. Likewise B has no blocks connecting V to its complement. But the decompositions need not agree. Their relative orientation is the geometry we want to measure.

Form X by projecting first onto U and then onto V perpendicular. It maps vectors of U into V perpendicular. Its operator norm is the maximal sine of a directed angle from U toward V. Form Y by projecting first onto U perpendicular and then onto V. It maps vectors of V into U perpendicular and measures the reverse direction.

These two directed maps can have different singular-value lists if the dimensions differ. We must retain both of them.

## Derive the first Sylvester equation

Take a vector u in U. Since A preserves U, applying the compression of A on U and then X gives the V-perpendicular component of A u. Since B preserves V perpendicular, applying the compression of B there to X u gives the V-perpendicular component of B u.

Subtract these two expressions. The result is the V-perpendicular component of B u minus A u. But B minus A equals K. Thus the first Sylvester equation has unknown X, coefficients B on V perpendicular and A on U, and right-hand side the block of K from U into V perpendicular.

Suppose the spectrum of A restricted to U is separated from that of B restricted to V perpendicular by a gap delta in the interval-versus-exterior sense. The appropriate Sylvester estimate gives delta times every Ky Fan prefix of X at most the corresponding prefix of that perturbation block.

This is a directed sine estimate, but only one of the two we need.

## Derive the complementary equation

Now reverse the roles of the selected spaces and their complements. Form X prime, the map that projects from U perpendicular into V. This is the adjoint of Y, so X prime and Y have the same singular values.

Because A preserves U perpendicular and B preserves V, a second calculation gives B restricted to V times X prime, minus X prime times A restricted to U perpendicular, equals the block of K from U perpendicular into V.

This requires another gap hypothesis: the selected spectrum of B on V must be separated from the spectrum of A on U perpendicular. The first gap does not automatically imply the second. Proposition six point one assumes both.

Apply the Sylvester inequality again. We obtain a Ky Fan bound on X prime using the second complementary block of K.

## Reassemble the ambient sine

We have two rectangular maps and two inequalities. How do they describe a single operator on the ambient Hilbert space?

Consider the square of P minus Q. Expand the product, remembering that P squared is P and Q squared is Q. The expression is P plus Q minus P Q minus Q P.

Now inspect it using the decomposition U plus U perpendicular. Its off-diagonal blocks vanish. Its U-to-U block is P times one minus Q times P, exactly X adjoint X. Its U-perpendicular block is one minus P times Q times one minus P, exactly Y Y adjoint.

Therefore the positive square root of this square has singular values obtained by combining the singular values of X and Y. This positive operator is the absolute value of P minus Q. It is the ambient sine-angle operator.

There is no dimension-matching assumption in this identity. If U contains a direction perpendicular to all of V, its sine is one. If the reverse defect exists instead, that also appears. The ambient construction records both.

## Combine the two inequalities without losing a constant

We want to combine every Ky Fan prefix of X and X prime. The direct-sum comparison from the previous lecture tells us how: if each block's singular-value prefixes are dominated by those of a corresponding perturbation block, their orthogonal direct sum inherits the domination.

The two perturbation blocks have orthogonal input supports, U and U perpendicular, and orthogonal output supports, V perpendicular and V. They can therefore be placed together as a single block-diagonal operator, up to exchanging the order of the target blocks.

This combined operator is the two-sided pinching of K that keeps precisely those two blocks. The reflection-averaging identity from Lemma six point two proves its norm, in every unitarily invariant gauge, is no greater than the norm of K.

Combining the Sylvester comparisons, direct-sum comparison, and pinching, we obtain delta times the ambient sine norm at most the norm of B minus A.

Notice what did not work. Adding two scalar operator-norm bounds directly would have yielded a factor of two. Nor could we assume the two directed lists were identical. The block methods preserve the exact multiplicities and the constant.

## Check equality in a two-dimensional example

Let A be diagonal with eigenvalues zero and four. Choose U as its zero-eigenspace, the horizontal axis. Rotate both eigenvectors by an angle theta, and let B be the rotation of A by that change of orthonormal basis. Its zero-eigenspace V is the rotated horizontal line.

Both crossed spectral gaps equal four: each zero block is separated from the opposite four block.

The operator norm of the difference of the two rank-one projections is sine theta. The operator norm of B minus A is four times sine theta. So delta times the ambient sine norm equals the perturbation norm exactly.

In Frobenius norm, each projection difference has two nonzero singular values equal to sine theta. Its Frobenius norm is the square root of two times sine theta. The perturbation difference similarly has two singular values four sine theta. Equality holds again.

This is a sharpness witness, not just an illustration. We cannot improve the universal constant below one in these norm classes.

## Why an arbitrary residual does not suffice

If we start only with a trial residual for U, we control the map from U into V perpendicular. We do not know what happens to a direction in V that lies in U perpendicular. For example, if U is a one-dimensional line inside a two-dimensional V, the directed escape of U from V is zero. Yet P minus Q has norm one because V contains a direction missing from U.

Proposition six point one avoids this defect by assuming two operators, two reducing subspaces, and two crossed spectral gaps. These hypotheses generate both directed equations and give access to the same ambient perturbation K on the right.

This is the precise difference between an ambient perturbation theorem and an arbitrary trial-residual theorem.

## The role of operator ideals

In an infinite-dimensional Hilbert space, a symmetric norm may be finite only for operators in a particular ideal. The statement must therefore establish two things: membership of the ambient sine operator when K belongs to the ideal, and the numerical inequality for its ideal norm.

The all-prefix Ky Fan comparisons establish weak majorization. For a supported symmetric ideal with the required dominance property, weak majorization transfers both membership and the norm bound. The source formalization keeps these obligations explicit.

The original paper states its theorem in a separable ambient Hilbert space and uses interval-versus-exterior crossed gaps. Stronger modern interfaces sometimes accept a more abstract Sylvester-gap certificate. When we present the original proposition, the printed spectral conditions matter.

## Close

The entire proof has four stages. Build two crossed Sylvester equations. Estimate both directed escape maps. Recognize the ambient sine as their combined singular-value list. Finally, pinch the common perturbation K to control both right-hand sides by a single norm.

Next we will return to a trial space that may not have orthonormal coordinates and may have a different dimension from the exact subspace. That situation admits a directed sine bound, but it must carry a lower-frame factor.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)


Let \(K=B-A\), \(P=P_U\), \(Q=P_V\), and
\[X=P_{V^\perp}P_U,\qquad X'=P_VP_{U^\perp}.\]
The cross-block Sylvester equations are
\[
 B_{V^\perp}X-XA_U=P_{V^\perp}KP_U,\qquad
 B_VX'-X'A_{U^\perp}=P_VKP_{U^\perp}.
\]
The ambient squared difference decomposes as
\[(P-Q)^2=\bigl(X^*X\bigr)|_U\oplus\bigl((X')^*X'\bigr)|_{U^\perp}.\]
Both crossed **interval/exterior** gaps are required in the paper-facing statement. The conclusion is ideal membership plus \(\delta N(\sin\Theta)\le N(K)\), not merely an operator-norm inequality.


### Exact Lean declaration excerpts


`DavisKahan/Sources/DavisKahan1970/Proposition61.lean` — `proposition6_1_complex` (exact declaration header; proof body omitted):

```lean
theorem proposition6_1_complex
    (N : SymmetricNormingFunction)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock A U hU)
      (PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock B V hV)
      (PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (cfc Real.sin (Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (Angle.angleOperator U V)) ≤ N.gauge (B - A) := by
```


`DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean` — `proposition6_1_printedGap_sourceExact_complex` (exact declaration header; proof body omitted):

```lean
theorem proposition6_1_printedGap_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B)
    {δ : ℝ} (hδ : 0 < δ)
    {β α β' α' : ℝ} (hβα : β ≤ α) (hβα' : β' ≤ α')
    (hgapUV : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) β α δ)
    (hgapVU : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) β' α' δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (cfc Real.sin (DavisKahan.Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (DavisKahan.Angle.angleOperator U V)) ≤ N.gauge (B - A) :=
```



**Mapping.** `hU` and `hV` certify reducing subspaces; `hgapUV` and `hgapVU` are two distinct cross-gap proofs. `SymmetricNormingFunction` and `NormalizedUnitaryInvariantNorm` encode the class of norms. `N.Mem` is a necessary premise/conclusion in Hilbert space. The exact source façade in `Section6SourceScope.lean` additionally requires ambient separability and the printed interval/exterior placement.

