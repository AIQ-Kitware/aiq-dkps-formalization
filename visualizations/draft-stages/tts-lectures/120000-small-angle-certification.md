# 120000 — Small-angle certification

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `118000–119000` branch ambiguity, spectral selection, and repulsion. **Next:** `121000` a comparative theorem decision procedure.

<!-- BEGIN SPOKEN LECTURE -->

# Small-angle certification

Theorem eight point one protects a two-block gap from an off-diagonal perturbation of arbitrary size. But not every perturbation is off-diagonal. A general self-adjoint perturbation can move the diagonal blocks, so the original gap may shrink. How small must such a perturbation be to identify a corresponding subspace and certify an angle below forty-five degrees?

This question leads to Davis and Kahan's Theorem eight point two. The result has two alternative smallness conditions: one on the full perturbation and one on a residual. Both are compared with half of a specified spectral gap. We will explain the geometry of these conditions and the analytic steps by which they select the correct angular branch.

## Identify the spectra precisely

Let A be self-adjoint, and let K be a bounded self-adjoint perturbation. The perturbed operator is S equal to A plus K.

Choose real endpoints beta and alpha with beta at most alpha. Let Q reduce S and have its spectrum in the closed interval from beta to alpha. Suppose the spectrum of S on Q perpendicular lies outside the expanded interval from beta minus delta to alpha plus delta, where delta is positive.

Thus Q is an isolated spectral cluster of S, separated from the remaining spectrum by at least delta on each side that exists. Note that Q is selected for S, the perturbed operator.

Choose P to be a reducing subspace of the unperturbed A, whose spectrum lies in the wider interval from beta minus half delta to alpha plus half delta. This is the trial or reference subspace that we want to compare with Q.

The middle region may contain several eigenvalues or a whole interval of spectrum. The theorem concerns subspaces, not the perturbation of one isolated eigenvector.

For the full angle between P and Q in finite dimensions, assume they have the same rank. In Hilbert space, an appropriate crossed-defect compatibility condition serves the same role for identifying the two directed angles with the ambient angle.

## State the two alternatives

The first smallness alternative is that the operator norm of K is strictly less than delta divided by two.

The second is that a particular residual is smaller than delta divided by two. Form the inclusion of P into the Hilbert space. Compute S applied to that inclusion, then subtract the inclusion followed by the compression of A onto P. Because P reduces A, the compression of A reproduces A on P. Therefore this residual is simply K restricted to P.

This is worth calculating. It means the residual alternative asks only how strongly the perturbation acts on vectors in the reference subspace, rather than on every vector in the Hilbert space. It can be much smaller than the global operator norm of K.

The two alternatives are logically different. A perturbation can act strongly on the orthogonal complement of P while its restriction to P remains small. Theorem eight point two includes a separate argument for that residual-based case.

## What is the conclusion?

Under either smallness alternative and the spectral-placement hypotheses, the theorem certifies that the appropriately directed subspace gap is strictly less than the sine of forty-five degrees, namely the square root of two divided by two.

When the source's dimension or crossed-defect conventions identify the directed and full gaps, this yields the literal full-angle conclusion: every principal angle is strictly below forty-five degrees.

The theorem also carries the corresponding sine-two-theta perturbation and residual estimates. Those inequalities may already have been established under broader hypotheses; the new contribution here is that the smallness condition selects their near-zero branch.

Be careful about the logic. The theorem does not say that the bound on sine twice theta by itself implies theta is below forty-five degrees. It proves the branch by additional spectral and continuation arguments.

## Why half a gap is natural

Suppose a self-adjoint matrix has an eigenvalue in an isolated cluster and another eigenvalue at least delta away. A perturbation of operator norm epsilon shifts any ordered eigenvalue by at most epsilon. If each of two neighboring spectral edges can shift toward the other, a separation of delta has a worst-case remaining width of delta minus twice epsilon.

Hence epsilon smaller than delta over two is the familiar condition ensuring that a middle boundary does not close under a path of perturbations. It is a conservative, easy-to-check sufficient condition.

For a concrete example, let A be diagonal with eigenvalues zero and three. Take beta and alpha both zero, and delta equal three. The desired perturbed cluster Q contains the lower eigenvalue of S, and the other eigenvalue must remain outside the interval from negative three to three as required by the theorem's final spectral-placement hypothesis. If K has norm less than one point five, the path from A to S cannot close the original separation between the two eigenvalue branches.

The endpoint spectral hypotheses still have to be checked. Smallness is not a replacement for the theorem's precise spectral-selection assumptions.

## The path argument and the angle barrier

Consider the path of operators A plus t times K as t runs from zero to one. At time zero the selected spectral subspace agrees with P. If we can exhibit a common separating contour along the path, the spectral projection onto the target cluster depends continuously on t.

The operator resolvent identity supplies a quantitative tool. For complex z outside the spectrum of A plus tK, the difference of resolvents at two nearby times equals their product with the bounded difference in operators. Integrating this resolvent over the separating contour gives a norm estimate for the corresponding spectral projection difference.

But no bound on a single resolvent is enough by itself. We must know that the contour remains in the resolvent set for every time, and that the chosen projection always captures the same cluster. The half-gap condition and the spectral placement are inputs to this continuation construction.

The selected projection starts at P. To reach a principal angle of forty-five degrees, it must cross the barrier at which the directed gap equals the square root of two divided by two. The source's continuation argument certifies that the selected endpoint stays on the near-zero side.

This is the step missing from the naive attempt to divide a sine-two-theta estimate by a doubled cosine.

## Why the residual alternative is harder

Suppose the residual norm on P is small but K itself is large. The direct homotopy A plus tK may have poor spectral-control estimates on the complement of P. We cannot replace the global perturbation norm by its restriction to P in the ordinary resolvent estimate.

Davis and Kahan instead use a self-adjoint completion argument. Informally, we build an auxiliary self-adjoint perturbation that has the same action on P as K but whose global norm is controlled by the residual size. With that replacement, the small-perturbation branch theorem can be applied to a problem that preserves the relevant trial information.

The operator-theory foundation for this step is the Krein self-adjoint completion theorem. It must preserve both the action on the reference subspace and the required self-adjointness. Simply extending an operator by zero on P perpendicular generally fails to be self-adjoint because it loses the matching adjoint off-diagonal block.

This is why the source formalization records a separate residual bridge and its completion obligations. It is substantive analytic work, not a cosmetic change of variable.

## The quantitative meaning of the branch

Once we know theta is below forty-five degrees, the doubled sine can be inverted monotonically. If the sine-two-theta estimate gives sine twice theta at most eta, where eta is below one, then theta is at most half arcsine eta.

That last step has a strict order. First establish the acute branch. Then invert the doubled sine. In particular, eta may be too large for a useful inverse bound, even though a separate branch theorem still asserts theta below forty-five degrees.

Do not confuse the half-gap hypothesis with a universal statement that every sine-two-theta bound has a right-hand side below one. The norms, constants, and range of the estimate must all be examined before applying the inverse sine.

## Directed angles and the standing convention

Here is a second qualification that becomes important in infinite dimensions. The explicitly derived smallness and continuation argument can control the directed gap from P to Q. A full ambient projection difference also measures the opposite directed gap.

In finite dimensions, equal rank identifies the two nonzero directed singular-value lists. For Hilbert spaces, equal infinite cardinal dimensions alone do not establish that identity. The original paper's crossed-defect standing assumption supplies the needed compatibility.

The source records the directed conclusion without imposing a dimension count, and then separately provides full-angle forms under the appropriate convention. We should teach and use exactly the version whose hypotheses are available.

## Final diagnostic

Suppose you are given an approximate invariant subspace and want to declare that its angle from a selected spectral cluster is small. Check four things: the spectral interval and its complement, the residual or perturbation norm, whether the half-gap inequality is strict, and whether your angle is directed or full.

If the hypotheses hold, the theorem certifies the near-zero branch and makes the doubled-angle estimate interpretable as an error bound. If the hypotheses fail, a small doubled sine may still coexist with a nearly perpendicular subspace.

The next lecture will put these results into a theorem-selection procedure. We will decide which gap notion, residual, angle, and norm belong to each perturbation estimate before doing any arithmetic.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `S=A+K`, `A=A*`, `K=K*`, `Q` reduce `S` with `σ(S|Q)⊂[β,α]`, and `σ(S|Qᗮ)` in the exterior of `[β-δ,α+δ]`; let `P` reduce `A` with `σ(A|P)⊂[β-δ/2,α+δ/2]`. The printed alternatives are `‖K‖<δ/2` or `‖R‖<δ/2` for the specifically defined residual of `S` on `P` relative to `A|P`.

The source's `theorem8_2_complex` packages two doubled-sine inequalities and `sourceFullAngleLtC P Q (π/4)`, with finite-dimensional equal-rank assumption. Separate dimension-free statements control the **directed** gap; full-angle descent in arbitrary dimension needs crossed-defect compatibility. The source comments also distinguish direct perturbation continuation from the Krein completion used for residual smallness.

### Exact Lean declaration excerpts

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem82.lean` — `theorem8_2_complex` (exact declaration header; proof body omitted):

```lean
theorem theorem8_2_complex [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Submodule.IsReducing P A)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ ∧
      delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
        2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ ∧
      sourceFullAngleLtC P Q (Real.pi / 4) :=
```

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem82Branch.lean` — `theorem8_2_branch` (exact declaration header; proof body omitted):

```lean
theorem theorem8_2_branch
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Submodule.IsReducing P A)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
```

**Mapping.** `theorem8_2_complex` assumes spectral placement for the selected `Q` and reference `P`, finite-dimensional equal rank, and the **disjunction** of strict half-gap smallness conditions. It returns both doubled-sine inequalities and the full-angle quarter-turn conclusion. The dimension-free `theorem8_2_branch` gives a directed conclusion under its explicit hypotheses; full angle requires a separate bridge.

