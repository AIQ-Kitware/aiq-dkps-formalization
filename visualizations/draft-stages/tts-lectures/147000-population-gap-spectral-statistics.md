# 147000 — Population-gap spectral statistics

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `027000–031000`, `107000–110000`, `146000`. **Next:** `148000`.

<!-- BEGIN SPOKEN LECTURE -->

# Population-gap spectral statistics

A central statistical task is to estimate an eigenspace from a noisy covariance or similarity matrix. There is a population matrix, which describes the mathematical target, and a sample matrix computed from observations. The sample eigenvectors fluctuate, but the target eigenspace may still be estimable. Today we will connect the Davis–Kahan framework to the population-gap perturbation bounds developed by Yu, Wang, and Samworth, and explain why their formulation is useful for statistical arguments.

## Two matrices with different roles

Let Sigma be a real symmetric p-by-p population matrix, with eigenvalues sorted from largest to smallest. Let Sigma hat be a sample estimate of Sigma. Their difference, call it E, is the estimation error.

Choose consecutive population eigenvectors, indexed from r through s, and collect them as an orthonormal frame V. The selected block has dimension d, equal to s minus r plus one. Collect the sample eigenvectors with the same ordered indices into V hat.

We want to bound the principal angles between the spans of V and V hat. If these spaces coincide, the sine distance is zero, even if an eigensolver returns different bases inside a repeated population eigenspace. If they differ, the Frobenius norm of the principal sine list measures total subspace leakage.

There is a statistical asymmetry here. The population matrix describes the target and usually has an assumed spectral gap. The sample matrix is random, and its eigenvalue spacings are themselves random. A theorem that assumes a positive sample gap may be awkward to apply, because verifying that gap is another probabilistic event.

The population-gap approach avoids making a sample eigenvalue gap into an independent hypothesis.

## Define the gap carefully

For a selected population block, compare its upper endpoint to the preceding population eigenvalue and its lower endpoint to the following population eigenvalue. The population boundary gap Delta is the smaller positive separation, ignoring a boundary that lies outside the ambient index range.

For the largest d eigenvalues, there is only a lower boundary. If the dth eigenvalue is separated from the next one by g, Delta is g. For an interior block, both boundaries matter. No separation among eigenvalues *inside* the selected block is required; repeated eigenvalues inside it are permitted.

This matters for principal component analysis. We often care about the entire leading d-dimensional subspace, not the orientation of individual principal components inside a nearly repeated cluster.

If Delta is zero, a small perturbation may cause a large change in which ordered eigenvectors are included in the selected block. A nonzero gap is the mechanism that identifies the target subspace.

## The population-only sine bound

Yu, Wang, and Samworth's symmetric block theorem, as formalized in the repository, gives a Frobenius sine bound involving the population gap alone. In spoken form, it says this: the sine distance is at most twice the smaller of square root of d times the operator norm of the estimation error and the Frobenius norm of that error, divided by Delta.

The factor of two is part of this source-facing theorem. The selected sample frame is identified by ordered eigenvalue indices, but the theorem does not ask us to separately provide a gap between sample eigenvalues. The perturbation may be large enough to make the bound numerically uninformative, yet the inequality remains valid under its stated finite-dimensional hypotheses.

Why are there two numerator options? Since the sine distance is a Frobenius norm of a d-column leakage map, a uniform operator-norm estimate can be multiplied by square root of d. Alternatively, if the full estimation error is well controlled in Frobenius norm, we can use that directly. Taking the smaller exploits whichever norm estimate is sharper in the application.

In high-dimensional statistics, these choices can behave differently. A low-rank estimation error may have a small Frobenius norm relative to a crude dimension-scaled operator bound. A dense error can behave the other way.

## A two-by-two check

Take a population matrix with eigenvalues four and one, and choose its leading eigenvector as the target. The population gap is three. Rotate its eigenbasis by an angle theta without changing the eigenvalues, producing Sigma hat. The sample leading eigenvector rotates by theta, so the principal sine is the absolute value of sine theta.

The perturbation matrix Sigma hat minus Sigma has operator norm three times the absolute value of sine theta. That follows from the same two-by-two projection-difference computation we used for operator functional calculus.

Our population-gap theorem, with selected dimension one, gives a bound of two times the absolute value of sine theta. The actual error is one times that value. The inequality is correct, though it does not claim the sharp constant for this example.

This is a useful reminder. An estimate designed to avoid assumptions on a random sample gap may trade some sharpness for simpler hypotheses. We must compare the theorem against its intended use, not only against the best two-level equality case.

## What if the sample eigenvalues cross?

Suppose estimation error is large enough that two sample eigenvalues exchange their order relative to the population eigenvalues. Then the sample frame defined by sorted index can correspond to a very different direction. The sine distance can approach its maximal value.

The theorem has not failed. The perturbation norm must be at least comparable to the population separation for such an exchange, and the right-hand side can then exceed one. The inequality becomes vacuous exactly where the data no longer determine a stable ordered block.

For small estimation error relative to Delta, the bound becomes informative and yields a consistency statement if the error-to-gap ratio tends to zero. The theorem itself is deterministic. A statistical analysis supplies a separate concentration bound for the random matrix E. Combining the two gives a probabilistic subspace-error guarantee.

This separation of tasks is conceptually clean: matrix perturbation theory controls geometry conditional on an error size, and probability theory controls the error size generated by sampling.

## Aligning estimated eigenvectors

Statistical work often reports an estimated matrix of eigenvectors rather than only a subspace. But even with zero estimation error, eigenvectors in a repeated block can be rotated orthogonally without changing the population matrix. So comparing V hat directly with V is generally ill-posed.

The appropriate comparison chooses an orthogonal d-by-d matrix O that best aligns the sample frame to the population frame. The Procrustes construction uses the singular value decomposition of their cross-Gram matrix. We studied that geometry in the earlier lectures.

For orthonormal frames with principal angles theta one through theta d, the optimal squared Frobenius frame discrepancy is twice the sum over j of one minus cosine theta j. The squared Frobenius sine distance is the sum of sine squared theta j. Their ratio is controlled because twice one minus cosine theta equals two sine squared theta divided by one plus cosine theta. Since cosine theta lies between zero and one, that quantity is between sine squared theta and twice sine squared theta.

Therefore the optimal aligned-frame Frobenius error is at most square root of two times the Frobenius sine distance. Combining this geometric fact with the population-gap sine bound gives the source's factor two times square root of two in the aligned-frame estimate.

This alignment step is essential when spectral embeddings feed a downstream model. If a basis changes by a harmless orthogonal rotation, comparing its raw columns can report a large error even when the represented subspace has not changed at all.

## Population gaps versus mixed gaps

There are versions of Davis–Kahan bounds that refer to a separation between a population cluster and sample eigenvalues outside the cluster. Such a mixed gap can be harder to verify, and its value depends on the random sample. The Yu–Wang–Samworth population-gap theorem replaces it with a gap stated entirely using the population matrix.

This does not mean the sample spectrum is irrelevant. The proof relies on ordered eigenvalue comparisons and variational inequalities to control how sample eigenvectors can move. It means the final theorem does not ask the user to assume or estimate a separate sample spectral gap.

There are also source-accuracy details. The repository's grounding audit identifies a missing square in one polynomial identity printed in the Yu–Wang–Samworth paper and exhibits a counterexample to that printed formula. The corrected identity is what the formal theorem proves. Separately, the rectangular extension requires the corrected ambient rank-boundary convention discussed in the previous lecture. Such distinctions are part of a faithful course: a paper's useful main insight should not oblige us to repeat a defective intermediate formula.

## What the Lean endpoint captures

The symmetric source-facing theorem has explicit real finite-dimensional matrices, symmetricness assumptions, ordered selected eigenvector blocks, and a positive population boundary gap. It concludes the Frobenius sine estimate. A separate theorem gives the existence of an orthogonal aligning matrix and its aligned-frame error bound.

You should be able to derive the aligned-frame factor from principal angles and write the deterministic population-gap inequality without introducing a sample gap. Then ask the statistical question separately: what concentration statement do we have for the operator or Frobenius norm of Sigma hat minus Sigma? The answer to that question depends on the sampling model, while the perturbation theorem does not.

Next we will push the alignment idea further, from subspaces and eigenframes to concrete spectral embeddings, where preserving geometry under orthogonal changes is often the essential invariant.

<!-- END SPOKEN LECTURE -->

---

## Display-only mathematical and Lean correspondence

For selected `d=s-r+1` population eigenvectors, positive `Δ` from the **population** boundary eigenvalues, and `E=Σhat-Σ`, the source-facing Theorem 2 conclusion in `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean` is

\[\|\sin\Theta(V,\widehat V)\|_F\le
\frac{2\min(\sqrt d\,\|E\|_{op},\|E\|_F)}{\Delta}.\]

The optimal orthogonal frame-alignment identity follows from the cross-Gram singular values:

\[\min_{O\in O(d)}\|\widehat V O-V\|_F^2
=2\sum_j(1-\cos\theta_j)\le 2\sum_j\sin^2\theta_j.\]

`YuWangSamworth2015/GROUNDING.md` documents the corrected square in the paper's equation (4); its printed version is refuted in the formalization. The source endpoints here are deterministic; probability concentration is a separate task.

## Exact Lean declaration excerpts

**`SourcePopulationGap`** — The exact denominator refers to consecutive eigenvalues of the POPULATION matrix only. No independent sample-eigenvalue-gap assumption appears in the endpoint.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean`; exact declaration header (proof body omitted).

```lean
def SourcePopulationGap
    {p : Nat}
    (Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (r s : Nat) (Delta : Real) : Prop :=
```

**`theorem2_sinTheta`** — The finite real symmetric theorem takes two ordered eigenvector blocks and the source population gap, and concludes the Frobenius sine-distance bound.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean`; exact declaration header (proof body omitted).

```lean
theorem theorem2_sinTheta
    {p d r s : Nat}
    (Sigma SigmaHat :
      EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace Real (Fin p))
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (sinThetaNorm : Real)
    (hSinThetaNorm :
      sinThetaNorm =
        Submodule.sinThetaFrobenius (Submodule.span Real (Set.range V))
          (Submodule.span Real (Set.range Vhat)))
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    sinThetaNorm ≤
      2 * min
        (Real.sqrt d * ‖SigmaHat - Sigma‖_op)
        ‖SigmaHat - Sigma‖_F / Delta := by
```

**`theorem2_alignedFrame`** — A separately quantified orthogonal matrix aligns the sample block to the population block. The factor two-times-square-root-two is the aligned-frame counterpart of the sine estimate.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean`; exact declaration header (proof body omitted).

```lean
theorem theorem2_alignedFrame
    {p d r s : Nat}
    (Sigma SigmaHat :
      EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace Real (Fin p))
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) Real,
      O ∈ Matrix.orthogonalGroup (Fin d) Real ∧
        Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min
              (Real.sqrt d * ‖SigmaHat - Sigma‖_op)
              ‖SigmaHat - Sigma‖_F / Delta := by
```

**`yuWangSamworth_equation4_printed_counterexample`** — The repository records a concrete refutation of the paper’s defective printed equation (4); the corrected version has the missing square.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/AngleIdentity.lean`; exact declaration header (proof body omitted).

```lean
theorem yuWangSamworth_equation4_printed_counterexample :
    (2 * (3 / 5 : ℝ)) ^ 2 * (1 - (3 / 5 : ℝ) ^ 2) ≠
      (1 / 4 : ℝ) * (2 - 2 * (3 / 5 : ℝ)) *
        (2 - (2 - 2 * (3 / 5 : ℝ))) *
          (4 - (2 - 2 * (3 / 5 : ℝ))) := by
```

