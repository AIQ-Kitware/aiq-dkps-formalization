# Semantic alignment review: headline mathematical statements

Generated: `2026-08-17T18:50:24+00:00`
Repository commit: `448189cd7cd943fbb768a7805f1f577a19e7dd2f`
Working tree clean: `no`
Importance threshold: `headline`
Papers: Yu--Wang--Samworth 2015
Compiler semantic probe run: `yes`
Compiler probe exit code: `1`

## Review purpose

This is a deliberately small semantic-review surface, not a full-paper census. For each selected headline claim it contains enough of both sides of the translation to let a mathematically knowledgeable reviewer decide whether the Lean theorem states the same claim under the same hypotheses and scope.

The **normalized source statement and correspondence table are maintained claims of this project**.  The primary Lean evidence is the human-written source declaration from this commit; the compiler-expanded `#check` type is retained in a details block immediately below it.  The reviewer's job is to challenge the correspondence between the source claim and that declaration.

Project-local definitions are expanded only when they hide mathematically relevant content in a headline theorem type.  Their mathematical role and source declaration are shown first, with full compiler `#print` output in details.  The packet does not recursively dump implementation dependencies.

## Yu--Wang--Samworth 2015

### Yu--Wang--Samworth Theorem 2

Review priority: `headline`

#### Source clause `YWS-T2-sinTheta`

**Source anchor:** Theorem 2

Theorem 2, first conclusion: the population two-sided exterior gap alone controls the Frobenius sine distance by 2 min(sqrt(d)||E||op,||E||F)/Delta, with no sample eigengap.

**Normalized source statement**

*Setup:*

- Sigma and Sigma-hat are real symmetric p x p matrices with ordered eigenvalues lambda_1>=...>=lambda_p and corresponding d-column eigenvector blocks V and V-hat at indices r,...,s; d=s-r+1; E=Sigma-hat-Sigma.

*Hypotheses:*

- Delta = min(lambda_{r-1}-lambda_r, lambda_s-lambda_{s+1}) > 0, with lambda_0=+infinity and lambda_{p+1}=-infinity.
- No sample-eigenvalue separation hypothesis is assumed.

*Conclusion:*

- ||sin Theta(V-hat,V)||_F <= 2 min(sqrt(d)||E||_op, ||E||_F) / Delta.

*Scope:*

- The canonical Lean declaration is specialized to Real^p to mirror the real symmetric matrix statement; the supporting implementation theorem is RCLike-generic.

**Canonical Lean statement as written in the source**

This is the primary Lean text for semantic review.  Relevant ambient `variable` binders inherited by the declaration are shown immediately above it.  The compiler-expanded type is retained below only as verification evidence.

`YuWangSamworth2015.theorem2_sinTheta`

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:346`

~~~~lean
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
        sinThetaFrobenius (Submodule.span Real (Set.range V))
          (Submodule.span Real (Set.range Vhat)))
    (perturbationFrobeniusNorm : Real)
    (hPerturbationFrobeniusNorm :
      perturbationFrobeniusNorm =
        UnitarilyInvariantSeminorm.frobenius Real
          (EuclideanSpace Real (Fin p)) (SigmaHat - Sigma))
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    sinThetaNorm ≤
      2 * min (Real.sqrt d * ‖(SigmaHat - Sigma).toContinuousLinearMap‖)
        perturbationFrobeniusNorm / Delta
~~~~

<details>
<summary><strong>Compiler-expanded verification</strong></summary>

`YuWangSamworth2015.theorem2_sinTheta`

> **UNRESOLVED:** no compiler output

</details>

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment.  The short mathematical gloss is the reading guide; source syntax is shown when it can be located uniquely, and the compiler's complete `#print` output is kept in details.

`YuWangSamworth2015.isEigenvectorBlock_iff` — Expands IsEigenvectorBlock completely: orthonormal columns and the ordered eigenvector equation at index r+i. This leaves the sample eigenvectors arbitrary inside repeated eigenspaces.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:177`

~~~~lean
theorem isEigenvectorBlock_iff
    {p d r s : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric}
    {hr : r ≤ s} {hs : s < p} {hd : d = s - r + 1}
    {V : Fin d → EuclideanSpace Real (Fin p)} :
    IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
      Orthonormal Real V ∧
        ∀ i, Sigma (V i) =
          hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
            (Fin.mk (r + (i : Nat)) (by omega)) • V i
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

`YuWangSamworth2015.sourcePopulationGap_iff` — Characterizes the source Delta itself: the full-space block is the +infinity endpoint case; otherwise Delta is the greatest real satisfying the two population boundary inequalities, hence exactly their finite minimum.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:301`

~~~~lean
theorem sourcePopulationGap_iff
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real} :
    SourcePopulationGap Sigma hSigma r s Delta ↔
      (r = 0 ∧ s + 1 = p) ∨
        (PopulationBoundaryGap Sigma hSigma r s Delta ∧
          ∀ delta : Real,
            PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta)
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

`YuWangSamworth2015.populationBoundaryGap_iff` — Expands the lower-bound predicate used inside SourcePopulationGap into the two population boundary inequalities, with endpoint conventions represented by vacuity and no condition on SigmaHat.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:245`

~~~~lean
theorem populationBoundaryGap_iff
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real} :
    PopulationBoundaryGap Sigma hSigma r s Delta ↔
      ((∀ q j : Fin p, (q : Nat) + 1 = r → (j : Nat) = r →
          Delta ≤
            hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q -
              hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j) ∧
        (∀ j q : Fin p, (j : Nat) = s → (q : Nat) = s + 1 →
          Delta ≤
            hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j -
              hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q))
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

`TauCeti.sinThetaFrobenius_eq` — Identifies sinThetaFrobenius with the Frobenius norm of the sine/cross-projection operator between the two spanned subspaces.

Source: `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean:39`

~~~~lean
-- Ambient variables in scope
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem sinThetaFrobenius_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinThetaFrobenius U V =
      UnitarilyInvariantSeminorm.frobenius 𝕜 E (sinThetaMap U V)
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

`TauCeti.singularValues_sinThetaMap` — Identifies the singular values of the sine/cross-projection operator with Tau Ceti principalSines, the principal-angle sine sequence.

Source: `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:504`

~~~~lean
-- Ambient variables in scope
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

theorem singularValues_sinThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (sinThetaMap U V).singularValues = principalSines U V
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| Sigma and Sigma-hat are real symmetric p by p matrices. | Sigma and SigmaHat are symmetric endomorphisms of EuclideanSpace Real (Fin p), the coordinate-free Real^p representation of real symmetric p by p matrices. | `claimed_exact` |
| The block is the consecutive ordered indices r,...,s with r <= s, s <= p, and d=s-r+1. | The canonical theorem displays hr : r <= s, hs : s < p under zero-based indexing, and hd : d = s - r + 1 literally. | `claimed_exact` |
| V and V-hat are arbitrary orthonormal eigenvector blocks at those ordered indices. | hV and hVhat use IsEigenvectorBlock, whose displayed definition is orthonormality plus Sigma(V_i)=lambda_(r+i)V_i and SigmaHat(Vhat_i)=lambdaHat_(r+i)Vhat_i. | `claimed_exact` |
| Only the population exterior gaps enter Delta; no sample eigengap is assumed. | hgap : SourcePopulationGap Sigma hSigma r s Delta. Its displayed characteristic theorem makes Delta the greatest real satisfying the two population boundary inequalities (the printed finite minimum), with an explicit full-space branch for the +infinity endpoint convention. Neither it nor PopulationBoundaryGap mentions SigmaHat. | `claimed_exact` |
| Frobenius sine bound with 2 min(sqrt(d)\|\|SigmaHat-Sigma\|\|op,\|\|SigmaHat-Sigma\|\|F)/Delta. | The conclusion is `sinThetaNorm <= 2 * min(sqrt d * \|\|SigmaHat-Sigma\|\|op, perturbationFrobeniusNorm) / Delta`.  Immediately above the colon, hSinThetaNorm identifies sinThetaNorm with sinThetaFrobenius of the spans of V and Vhat, and hPerturbationFrobeniusNorm identifies perturbationFrobeniusNorm with the Frobenius seminorm of SigmaHat-Sigma.  The semantic dictionary then identifies sinThetaFrobenius with the sine cross-projection norm and its singular values with the principal-sine sequence. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`YuWangSamworth2015.yuWangSamworth_sinTheta_block_le`

> **UNRESOLVED:** no compiler output

`YuWangSamworth2015.yuWangSamworth_sinTheta_le`

> **UNRESOLVED:** no compiler output

</details>

**Maintainer note:** The canonical theorem is both the presentation and audit surface: its claim uses source-readable scalar names, while equality hypotheses in the same signature expose their exact Lean meanings.  The context dictionary closes the sine quantity through to the principal-sine sequence.

#### Source clause `YWS-T2-alignedBasis`

**Source anchor:** Theorem 2, aligned-basis conclusion

Theorem 2, second conclusion: under the same population-gap hypotheses, there is an orthogonal matrix O-hat aligning the supplied sample frame to the supplied population frame with the printed 2^(3/2) Frobenius bound.

**Normalized source statement**

*Setup:*

- The same Sigma, Sigma-hat, consecutive block r,...,s, supplied eigenvector frames V,V-hat, perturbation E, and d=s-r+1 as in the first conclusion.

*Hypotheses:*

- The same Delta>0 population boundary-gap hypothesis and no sample eigengap.

*Conclusion:*

- There exists O-hat in O(d) such that ||V-hat O-hat - V||_F <= 2^(3/2) min(sqrt(d)||E||_op,||E||_F)/Delta.

*Scope:*

- The canonical review declaration is the Real^p paper-facing wrapper; the older real block theorem and RCLike generalization remain supporting proof surfaces.

**Canonical Lean statement as written in the source**

This is the primary Lean text for semantic review.  Relevant ambient `variable` binders inherited by the declaration are shown immediately above it.  The compiler-expanded type is retained below only as verification evidence.

`YuWangSamworth2015.theorem2_alignedFrame`

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:390`

~~~~lean
theorem theorem2_alignedFrame
    {p d r s : Nat}
    (Sigma SigmaHat :
      EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p))
    (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric)
    (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
    (V Vhat : Fin d → EuclideanSpace Real (Fin p))
    (hV : IsEigenvectorBlock Sigma hSigma hr hs hd V)
    (hVhat : IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
    (perturbationFrobeniusNorm : Real)
    (hPerturbationFrobeniusNorm :
      perturbationFrobeniusNorm =
        UnitarilyInvariantSeminorm.frobenius Real
          (EuclideanSpace Real (Fin p)) (SigmaHat - Sigma))
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) Real,
      O ∈ Matrix.orthogonalGroup (Fin d) Real ∧
        Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min (Real.sqrt d * ‖(SigmaHat - Sigma).toContinuousLinearMap‖)
              perturbationFrobeniusNorm / Delta
~~~~

<details>
<summary><strong>Compiler-expanded verification</strong></summary>

`YuWangSamworth2015.theorem2_alignedFrame`

> **UNRESOLVED:** no compiler output

</details>

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment.  The short mathematical gloss is the reading guide; source syntax is shown when it can be located uniquely, and the compiler's complete `#print` output is kept in details.

`YuWangSamworth2015.isEigenvectorBlock_iff` — Expands the supplied population and sample eigenvector blocks into orthonormality plus their ordered eigenvector equations.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:177`

~~~~lean
theorem isEigenvectorBlock_iff
    {p d r s : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric}
    {hr : r ≤ s} {hs : s < p} {hd : d = s - r + 1}
    {V : Fin d → EuclideanSpace Real (Fin p)} :
    IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
      Orthonormal Real V ∧
        ∀ i, Sigma (V i) =
          hSigma.eigenvalues
            (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp)
            (Fin.mk (r + (i : Nat)) (by omega)) • V i
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

`YuWangSamworth2015.sourcePopulationGap_iff` — Characterizes the source Delta itself as the exact finite population boundary minimum, with an explicit full-space +infinity endpoint case.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:301`

~~~~lean
theorem sourcePopulationGap_iff
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real} :
    SourcePopulationGap Sigma hSigma r s Delta ↔
      (r = 0 ∧ s + 1 = p) ∨
        (PopulationBoundaryGap Sigma hSigma r s Delta ∧
          ∀ delta : Real,
            PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta)
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

`YuWangSamworth2015.populationBoundaryGap_iff` — Expands the lower-bound predicate used inside SourcePopulationGap into the two population-only boundary inequalities and shows that no sample-gap condition is hidden.

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:245`

~~~~lean
theorem populationBoundaryGap_iff
    {p : Nat}
    {Sigma : EuclideanSpace Real (Fin p) →ₗ[Real] EuclideanSpace Real (Fin p)}
    {hSigma : Sigma.IsSymmetric} {r s : Nat} {Delta : Real} :
    PopulationBoundaryGap Sigma hSigma r s Delta ↔
      ((∀ q j : Fin p, (q : Nat) + 1 = r → (j : Nat) = r →
          Delta ≤
            hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q -
              hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j) ∧
        (∀ j q : Fin p, (j : Nat) = s → (q : Nat) = s + 1 →
          Delta ≤
            hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) j -
              hSigma.eigenvalues
                (show finrank Real (EuclideanSpace Real (Fin p)) = p by simp) q))
~~~~

<details>
<summary><strong>Compiler-expanded definition</strong></summary>

> **UNRESOLVED DEFINITION:** no compiler output

</details>

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The second conclusion has the same real symmetric matrices, consecutive eigenvector blocks, and population-only gap as the first. | theorem2_alignedFrame repeats the same Sigma, SigmaHat, hr, hs, hd, IsEigenvectorBlock, Delta>0, and exact SourcePopulationGap mathematical hypotheses as theorem2_sinTheta; its additional hPerturbationFrobeniusNorm is a definitional equality naming the source Frobenius perturbation quantity. | `claimed_exact` |
| There exists O-hat in O(d). | The conclusion existentially returns O : Matrix (Fin d) (Fin d) Real with O in Matrix.orthogonalGroup (Fin d) Real. | `claimed_exact` |
| V-hat O-hat is compared with the supplied V. | The left side is sqrt(sum_i \|\|sum_j O j i * Vhat j - V i\|\|^2), using exactly the V and Vhat arguments from the hypotheses. | `claimed_exact` |
| The constant is 2^(3/2) with the same minimum numerator and Delta denominator. | The conclusion is 2 * sqrt 2 * min(sqrt d * \|\|SigmaHat-Sigma\|\|op, perturbationFrobeniusNorm) / Delta, and the same theorem signature identifies perturbationFrobeniusNorm with the Frobenius seminorm of SigmaHat-Sigma. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le`

> **UNRESOLVED:** no compiler output

`YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le`

> **UNRESOLVED:** no compiler output

</details>

**Maintainer note:** The aligned headline wrapper exposes the orthogonal matrix and aligned frame distance directly.  Only the source Frobenius perturbation quantity is named, with its concrete Lean value given by a literal equality hypothesis in the same theorem signature.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

## Scope intentionally omitted

Rows marked `major`, `supporting`, or `technical` are excluded from the default `headline` packet. Use `--importance major` for the broader tier. The exhaustive paper censuses remain the authority for full-paper coverage.
