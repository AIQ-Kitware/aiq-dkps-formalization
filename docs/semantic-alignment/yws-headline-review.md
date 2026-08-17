# Semantic alignment review: headline mathematical statements

Generated: `2026-08-17T17:12:48+00:00`
Repository commit: `6c7741125d3b025e7ac1ef2c13bf992711a9e1be`
Working tree clean: `no`
Importance threshold: `headline`
Papers: Yu--Wang--Samworth 2015
Compiler semantic probe run: `yes`
Compiler probe exit code: `0`

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

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:285`

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
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : PopulationBoundaryGap Sigma hSigma r s Delta) :
    sinThetaFrobenius (Submodule.span Real (Set.range V))
        (Submodule.span Real (Set.range Vhat)) ≤
      2 * min (Real.sqrt d * ‖(SigmaHat - Sigma).toContinuousLinearMap‖)
        (UnitarilyInvariantSeminorm.frobenius Real (EuclideanSpace Real (Fin p))
          (SigmaHat - Sigma)) / Delta
~~~~

<details>
<summary><strong>Compiler-expanded verification</strong></summary>

`YuWangSamworth2015.theorem2_sinTheta`

~~~~lean
@YuWangSamworth2015.theorem2_sinTheta : ∀ {p d r s : ℕ}
  (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
  (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
  (V Vhat : Fin d → EuclideanSpace ℝ (Fin p)),
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V →
    YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat →
      ∀ (Delta : ℝ),
        0 < Delta →
          YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta →
            TauCeti.sinThetaFrobenius (Submodule.span ℝ (Set.range V)) (Submodule.span ℝ (Set.range Vhat)) ≤
              2 *
                  min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
                    ((TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ (EuclideanSpace ℝ (Fin p))).toFun
                      (SigmaHat - Sigma)) /
                Delta
~~~~

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

~~~~lean
theorem YuWangSamworth2015.isEigenvectorBlock_iff : ∀ {p d r s : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {hr : r ≤ s}
  {hs : s < p} {hd : d = s - r + 1} {V : Fin d → EuclideanSpace ℝ (Fin p)},
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
    Orthonormal ℝ V ∧ ∀ (i : Fin d), Sigma (V i) = hSigma.eigenvalues ⋯ ⟨r + ↑i, ⋯⟩ • V i :=
fun {p d r s} {Sigma} {hSigma} {hr} {hs} {hd} {V} => Iff.rfl
~~~~

</details>

`YuWangSamworth2015.populationBoundaryGap_iff` — Expands PopulationBoundaryGap completely into the two population boundary inequalities, with endpoint conventions represented by vacuity and no condition on SigmaHat.

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

~~~~lean
theorem YuWangSamworth2015.populationBoundaryGap_iff : ∀ {p : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {r s : ℕ} {Delta : ℝ},
  YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta ↔
    (∀ (q j : Fin p), ↑q + 1 = r → ↑j = r → Delta ≤ hSigma.eigenvalues ⋯ q - hSigma.eigenvalues ⋯ j) ∧
      ∀ (j q : Fin p), ↑j = s → ↑q = s + 1 → Delta ≤ hSigma.eigenvalues ⋯ j - hSigma.eigenvalues ⋯ q :=
fun {p} {Sigma} {hSigma} {r s} {Delta} => Iff.rfl
~~~~

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

~~~~lean
theorem TauCeti.sinThetaFrobenius_eq.{u_1, u_2} : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E]
  (U V : Submodule 𝕜 E) [inst_4 : U.HasOrthogonalProjection] [inst_5 : V.HasOrthogonalProjection],
  TauCeti.sinThetaFrobenius U V = (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (TauCeti.sinThetaMap U V) :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] U V
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  Eq.mpr
    (id
      (congrArg (fun _a => _a = (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (TauCeti.sinThetaMap U V))
        (TauCeti.sinThetaFrobenius.eq_1✝ U V)))
    (Eq.refl ((TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (TauCeti.sinThetaMap U V)))
~~~~

</details>

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| Sigma and Sigma-hat are real symmetric p by p matrices. | Sigma and SigmaHat are symmetric endomorphisms of EuclideanSpace Real (Fin p), the coordinate-free Real^p representation of real symmetric p by p matrices. | `claimed_exact` |
| The block is the consecutive ordered indices r,...,s with r <= s, s <= p, and d=s-r+1. | The canonical theorem displays hr : r <= s, hs : s < p under zero-based indexing, and hd : d = s - r + 1 literally. | `claimed_exact` |
| V and V-hat are arbitrary orthonormal eigenvector blocks at those ordered indices. | hV and hVhat use IsEigenvectorBlock, whose displayed definition is orthonormality plus Sigma(V_i)=lambda_(r+i)V_i and SigmaHat(Vhat_i)=lambdaHat_(r+i)Vhat_i. | `claimed_exact` |
| Only the population exterior gaps enter Delta; no sample eigengap is assumed. | hgap : PopulationBoundaryGap Sigma hSigma r s Delta. Its displayed definition mentions only Sigma and its sorted eigenvalues; there is no gap hypothesis involving SigmaHat. | `claimed_exact` |
| Frobenius sine bound with 2 min(sqrt(d)\|\|SigmaHat-Sigma\|\|op,\|\|SigmaHat-Sigma\|\|F)/Delta. | The conclusion of theorem2_sinTheta displays exactly that bound, with the operator norm as the norm of the associated continuous linear map and the Frobenius norm as the TauCeti unitarily-invariant Frobenius seminorm. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`YuWangSamworth2015.yuWangSamworth_sinTheta_block_le`

~~~~lean
@YuWangSamworth2015.yuWangSamworth_sinTheta_block_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
  {hA : A.IsSymmetric} {hB : B.IsSymmetric} {n d r s : ℕ} {hn : Module.finrank 𝕜 E = n} (hsn : s + 1 ≤ n)
  (hd : r + d = s + 1) {u v : Fin d → E},
  TauCeti.IsOrderedEigenframe hA hn (YuWangSamworth2015.consecutiveEmb ⋯) u →
    TauCeti.IsOrderedEigenframe hB hn (YuWangSamworth2015.consecutiveEmb ⋯) v →
      ∀ {Δ : ℝ},
        0 < Δ →
          YuWangSamworth2015.OrderedBlockBoundaryGap hA hn r s Δ →
            TauCeti.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u)) (Submodule.span 𝕜 (Set.range v)) ≤
              2 *
                  min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                    ((TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (B - A)) /
                Δ
~~~~

`YuWangSamworth2015.yuWangSamworth_sinTheta_le`

~~~~lean
@YuWangSamworth2015.yuWangSamworth_sinTheta_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) {U V : Submodule 𝕜 E} [inst_4 : U.HasOrthogonalProjection]
  [inst_5 : V.HasOrthogonalProjection],
  TauCeti.IsInvariant A U →
    TauCeti.IsInvariant B V →
      YuWangSamworth2015.CorrespondingEigenblock hA hB U V →
        ∀ {d : ℕ},
          Module.finrank 𝕜 ↥U = d →
            ∀ {Δ : ℝ},
              0 < Δ →
                TauCeti.InternalGap A U Δ →
                  TauCeti.sinThetaFrobenius U V ≤
                    2 *
                        min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                          ((TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (B - A)) /
                      Δ
~~~~

</details>

**Maintainer note:** The canonical declaration is intentionally a thin Real^p wrapper over the more general proved block theorem. Its only project-local hypothesis abbreviations are printed in the semantic dictionary, so the review surface does not require chasing consecutiveEmb or IsOrderedEigenframe.

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

Source: `YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:317`

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
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : PopulationBoundaryGap Sigma hSigma r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) Real,
      O ∈ Matrix.orthogonalGroup (Fin d) Real ∧
        Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min (Real.sqrt d * ‖(SigmaHat - Sigma).toContinuousLinearMap‖)
              (UnitarilyInvariantSeminorm.frobenius Real
                (EuclideanSpace Real (Fin p)) (SigmaHat - Sigma)) / Delta
~~~~

<details>
<summary><strong>Compiler-expanded verification</strong></summary>

`YuWangSamworth2015.theorem2_alignedFrame`

~~~~lean
@YuWangSamworth2015.theorem2_alignedFrame : ∀ {p d r s : ℕ}
  (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
  (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
  (V Vhat : Fin d → EuclideanSpace ℝ (Fin p)),
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V →
    YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat →
      ∀ (Delta : ℝ),
        0 < Delta →
          YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta →
            ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
              √(∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
                2 * √2 *
                    min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
                      ((TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ (EuclideanSpace ℝ (Fin p))).toFun
                        (SigmaHat - Sigma)) /
                  Delta
~~~~

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

~~~~lean
theorem YuWangSamworth2015.isEigenvectorBlock_iff : ∀ {p d r s : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {hr : r ≤ s}
  {hs : s < p} {hd : d = s - r + 1} {V : Fin d → EuclideanSpace ℝ (Fin p)},
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
    Orthonormal ℝ V ∧ ∀ (i : Fin d), Sigma (V i) = hSigma.eigenvalues ⋯ ⟨r + ↑i, ⋯⟩ • V i :=
fun {p d r s} {Sigma} {hSigma} {hr} {hs} {hd} {V} => Iff.rfl
~~~~

</details>

`YuWangSamworth2015.populationBoundaryGap_iff` — Expands the gap hypothesis into the two population boundary inequalities and shows that no sample-gap condition is hidden.

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

~~~~lean
theorem YuWangSamworth2015.populationBoundaryGap_iff : ∀ {p : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {r s : ℕ} {Delta : ℝ},
  YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta ↔
    (∀ (q j : Fin p), ↑q + 1 = r → ↑j = r → Delta ≤ hSigma.eigenvalues ⋯ q - hSigma.eigenvalues ⋯ j) ∧
      ∀ (j q : Fin p), ↑j = s → ↑q = s + 1 → Delta ≤ hSigma.eigenvalues ⋯ j - hSigma.eigenvalues ⋯ q :=
fun {p} {Sigma} {hSigma} {r s} {Delta} => Iff.rfl
~~~~

</details>

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The second conclusion has the same real symmetric matrices, consecutive eigenvector blocks, and population-only gap as the first. | theorem2_alignedFrame repeats the same Sigma, SigmaHat, hr, hs, hd, IsEigenvectorBlock, Delta>0, and PopulationBoundaryGap hypotheses as theorem2_sinTheta. | `claimed_exact` |
| There exists O-hat in O(d). | The conclusion existentially returns O : Matrix (Fin d) (Fin d) Real with O in Matrix.orthogonalGroup (Fin d) Real. | `claimed_exact` |
| V-hat O-hat is compared with the supplied V. | The left side is sqrt(sum_i \|\|sum_j O j i * Vhat j - V i\|\|^2), using exactly the V and Vhat arguments from the hypotheses. | `claimed_exact` |
| The constant is 2^(3/2) with the same minimum numerator and Delta denominator. | The conclusion is 2 * sqrt 2 * min(sqrt d * \|\|SigmaHat-Sigma\|\|op, \|\|SigmaHat-Sigma\|\|F) / Delta. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le`

~~~~lean
@YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le : ∀ {F : Type u_1} [inst : NormedAddCommGroup F]
  [inst_1 : InnerProductSpace ℝ F] [inst_2 : FiniteDimensional ℝ F] {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric}
  {hB : B.IsSymmetric} {n d r s : ℕ} {hn : Module.finrank ℝ F = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
  {u v : Fin d → F},
  TauCeti.IsOrderedEigenframe hA hn (YuWangSamworth2015.consecutiveEmb ⋯) u →
    TauCeti.IsOrderedEigenframe hB hn (YuWangSamworth2015.consecutiveEmb ⋯) v →
      ∀ {Δ : ℝ},
        0 < Δ →
          YuWangSamworth2015.OrderedBlockBoundaryGap hA hn r s Δ →
            ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
              √(∑ i, ‖∑ j, O j i • v j - u i‖ ^ 2) ≤
                2 * √2 *
                    min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                      ((TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ F).toFun (B - A)) /
                  Δ
~~~~

`YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le`

~~~~lean
@YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
  {hA : A.IsSymmetric} {hB : B.IsSymmetric} {n d r s : ℕ} {hn : Module.finrank 𝕜 E = n} (hsn : s + 1 ≤ n)
  (hd : r + d = s + 1) {u v : Fin d → E},
  TauCeti.IsOrderedEigenframe hA hn (YuWangSamworth2015.consecutiveEmb ⋯) u →
    ∀ (hv : TauCeti.IsOrderedEigenframe hB hn (YuWangSamworth2015.consecutiveEmb ⋯) v) {Δ : ℝ},
      0 < Δ →
        YuWangSamworth2015.OrderedBlockBoundaryGap hA hn r s Δ →
          ∃ O,
            (∀ (x y : EuclideanSpace 𝕜 (Fin d)), inner 𝕜 (O x) (O y) = inner 𝕜 x y) ∧
              √(∑ i, ‖YuWangSamworth2015.frameComp ⋯ O i - u i‖ ^ 2) ≤
                2 * √2 *
                    min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                      ((TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (B - A)) /
                  Δ
~~~~

</details>

**Maintainer note:** The aligned headline wrapper shares the exact hypothesis surface of theorem2_sinTheta and exposes the source orthogonal matrix directly. The semantic dictionary expands the only two YWS-specific predicates in that type.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

## Scope intentionally omitted

Rows marked `major`, `supporting`, or `technical` are excluded from the default `headline` packet. Use `--importance major` for the broader tier. The exhaustive paper censuses remain the authority for full-paper coverage.
