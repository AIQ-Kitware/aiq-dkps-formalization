# Semantic alignment review packet

This packet is generated from curated semantic-review fields in the source censuses. Human-written Lean headers are structural source evidence. Compiler output, when present, is elaborator-backed evidence about the Lean surface. The source-to-Lean correspondence remains the census author's explicit review claim.

**Compiler imports:** `YuWangSamworth2015`

## Yi Yu, Tengyao Wang and Richard J. Samworth, A useful variant of the Davis--Kahan theorem for statisticians, Biometrika 102(2), 2015, 315--323; preprint arXiv:1405.0680.: Yu--Wang--Samworth Theorem 2

Theorem 2, first conclusion: the population two-sided exterior gap alone controls the Frobenius sine distance by 2 min(sqrt(d)||E||op,||E||F)/Delta, with no sample eigengap.

### `YWS-T2-sinTheta`

### Normalized source statement

**Setup**
- Sigma and Sigma-hat are real symmetric p x p matrices with ordered eigenvalues lambda_1>=...>=lambda_p and corresponding d-column eigenvector blocks V and V-hat at indices r,...,s; d=s-r+1; E=Sigma-hat-Sigma.

**Hypotheses**
- Delta = min(lambda_{r-1}-lambda_r, lambda_s-lambda_{s+1}) > 0, with lambda_0=+infinity and lambda_{p+1}=-infinity.
- No sample-eigenvalue separation hypothesis is assumed.

**Conclusions**
- ||sin Theta(V-hat,V)||_F <= 2 min(sqrt(d)||E||_op, ||E||_F) / Delta.

**Scope**
- The canonical Lean declaration is specialized to Real^p to mirror the real symmetric matrix statement; the supporting implementation theorem is RCLike-generic.

### Canonical Lean declarations

#### `YuWangSamworth2015.theorem2_sinTheta`

**Human-written Lean statement**

`YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:371`

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
    (Delta : Real) (hDelta : 0 < Delta)
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    sinThetaNorm ≤
      2 * min
        (Real.sqrt d * ‖SigmaHat - Sigma‖_op)
        ‖SigmaHat - Sigma‖_F / Delta
~~~~

**Compiler-resolved type**

~~~~lean
@YuWangSamworth2015.theorem2_sinTheta : ∀ {p d r s : ℕ}
  (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
  (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
  (V Vhat : Fin d → EuclideanSpace ℝ (Fin p)),
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V →
    YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat →
      ∀ (sinThetaNorm : ℝ),
        sinThetaNorm = TauCeti.sinThetaFrobenius (Submodule.span ℝ (Set.range V)) (Submodule.span ℝ (Set.range Vhat)) →
          ∀ (Delta : ℝ),
            0 < Delta →
              YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta →
                sinThetaNorm ≤
                  2 *
                      min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
                        (YuWangSamworth2015.frobeniusNorm (SigmaHat - Sigma)) /
                    Delta
~~~~

### Supporting scope declarations

- `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le` — resolved; source located
- `YuWangSamworth2015.yuWangSamworth_sinTheta_le` — resolved; source located

### Local semantic dictionary

#### `YuWangSamworth2015.isEigenvectorBlock_iff`

Expands IsEigenvectorBlock completely: orthonormal columns and the ordered eigenvector equation at index r+i. This leaves the sample eigenvectors arbitrary inside repeated eigenspaces.

~~~~lean
theorem YuWangSamworth2015.isEigenvectorBlock_iff : ∀ {p d r s : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {hr : r ≤ s}
  {hs : s < p} {hd : d = s - r + 1} {V : Fin d → EuclideanSpace ℝ (Fin p)},
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
    Orthonormal ℝ V ∧ ∀ (i : Fin d), Sigma (V i) = hSigma.eigenvalues ⋯ ⟨r + ↑i, ⋯⟩ • V i :=
fun {p d r s} {Sigma} {hSigma} {hr} {hs} {hd} {V} => Iff.rfl
~~~~

#### `YuWangSamworth2015.sourcePopulationGap_iff`

Characterizes the source Delta itself: the full-space block is the +infinity endpoint case; otherwise Delta is the greatest real satisfying the two population boundary inequalities, hence exactly their finite minimum.

~~~~lean
theorem YuWangSamworth2015.sourcePopulationGap_iff : ∀ {p : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {r s : ℕ} {Delta : ℝ},
  YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta ↔
    r = 0 ∧ s + 1 = p ∨
      YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta ∧
        ∀ (delta : ℝ), YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta :=
fun {p} {Sigma} {hSigma} {r s} {Delta} => Iff.rfl
~~~~

#### `YuWangSamworth2015.populationBoundaryGap_iff`

Expands the lower-bound predicate used inside SourcePopulationGap into the two population boundary inequalities, with endpoint conventions represented by vacuity and no condition on SigmaHat.

~~~~lean
theorem YuWangSamworth2015.populationBoundaryGap_iff : ∀ {p : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {r s : ℕ} {Delta : ℝ},
  YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta ↔
    (∀ (q j : Fin p), ↑q + 1 = r → ↑j = r → Delta ≤ hSigma.eigenvalues ⋯ q - hSigma.eigenvalues ⋯ j) ∧
      ∀ (j q : Fin p), ↑j = s → ↑q = s + 1 → Delta ≤ hSigma.eigenvalues ⋯ j - hSigma.eigenvalues ⋯ q :=
fun {p} {Sigma} {hSigma} {r s} {Delta} => Iff.rfl
~~~~

#### `YuWangSamworth2015.frobeniusNorm`

Reducible source-facing abbreviation for the existing Frobenius seminorm of a real square operator; in the headline theorem it is applied literally to SigmaHat-Sigma.

~~~~lean
@[reducible] def YuWangSamworth2015.frobeniusNorm : {p : ℕ} →
  (EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) → ℝ :=
fun {p} A => (TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ (EuclideanSpace ℝ (Fin p))).toFun A
~~~~

#### `TauCeti.sinThetaFrobenius_eq`

Identifies sinThetaFrobenius with the Frobenius norm of the sine/cross-projection operator between the two spanned subspaces.

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

#### `TauCeti.singularValues_sinThetaMap`

Identifies the singular values of the sine/cross-projection operator with Tau Ceti principalSines, the principal-angle sine sequence.

~~~~lean
@[defeq] theorem TauCeti.singularValues_sinThetaMap.{u_1, u_2} : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E]
  (U V : Submodule 𝕜 E) [inst_4 : U.HasOrthogonalProjection] [inst_5 : V.HasOrthogonalProjection],
  (TauCeti.sinThetaMap U V).singularValues = TauCeti.principalSines U V :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] U V
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  rfl
~~~~

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| Sigma and Sigma-hat are real symmetric p by p matrices. | Sigma and SigmaHat are symmetric endomorphisms of EuclideanSpace Real (Fin p), the coordinate-free Real^p representation of real symmetric p by p matrices. | claimed_exact |
| The block is the consecutive ordered indices r,...,s with r <= s, s <= p, and d=s-r+1. | The canonical theorem displays hr : r <= s, hs : s < p under zero-based indexing, and hd : d = s - r + 1 literally. | claimed_exact |
| V and V-hat are arbitrary orthonormal eigenvector blocks at those ordered indices. | hV and hVhat use IsEigenvectorBlock, whose displayed definition is orthonormality plus Sigma(V_i)=lambda_(r+i)V_i and SigmaHat(Vhat_i)=lambdaHat_(r+i)Vhat_i. | claimed_exact |
| Only the population exterior gaps enter Delta; no sample eigengap is assumed. | hgap : SourcePopulationGap Sigma hSigma r s Delta. Its displayed characteristic theorem makes Delta the greatest real satisfying the two population boundary inequalities (the printed finite minimum), with an explicit full-space branch for the +infinity endpoint convention. Neither it nor PopulationBoundaryGap mentions SigmaHat. | claimed_exact |
| Frobenius sine bound with 2 min(sqrt(d)\|\|SigmaHat-Sigma\|\|op,\|\|SigmaHat-Sigma\|\|F)/Delta. | The conclusion is `sinThetaNorm <= 2 * min(sqrt d * \|\|SigmaHat-Sigma\|\|op, frobeniusNorm (SigmaHat-Sigma)) / Delta`. Immediately above the colon, hSinThetaNorm identifies sinThetaNorm with sinThetaFrobenius of the spans of V and Vhat. The local semantic dictionary expands the reducible frobeniusNorm abbreviation and then identifies sinThetaFrobenius with the sine cross-projection norm and its singular values with the principal-sine sequence. | claimed_exact |

**Review note.** The canonical theorem is both the presentation and audit surface: its claim uses the source-readable sinThetaNorm name and the literal application `frobeniusNorm (SigmaHat - Sigma)`. The equality hypothesis in the same signature exposes the exact Lean meaning of sinThetaNorm, while the semantic dictionary expands frobeniusNorm and closes the sine quantity through to the principal-sine sequence.

**Next action.** None.

### `YWS-T2-alignedBasis`

### Normalized source statement

**Setup**
- The same Sigma, Sigma-hat, consecutive block r,...,s, supplied eigenvector frames V,V-hat, perturbation E, and d=s-r+1 as in the first conclusion.

**Hypotheses**
- The same Delta>0 population boundary-gap hypothesis and no sample eigengap.

**Conclusions**
- There exists O-hat in O(d) such that ||V-hat O-hat - V||_F <= 2^(3/2) min(sqrt(d)||E||_op,||E||_F)/Delta.

**Scope**
- The canonical review declaration is the Real^p paper-facing wrapper; the older real block theorem and RCLike generalization remain supporting proof surfaces.

### Canonical Lean declarations

#### `YuWangSamworth2015.theorem2_alignedFrame`

**Human-written Lean statement**

`YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean:411`

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
    (hgap : SourcePopulationGap Sigma hSigma r s Delta) :
    ∃ O : Matrix (Fin d) (Fin d) Real,
      O ∈ Matrix.orthogonalGroup (Fin d) Real ∧
        Real.sqrt (∑ i, ‖(∑ j, O j i • Vhat j) - V i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min
              (Real.sqrt d * ‖SigmaHat - Sigma‖_op)
              ‖SigmaHat - Sigma‖_F / Delta
~~~~

**Compiler-resolved type**

~~~~lean
@YuWangSamworth2015.theorem2_alignedFrame : ∀ {p d r s : ℕ}
  (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
  (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1)
  (V Vhat : Fin d → EuclideanSpace ℝ (Fin p)),
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V →
    YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat →
      ∀ (Delta : ℝ),
        0 < Delta →
          YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta →
            ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
              √(∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
                2 * √2 *
                    min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
                      (YuWangSamworth2015.frobeniusNorm (SigmaHat - Sigma)) /
                  Delta
~~~~

### Supporting scope declarations

- `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le` — resolved; source located
- `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le` — resolved; source located

### Local semantic dictionary

#### `YuWangSamworth2015.isEigenvectorBlock_iff`

Expands the supplied population and sample eigenvector blocks into orthonormality plus their ordered eigenvector equations.

~~~~lean
theorem YuWangSamworth2015.isEigenvectorBlock_iff : ∀ {p d r s : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {hr : r ≤ s}
  {hs : s < p} {hd : d = s - r + 1} {V : Fin d → EuclideanSpace ℝ (Fin p)},
  YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V ↔
    Orthonormal ℝ V ∧ ∀ (i : Fin d), Sigma (V i) = hSigma.eigenvalues ⋯ ⟨r + ↑i, ⋯⟩ • V i :=
fun {p d r s} {Sigma} {hSigma} {hr} {hs} {hd} {V} => Iff.rfl
~~~~

#### `YuWangSamworth2015.sourcePopulationGap_iff`

Characterizes the source Delta itself as the exact finite population boundary minimum, with an explicit full-space +infinity endpoint case.

~~~~lean
theorem YuWangSamworth2015.sourcePopulationGap_iff : ∀ {p : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {r s : ℕ} {Delta : ℝ},
  YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta ↔
    r = 0 ∧ s + 1 = p ∨
      YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta ∧
        ∀ (delta : ℝ), YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s delta → delta ≤ Delta :=
fun {p} {Sigma} {hSigma} {r s} {Delta} => Iff.rfl
~~~~

#### `YuWangSamworth2015.populationBoundaryGap_iff`

Expands the lower-bound predicate used inside SourcePopulationGap into the two population-only boundary inequalities and shows that no sample-gap condition is hidden.

~~~~lean
theorem YuWangSamworth2015.populationBoundaryGap_iff : ∀ {p : ℕ}
  {Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {hSigma : Sigma.IsSymmetric} {r s : ℕ} {Delta : ℝ},
  YuWangSamworth2015.PopulationBoundaryGap Sigma hSigma r s Delta ↔
    (∀ (q j : Fin p), ↑q + 1 = r → ↑j = r → Delta ≤ hSigma.eigenvalues ⋯ q - hSigma.eigenvalues ⋯ j) ∧
      ∀ (j q : Fin p), ↑j = s → ↑q = s + 1 → Delta ≤ hSigma.eigenvalues ⋯ j - hSigma.eigenvalues ⋯ q :=
fun {p} {Sigma} {hSigma} {r s} {Delta} => Iff.rfl
~~~~

#### `YuWangSamworth2015.frobeniusNorm`

Reducible source-facing abbreviation for the existing Frobenius seminorm, applied directly to SigmaHat-Sigma in the aligned-frame bound.

~~~~lean
@[reducible] def YuWangSamworth2015.frobeniusNorm : {p : ℕ} →
  (EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) → ℝ :=
fun {p} A => (TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ (EuclideanSpace ℝ (Fin p))).toFun A
~~~~

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The second conclusion has the same real symmetric matrices, consecutive eigenvector blocks, and population-only gap as the first. | theorem2_alignedFrame repeats the same Sigma, SigmaHat, hr, hs, hd, IsEigenvectorBlock, Delta>0, and exact SourcePopulationGap mathematical hypotheses as theorem2_sinTheta. The perturbation Frobenius term is written directly as `frobeniusNorm (SigmaHat - Sigma)`. | claimed_exact |
| There exists O-hat in O(d). | The conclusion existentially returns O : Matrix (Fin d) (Fin d) Real with O in Matrix.orthogonalGroup (Fin d) Real. | claimed_exact |
| V-hat O-hat is compared with the supplied V. | The left side is sqrt(sum_i \|\|sum_j O j i * Vhat j - V i\|\|^2), using exactly the V and Vhat arguments from the hypotheses. | claimed_exact |
| The constant is 2^(3/2) with the same minimum numerator and Delta denominator. | The conclusion is 2 * sqrt 2 * min(sqrt d * \|\|SigmaHat-Sigma\|\|op, frobeniusNorm (SigmaHat-Sigma)) / Delta; the local semantic dictionary expands frobeniusNorm to the existing Frobenius seminorm. | claimed_exact |

**Review note.** The aligned headline wrapper exposes the orthogonal matrix and aligned frame distance directly and writes the source perturbation Frobenius norm as the reducible `frobeniusNorm (SigmaHat - Sigma)` application.

**Next action.** None.
