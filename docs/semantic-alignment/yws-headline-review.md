# Semantic alignment review packet

This packet is generated from curated semantic-review fields in the source censuses. Human-written Lean headers are structural source evidence. Compiler output, when present, is elaborator-backed evidence about the Lean surface. The source-to-Lean correspondence remains the census author's explicit review claim.

**Elaborator evidence:** statement sidecar with 309 record(s), toolchain `leanprover/lean4:v4.34.0-rc1`. Signatures, hashes and closures below are read from the elaborated environment, not from source text.

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

**Elaborated signature** (statement pin: current)

~~~~lean
YuWangSamworth2015.theorem2_sinTheta {p d r s : ℕ}
  (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p)
  (hd : d = s - r + 1) (V Vhat : Fin d → EuclideanSpace ℝ (Fin p))
  (hV : YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V)
  (hVhat : YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
  (sinThetaNorm : ℝ)
  (hSinThetaNorm :
    sinThetaNorm =
      TauCeti.sinThetaFrobenius (Submodule.span ℝ (Set.range V))
        (Submodule.span ℝ (Set.range Vhat)))
  (Delta : ℝ) (hDelta : 0 < Delta)
  (hgap : YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta) :
  sinThetaNorm ≤
    2 *
        min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
          (YuWangSamworth2015.frobeniusNorm (SigmaHat - Sigma)) /
      Delta
~~~~

Structural type hash `3500685691`, printed-type hash `61df0a9f00908bbe`.

Statement closure: 10 project constant(s) unfolded, 0 project leaf/leaves, 36 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `YuWangSamworth2015.IsEigenvectorBlock`, `TauCeti.sinThetaFrobenius`, `YuWangSamworth2015.SourcePopulationGap`, `TauCeti.UnitarilyInvariantSeminorm.frobenius`, `TauCeti.sinThetaMap`, `YuWangSamworth2015.PopulationBoundaryGap`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.complementaryProjection`, `TauCeti.projection`
Boundary vocabulary: `Nat`, `LinearMap`, `Real`, `RingHom.id`, `EuclideanSpace`, `Fin`, `ENNReal`, `LinearMap.IsSymmetric`, `Eq`, `Submodule.span`, `Set.range`, `Subtype`, `Submodule`, `Real.sqrt`, `Nat.cast`, `ContinuousLinearMap`, `LinearEquiv`, `LinearMap.toContinuousLinearMap`, `And`, `Orthonormal`, `LinearMap.IsSymmetric.eigenvalues`, `RCLike`, `NormedAddCommGroup`, `InnerProductSpace`, `FiniteDimensional`, `Submodule.HasOrthogonalProjection`, `Or`, `Finset.sum`, `Module.finrank`, `Finset.univ`, `OrthonormalBasis`, `stdOrthonormalBasis`, `LinearIsometryEquiv`, `LinearMap.comp`, `Submodule.orthogonal`, `Submodule.starProjection`

<details><summary>Statement closure tree</summary>

~~~~text
YuWangSamworth2015.theorem2_sinTheta  (theorem, YuWangSamworth2015/Symmetric/Theorem2.lean:357)
    YuWangSamworth2015.theorem2_sinTheta {p d r s : ℕ}
      (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
      (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p)
      (hd : d = s - r + 1) (V Vhat : Fin d → EuclideanSpace ℝ (Fin p))
      (hV : YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V)
      (hVhat : YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat)
      (sinThetaNorm : ℝ)
      (hSinThetaNorm :
        sinThetaNorm =
          TauCeti.sinThetaFrobenius (Submodule.span ℝ (Set.range V))
            (Submodule.span ℝ (Set.range Vhat)))
      (Delta : ℝ) (hDelta : 0 < Delta)
      (hgap : YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta) :
      sinThetaNorm ≤
        2 *
            min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
              (YuWangSamworth2015.frobeniusNorm (SigmaHat - Sigma)) /
          Delta
    hash: expr=3500685691 text=61df0a9f00908bbe
  [type] YuWangSamworth2015.IsEigenvectorBlock  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:159)
      YuWangSamworth2015.IsEigenvectorBlock {p d r s : ℕ}
        (Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
        (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1) (V : Fin d → EuclideanSpace ℝ (Fin p)) : Prop
      hash: expr=1106865433 text=ffe3502345f67ce2
  [type] TauCeti.sinThetaFrobenius  (def, ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean:33)
      TauCeti.sinThetaFrobenius.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : ℝ
      hash: expr=2854648257 text=0ec6530664147185
    [body] TauCeti.UnitarilyInvariantSeminorm.frobenius  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:573)
        TauCeti.UnitarilyInvariantSeminorm.frobenius.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
          TauCeti.UnitarilyInvariantSeminorm 𝕜 E
        hash: expr=3446404092 text=20e49e15f61e4e69
      [type] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
          TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
          field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
          field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
          field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
          field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
          hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.sinThetaMap  (def, ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:59)
        TauCeti.sinThetaMap.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2} [NormedAddCommGroup E]
          [InnerProductSpace 𝕜 E] (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →ₗ[𝕜] E
        hash: expr=2598557352 text=076d3d5dc3e3f18e
      [body] TauCeti.complementaryProjection  (def, ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean:125)
          TauCeti.complementaryProjection.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
            E →ₗ[𝕜] E
          hash: expr=2692684913 text=1ddd79569757bcd7
        [body] TauCeti.projection  (def, ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean:118)
            TauCeti.projection.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2} [NormedAddCommGroup E]
              [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : E →ₗ[𝕜] E
            hash: expr=2692684913 text=1ddd79569757bcd7
      [body] TauCeti.projection  (above)
  [type] YuWangSamworth2015.SourcePopulationGap  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:279)
      YuWangSamworth2015.SourcePopulationGap {p : ℕ}
        (Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
        (r s : ℕ) (Delta : ℝ) : Prop
      hash: expr=1183521196 text=c73678dcf8b912e0
    [body] YuWangSamworth2015.PopulationBoundaryGap  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:219)
        YuWangSamworth2015.PopulationBoundaryGap {p : ℕ}
          (Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
          (r s : ℕ) (Delta : ℝ) : Prop
        hash: expr=1183521196 text=c73678dcf8b912e0
  [type] YuWangSamworth2015.frobeniusNorm  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:342)
      YuWangSamworth2015.frobeniusNorm {p : ℕ}
        (A : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) : ℝ
      hash: expr=2597927890 text=33f958e470c75938
    [body] TauCeti.UnitarilyInvariantSeminorm.frobenius  (above)

10 project constant(s) unfolded, 0 project leaf/leaves, 36 boundary constant(s), 170 instance/projection constant(s)
boundary: Nat, LinearMap, Real, RingHom.id, EuclideanSpace, Fin, ENNReal, LinearMap.IsSymmetric, Eq, Submodule.span, Set.range, Subtype, Submodule, Real.sqrt, Nat.cast, ContinuousLinearMap, LinearEquiv, LinearMap.toContinuousLinearMap, And, Orthonormal, LinearMap.IsSymmetric.eigenvalues, RCLike, NormedAddCommGroup, InnerProductSpace, FiniteDimensional, Submodule.HasOrthogonalProjection, Or, Finset.sum, Module.finrank, Finset.univ, OrthonormalBasis, stdOrthonormalBasis, LinearIsometryEquiv, LinearMap.comp, Submodule.orthogonal, Submodule.starProjection
~~~~

</details>

### Supporting scope declarations

- `YuWangSamworth2015.yuWangSamworth_sinTheta_block_le` — elaborated; source located
- `YuWangSamworth2015.yuWangSamworth_sinTheta_le` — elaborated; source located

### Local semantic dictionary

#### `YuWangSamworth2015.isEigenvectorBlock_iff`

Expands IsEigenvectorBlock completely: orthonormal columns and the ordered eigenvector equation at index r+i. This leaves the sample eigenvectors arbitrary inside repeated eigenspaces.

#### `YuWangSamworth2015.sourcePopulationGap_iff`

Characterizes the source Delta itself: the full-space block is the +infinity endpoint case; otherwise Delta is the greatest real satisfying the two population boundary inequalities, hence exactly their finite minimum.

#### `YuWangSamworth2015.populationBoundaryGap_iff`

Expands the lower-bound predicate used inside SourcePopulationGap into the two population boundary inequalities, with endpoint conventions represented by vacuity and no condition on SigmaHat.

#### `YuWangSamworth2015.frobeniusNorm`

Reducible source-facing abbreviation for the existing Frobenius seminorm of a real square operator; in the headline theorem it is applied literally to SigmaHat-Sigma.

#### `TauCeti.sinThetaFrobenius_eq`

Identifies sinThetaFrobenius with the Frobenius norm of the sine/cross-projection operator between the two spanned subspaces.

#### `TauCeti.singularValues_sinThetaMap`

Identifies the singular values of the sine/cross-projection operator with Tau Ceti principalSines, the principal-angle sine sequence.

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

**Elaborated signature** (statement pin: current)

~~~~lean
YuWangSamworth2015.theorem2_alignedFrame {p d r s : ℕ}
  (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p)
  (hd : d = s - r + 1) (V Vhat : Fin d → EuclideanSpace ℝ (Fin p))
  (hV : YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V)
  (hVhat : YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat) (Delta : ℝ)
  (hDelta : 0 < Delta) (hgap : YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta) :
  ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
    √(∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
      2 * √2 *
          min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
            (YuWangSamworth2015.frobeniusNorm (SigmaHat - Sigma)) /
        Delta
~~~~

Structural type hash `1136898647`, printed-type hash `eca00f43b9afb1ea`.

Statement closure: 6 project constant(s) unfolded, 0 project leaf/leaves, 33 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `YuWangSamworth2015.IsEigenvectorBlock`, `YuWangSamworth2015.SourcePopulationGap`, `YuWangSamworth2015.PopulationBoundaryGap`, `TauCeti.UnitarilyInvariantSeminorm.frobenius`, `TauCeti.UnitarilyInvariantSeminorm`
Boundary vocabulary: `Nat`, `LinearMap`, `Real`, `RingHom.id`, `EuclideanSpace`, `Fin`, `ENNReal`, `LinearMap.IsSymmetric`, `Eq`, `Exists`, `Matrix`, `And`, `Submonoid`, `Matrix.orthogonalGroup`, `Real.sqrt`, `Finset.sum`, `Finset.univ`, `Nat.cast`, `ContinuousLinearMap`, `LinearEquiv`, `LinearMap.toContinuousLinearMap`, `Orthonormal`, `LinearMap.IsSymmetric.eigenvalues`, `Or`, `RCLike`, `NormedAddCommGroup`, `InnerProductSpace`, `FiniteDimensional`, `Module.finrank`, `OrthonormalBasis`, `stdOrthonormalBasis`, `LinearIsometryEquiv`, `LinearMap.comp`

<details><summary>Statement closure tree</summary>

~~~~text
YuWangSamworth2015.theorem2_alignedFrame  (theorem, YuWangSamworth2015/Symmetric/Theorem2.lean:404)
    YuWangSamworth2015.theorem2_alignedFrame {p d r s : ℕ}
      (Sigma SigmaHat : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
      (hSigma : Sigma.IsSymmetric) (hSigmaHat : SigmaHat.IsSymmetric) (hr : r ≤ s) (hs : s < p)
      (hd : d = s - r + 1) (V Vhat : Fin d → EuclideanSpace ℝ (Fin p))
      (hV : YuWangSamworth2015.IsEigenvectorBlock Sigma hSigma hr hs hd V)
      (hVhat : YuWangSamworth2015.IsEigenvectorBlock SigmaHat hSigmaHat hr hs hd Vhat) (Delta : ℝ)
      (hDelta : 0 < Delta) (hgap : YuWangSamworth2015.SourcePopulationGap Sigma hSigma r s Delta) :
      ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
        √(∑ i, ‖∑ j, O j i • Vhat j - V i‖ ^ 2) ≤
          2 * √2 *
              min (√↑d * ‖LinearMap.toContinuousLinearMap (SigmaHat - Sigma)‖)
                (YuWangSamworth2015.frobeniusNorm (SigmaHat - Sigma)) /
            Delta
    hash: expr=1136898647 text=eca00f43b9afb1ea
  [type] YuWangSamworth2015.IsEigenvectorBlock  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:159)
      YuWangSamworth2015.IsEigenvectorBlock {p d r s : ℕ}
        (Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
        (hr : r ≤ s) (hs : s < p) (hd : d = s - r + 1) (V : Fin d → EuclideanSpace ℝ (Fin p)) : Prop
      hash: expr=1106865433 text=ffe3502345f67ce2
  [type] YuWangSamworth2015.SourcePopulationGap  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:279)
      YuWangSamworth2015.SourcePopulationGap {p : ℕ}
        (Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
        (r s : ℕ) (Delta : ℝ) : Prop
      hash: expr=1183521196 text=c73678dcf8b912e0
    [body] YuWangSamworth2015.PopulationBoundaryGap  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:219)
        YuWangSamworth2015.PopulationBoundaryGap {p : ℕ}
          (Sigma : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (hSigma : Sigma.IsSymmetric)
          (r s : ℕ) (Delta : ℝ) : Prop
        hash: expr=1183521196 text=c73678dcf8b912e0
  [type] YuWangSamworth2015.frobeniusNorm  (def, YuWangSamworth2015/Symmetric/Theorem2.lean:342)
      YuWangSamworth2015.frobeniusNorm {p : ℕ}
        (A : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) : ℝ
      hash: expr=2597927890 text=33f958e470c75938
    [body] TauCeti.UnitarilyInvariantSeminorm.frobenius  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:573)
        TauCeti.UnitarilyInvariantSeminorm.frobenius.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
          TauCeti.UnitarilyInvariantSeminorm 𝕜 E
        hash: expr=3446404092 text=20e49e15f61e4e69
      [type] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
          TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
          field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
          field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
          field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
          field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
          hash: expr=2499593303 text=2e9a12d567f1324f

6 project constant(s) unfolded, 0 project leaf/leaves, 33 boundary constant(s), 170 instance/projection constant(s)
boundary: Nat, LinearMap, Real, RingHom.id, EuclideanSpace, Fin, ENNReal, LinearMap.IsSymmetric, Eq, Exists, Matrix, And, Submonoid, Matrix.orthogonalGroup, Real.sqrt, Finset.sum, Finset.univ, Nat.cast, ContinuousLinearMap, LinearEquiv, LinearMap.toContinuousLinearMap, Orthonormal, LinearMap.IsSymmetric.eigenvalues, Or, RCLike, NormedAddCommGroup, InnerProductSpace, FiniteDimensional, Module.finrank, OrthonormalBasis, stdOrthonormalBasis, LinearIsometryEquiv, LinearMap.comp
~~~~

</details>

### Supporting scope declarations

- `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_real_le` — elaborated; source located
- `YuWangSamworth2015.yuWangSamworth_alignedFrame_block_le` — elaborated; source located

### Local semantic dictionary

#### `YuWangSamworth2015.isEigenvectorBlock_iff`

Expands the supplied population and sample eigenvector blocks into orthonormality plus their ordered eigenvector equations.

#### `YuWangSamworth2015.sourcePopulationGap_iff`

Characterizes the source Delta itself as the exact finite population boundary minimum, with an explicit full-space +infinity endpoint case.

#### `YuWangSamworth2015.populationBoundaryGap_iff`

Expands the lower-bound predicate used inside SourcePopulationGap into the two population-only boundary inequalities and shows that no sample-gap condition is hidden.

#### `YuWangSamworth2015.frobeniusNorm`

Reducible source-facing abbreviation for the existing Frobenius seminorm, applied directly to SigmaHat-Sigma in the aligned-frame bound.

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The second conclusion has the same real symmetric matrices, consecutive eigenvector blocks, and population-only gap as the first. | theorem2_alignedFrame repeats the same Sigma, SigmaHat, hr, hs, hd, IsEigenvectorBlock, Delta>0, and exact SourcePopulationGap mathematical hypotheses as theorem2_sinTheta. The perturbation Frobenius term is written directly as `frobeniusNorm (SigmaHat - Sigma)`. | claimed_exact |
| There exists O-hat in O(d). | The conclusion existentially returns O : Matrix (Fin d) (Fin d) Real with O in Matrix.orthogonalGroup (Fin d) Real. | claimed_exact |
| V-hat O-hat is compared with the supplied V. | The left side is sqrt(sum_i \|\|sum_j O j i * Vhat j - V i\|\|^2), using exactly the V and Vhat arguments from the hypotheses. | claimed_exact |
| The constant is 2^(3/2) with the same minimum numerator and Delta denominator. | The conclusion is 2 * sqrt 2 * min(sqrt d * \|\|SigmaHat-Sigma\|\|op, frobeniusNorm (SigmaHat-Sigma)) / Delta; the local semantic dictionary expands frobeniusNorm to the existing Frobenius seminorm. | claimed_exact |

**Review note.** The aligned headline wrapper exposes the orthogonal matrix and aligned frame distance directly and writes the source perturbation Frobenius norm as the reducible `frobeniusNorm (SigmaHat - Sigma)` application.

**Next action.** None.
