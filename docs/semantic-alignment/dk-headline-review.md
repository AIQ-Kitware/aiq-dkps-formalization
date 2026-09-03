# Semantic alignment review packet

This packet is generated from curated semantic-review fields in the source censuses. Human-written Lean headers are structural source evidence. Compiler output, when present, is elaborator-backed evidence about the Lean surface. The source-to-Lean correspondence remains the census author's explicit review claim.

**Elaborator evidence:** statement sidecar with 829 record(s), toolchain `leanprover/lean4:v4.34.0-rc1`. Signatures, hashes and closures below are read from the elaborated environment, not from source text.

## C. Davis and W. M. Kahan, The Rotation of Eigenvectors by a Perturbation. III, SIAM J. Numer. Anal. 7(1), 1970, 1–46.: Davis--Kahan single-angle sin theta theorem

The Section 2 sin-theta theorem: interval/exterior spectral separation controls the directed sine of the subspace angle by the residual, with sharp factor one.

### Normalized source statement

**Setup**
- A0 is the trial/compressed self-adjoint operator, Lambda1 is the complementary exact self-adjoint block, R is the residual, and Theta0 is the directed angle from the trial subspace to the exact subspace.

**Hypotheses**
- There are beta <= alpha and delta > 0 such that spec(A0) is contained in [beta, alpha] and spec(Lambda1) avoids (beta-delta, alpha+delta), or the same interval/exterior condition with A0 and Lambda1 interchanged.
- The separating interval may be half-infinite: the source states that the spectral intervals in the gap hypotheses may be half-infinite and the remaining spectra unbounded, so the ordered semibounded configurations are part of the printed hypothesis and not a later generalization.
- The norm is an arbitrary source unitary-invariant norm and the residual belongs to its norm ideal whenever that norm is finite.

**Conclusions**
- delta * ||sin Theta0|| <= ||R||.

**Scope**
- The paper states the result in finite and infinite dimension, over real or complex Hilbert spaces.
- The unbounded self-adjoint extension is included when the domain condition holds and the residual/norm expression is bounded and meaningful.

### Canonical Lean declarations

#### `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:343`

~~~~lean
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem sinTheta_unbounded_formGap_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex.{v} {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F)
  (Λ₁ : G →ₗ.[ℂ] G) (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
  (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
  (htrial : DavisKahan1970.IsTrialResidual A A₀ E₀ R)
  (hexact : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁) {δ : ℝ} (hδ : 0 < δ)
  (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) (hR : N.Mem R) :
  N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ∧
    δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ≤
      N.gauge R
~~~~

Structural type hash `3277617206`, printed-type hash `6abf61c51dee3066`.

Statement closure: 22 project constant(s) unfolded, 0 project leaf/leaves, 51 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.diagOp`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.ApproximationNumber.approximationSingularValue`, `ContinuousLinearMap.approximationNumber`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.Sylvester.HasUnboundedSylvesterKyFan`, `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `IsSelfAdjoint`, `Real`, `And`, `ContinuousLinearMap.comp`, `ContinuousLinearMap.id`, `LinearIsometryEquiv`, `starRingEnd`, `ContinuousLinearMap.adjoint`, `Nat`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `Subtype`, `Submodule`, `LinearPMap.toFun'`, `Ne`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `iSup`, `ENNReal.ofReal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `InnerProductSpace.rankOne`, `Exists`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `NormedSpace`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`

<details><summary>Statement closure tree</summary>

~~~~text
DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:326)
    DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex.{v} {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F]
      [InnerProductSpace ℂ F] [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
      [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F)
      (Λ₁ : G →ₗ.[ℂ] G) (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
      (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
      (htrial : DavisKahan1970.IsTrialResidual A A₀ E₀ R)
      (hexact : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁) {δ : ℝ} (hδ : 0 < δ)
      (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) (hR : N.Mem R) :
      N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ∧
        δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ≤
          N.gauge R
    hash: expr=3277617206 text=6abf61c51dee3066
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] DavisKahan1970.IsTrialResidual  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:67)
      DavisKahan1970.IsTrialResidual.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E)
        (A₀ : F →ₗ.[𝕜] F) (E₀ R : F →L[𝕜] E) : Prop
      field isometry : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E}, DavisKahan1970.IsTrialResidual A A₀ E₀ R → TauCeti.DavisKahan.IsometricEmbedding E₀
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E}, DavisKahan1970.IsTrialResidual A A₀ E₀ R → ∀ (x : ↥A₀.domain), E₀ ↑x ∈ A.domain
      field residualEquation : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E} (self : DavisKahan1970.IsTrialResidual A A₀ E₀ R) (x : ↥A₀.domain), ↑A ⟨E₀ ↑x, ⋯⟩ - E₀ (↑A₀ x) = R ↑x
      hash: expr=697366030 text=7086524c853f1414
    [body] TauCeti.DavisKahan.IsometricEmbedding  (def, DavisKahan/BoundedOperator/Compat.lean:107)
        TauCeti.DavisKahan.IsometricEmbedding.{u_1, u_2, u_3} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F : Type u_3} [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (X : F →L[𝕜] E) : Prop
        hash: expr=2691607086 text=02c1b372cca3865c
  [type] DavisKahan1970.IsExactSpectralDecomposition  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:146)
      DavisKahan1970.IsExactSpectralDecomposition.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E G H : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup G]
        [InnerProductSpace 𝕜 G] [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
        [CompleteSpace H] (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) : Prop
      field desiredIsometry : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → TauCeti.DavisKahan.IsometricEmbedding F₀
      field complementIsometry : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → TauCeti.DavisKahan.IsometricEmbedding F₁
      field orthogonal : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → ContinuousLinearMap.adjoint F₀ ∘SL F₁ = 0
      field complete : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → F₀ ∘SL ContinuousLinearMap.adjoint F₀ + F₁ ∘SL ContinuousLinearMap.adjoint F₁ = ContinuousLinearMap.id 𝕜 E
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → ∀ (y : ↥Λ₁.domain), F₁ ↑y ∈ A.domain
      field intertwines : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E} (self : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁) (y : ↥Λ₁.domain), ↑A ⟨F₁ ↑y, ⋯⟩ = F₁ (↑Λ₁ y)
      hash: expr=3953242937 text=f545b1a4a840a6d9
    [body] TauCeti.DavisKahan.IsometricEmbedding  (above)
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

22 project constant(s) unfolded, 0 project leaf/leaves, 51 boundary constant(s), 170 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, ContinuousLinearMap, IsSelfAdjoint, Real, And, ContinuousLinearMap.comp, ContinuousLinearMap.id, LinearIsometryEquiv, starRingEnd, ContinuousLinearMap.adjoint, Nat, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, Subtype, Submodule, LinearPMap.toFun', Ne, ENNReal.toReal, FiniteDimensional, LinearMap, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set, Set.Icc, Set.ofPred, AddMonoidHom, iSup, ENNReal.ofReal, Finset.sum, Finset.univ, RCLike.ofReal, InnerProductSpace.rankOne, Exists, NontriviallyNormedField, SeminormedAddCommGroup, NormedSpace, iInf, Cardinal, LinearMap.rank, Nat.cast
~~~~

</details>

#### `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:457`

~~~~lean
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem sinTheta_unbounded_formGap_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real.{v} {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F)
  (Λ₁ : G →ₗ.[ℝ] G) (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
  (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
  (htrial : DavisKahan1970.IsTrialResidual A A₀ E₀ R)
  (hexact : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁) {δ : ℝ} (hδ : 0 < δ)
  (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) (hR : N.Mem R) :
  N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ∧
    δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ≤
      N.gauge R
~~~~

Structural type hash `295553877`, printed-type hash `356c5a6af70fc875`.

Statement closure: 22 project constant(s) unfolded, 0 project leaf/leaves, 51 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.diagOp`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.ApproximationNumber.approximationSingularValue`, `ContinuousLinearMap.approximationNumber`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.Sylvester.HasUnboundedSylvesterKyFan`, `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `IsSelfAdjoint`, `And`, `ContinuousLinearMap.comp`, `ContinuousLinearMap.id`, `LinearIsometryEquiv`, `starRingEnd`, `ContinuousLinearMap.adjoint`, `Nat`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `Subtype`, `Submodule`, `LinearPMap.toFun'`, `Ne`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `iSup`, `ENNReal.ofReal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `InnerProductSpace.rankOne`, `Exists`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `NormedSpace`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`

<details><summary>Statement closure tree</summary>

~~~~text
DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:452)
    DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real.{v} {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
      [InnerProductSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
      [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F)
      (Λ₁ : G →ₗ.[ℝ] G) (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
      (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
      (htrial : DavisKahan1970.IsTrialResidual A A₀ E₀ R)
      (hexact : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁) {δ : ℝ} (hδ : 0 < δ)
      (hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ) (hR : N.Mem R) :
      N.Mem ((ContinuousLinearMap.id ℝ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ∧
        δ * N.gauge ((ContinuousLinearMap.id ℝ E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ≤
          N.gauge R
    hash: expr=295553877 text=356c5a6af70fc875
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] DavisKahan1970.IsTrialResidual  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:67)
      DavisKahan1970.IsTrialResidual.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E)
        (A₀ : F →ₗ.[𝕜] F) (E₀ R : F →L[𝕜] E) : Prop
      field isometry : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E}, DavisKahan1970.IsTrialResidual A A₀ E₀ R → TauCeti.DavisKahan.IsometricEmbedding E₀
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E}, DavisKahan1970.IsTrialResidual A A₀ E₀ R → ∀ (x : ↥A₀.domain), E₀ ↑x ∈ A.domain
      field residualEquation : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] {A : E →ₗ.[𝕜] E} {A₀ : F →ₗ.[𝕜] F} {E₀ R : F →L[𝕜] E} (self : DavisKahan1970.IsTrialResidual A A₀ E₀ R) (x : ↥A₀.domain), ↑A ⟨E₀ ↑x, ⋯⟩ - E₀ (↑A₀ x) = R ↑x
      hash: expr=697366030 text=7086524c853f1414
    [body] TauCeti.DavisKahan.IsometricEmbedding  (def, DavisKahan/BoundedOperator/Compat.lean:107)
        TauCeti.DavisKahan.IsometricEmbedding.{u_1, u_2, u_3} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F : Type u_3} [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (X : F →L[𝕜] E) : Prop
        hash: expr=2691607086 text=02c1b372cca3865c
  [type] DavisKahan1970.IsExactSpectralDecomposition  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean:146)
      DavisKahan1970.IsExactSpectralDecomposition.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E G H : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup G]
        [InnerProductSpace 𝕜 G] [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
        [CompleteSpace H] (A : E →ₗ.[𝕜] E) (Λ₁ : G →ₗ.[𝕜] G) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) : Prop
      field desiredIsometry : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → TauCeti.DavisKahan.IsometricEmbedding F₀
      field complementIsometry : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → TauCeti.DavisKahan.IsometricEmbedding F₁
      field orthogonal : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → ContinuousLinearMap.adjoint F₀ ∘SL F₁ = 0
      field complete : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → F₀ ∘SL ContinuousLinearMap.adjoint F₀ + F₁ ∘SL ContinuousLinearMap.adjoint F₁ = ContinuousLinearMap.id 𝕜 E
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}, DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ → ∀ (y : ↥Λ₁.domain), F₁ ↑y ∈ A.domain
      field intertwines : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E] [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G] [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E} (self : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁) (y : ↥Λ₁.domain), ↑A ⟨F₁ ↑y, ⋯⟩ = F₁ (↑Λ₁ y)
      hash: expr=3953242937 text=f545b1a4a840a6d9
    [body] TauCeti.DavisKahan.IsometricEmbedding  (above)
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

22 project constant(s) unfolded, 0 project leaf/leaves, 51 boundary constant(s), 171 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, LinearPMap, RingHom.id, ContinuousLinearMap, IsSelfAdjoint, And, ContinuousLinearMap.comp, ContinuousLinearMap.id, LinearIsometryEquiv, starRingEnd, ContinuousLinearMap.adjoint, Nat, Complex, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, Subtype, Submodule, LinearPMap.toFun', Ne, ENNReal.toReal, FiniteDimensional, LinearMap, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set, Set.Icc, Set.ofPred, AddMonoidHom, iSup, ENNReal.ofReal, Finset.sum, Finset.univ, RCLike.ofReal, InnerProductSpace.rankOne, Exists, NontriviallyNormedField, SeminormedAddCommGroup, NormedSpace, iInf, Cardinal, LinearMap.rank, Nat.cast
~~~~

</details>

### Supporting scope declarations

- `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike` — elaborated; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real_ofRCLike` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_ofComponents_rclike` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_rclike` — elaborated; source located
- `DavisKahan1970.sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_idealFamily_rclike` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_spectralSubspace_complex` — not in environment; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_spectralSubspace_real` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace_complex` — not in environment; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex_ofRCLike_conforms` — elaborated; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_real_ofRCLike_conforms` — elaborated; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike` — elaborated; source located

### Local semantic dictionary

#### `DavisKahan1970.isTrialResidual_iff`

Expands the compact trial-residual hypothesis into the trial isometry, domain transport, and exact residual identity R = A E0 - E0 A0.

#### `DavisKahan1970.isExactSpectralDecomposition_iff`

Expands the compact exact-space hypothesis into isometric F0/F1 coordinates, orthogonality, completeness, domain transport, and A F1 = F1 Lambda1.

#### `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction`

Implementation structure behind the public theorem spelling UnitaryInvariantNorm: the dimension-coherent normalized unitary-invariant norm quantified over by Davis--Kahan.

#### `TauCeti.DavisKahan.Sylvester.HasUnboundedSylvesterKyFan`

Scalar-field proof capability used to keep one theorem generic over RCLike. The repository provides instances for both source scalar fields, R and C; this is implementation evidence rather than an additional paper hypothesis.

#### `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`

Approximation-number min--max capability needed by the universal norm machinery. It has proved R and C instances and is not an extra source restriction.

#### `LinearPMap`

Mathlib's partial linear map: the repository representation of the paper's possibly unbounded self-adjoint operators. Dense domain, closed graph and self-adjointness are hypotheses of the theorems that need them, not fields of the carrier; the bundled DKPS record that once played this role was deleted on 2026-08-28.

#### `TauCeti.LinearPMap.realSpectrum`

Real spectrum of a self-adjoint partial/closed operator; the interval/exterior alternative itself remains literal in the canonical theorem.

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical theorem is generic over 𝕜 with [RCLike 𝕜]. Its two scalar capability binders have proved instances for both source scalar fields ℝ and ℂ. | claimed_exact |
| A, A0, and Lambda1 are self-adjoint; E0 is the trial coordinate map and F0,F1 are orthogonal exact-space coordinates. | A, A₀, Λ₁, E₀, F₀, and F₁ are explicit arguments. Self-adjointness is literal; IsTrialResidual and IsExactSpectralDecomposition are expanded immediately in the local semantic dictionary. | claimed_exact |
| R = A E0 - E0 A0 on the operator domain, while F1 intertwines Lambda1 with A. | These clauses are exactly the residualEquation and intertwines components exposed by isTrialResidual_iff and isExactSpectralDecomposition_iff, together with their domain-transport hypotheses. | claimed_exact |
| sin Theta0 is the directed sine block from the trial subspace to the exact subspace. | sinTheta₀ is an explicit theorem parameter and hSinTheta₀ literally states sinTheta₀ = (I - F₀ F₀†) E₀. No named definition hides this identification. | claimed_exact |
| For beta <= alpha and delta > 0, one spectrum lies in [beta,alpha] and the other avoids (beta-delta,alpha+delta), with the roles interchangeable. | hβα and hδ are explicit, and hspectral is literally the disjunction of the two real-spectrum inclusions. | claimed_exact |
| The norm is an arbitrary source unitary-invariant norm and R has finite norm. | N : UnitaryInvariantNorm and hR : N.Mem R appear directly. UnitaryInvariantNorm is the existing public source-facing name for the audited SymmetricNormingFunction implementation structure. | claimed_exact |
| delta \|\|sin Theta0\|\| <= \|\|R\|\|. | The text after the theorem colon is exactly δ * N.gauge sinTheta₀ <= N.gauge R. The supporting sinTheta_unbounded_intervalExterior_symmetricNorming_rclike theorem additionally certifies N.Mem sinTheta₀ after rewriting by hSinTheta₀. | claimed_exact |
| Infinite-dimensional and unbounded self-adjoint scope. | There is no FiniteDimensional hypothesis; A, A₀, and Λ₁ are `LinearPMap` values and the two expanded setup predicates carry the required domain conditions. | claimed_exact |

**Review note.** The canonical review declaration is also the intended paper-display declaration. It names sinTheta₀ as a theorem parameter but gives its concrete projection-block formula by a literal equality hypothesis in the same signature, so the claim after the colon is a one-to-one rendering of the printed inequality without an opaque angle definition. Only the domain-heavy trial and exact-coordinate setup is bundled, and both bundles are fully expanded by characteristic theorems in the local semantic dictionary. The stronger generic theorem remains supporting evidence for norm-ideal membership and the implementation proof bridge. CANONICAL WITNESS CORRECTED 2026-08-31. The row named `sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` as the exact source match. That was wrong on two counts: it carries only the bounded interval/exterior branch of the gap, while the source permits half-infinite separating intervals, and it drops the ideal-membership half of the conclusion. The canonical witness is now `DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike`, added the same day: scalar-generic over `RCLike`, unbounded `LinearPMap` ambient operator, arbitrary Hilbert dimension, the whole `FormBoundedSylvesterGap` (interval/exterior plus both ordered semibounded configurations), an arbitrary `SymmetricNormingFunction`, and both conclusions. It is proved by taking the gap directly into the Ky-Fan-to-paper-norm promotion the interval/exterior theorem already ran, so it is a repackaging rather than a new argument, and the interval/exterior form is now a one-line consequence of it. `..._complex_ofRCLike` and `..._real_ofRCLike` are the compiled conformance checks: each restates the corresponding fixed-field endpoint's type verbatim and discharges it by the generic theorem with no adapter. The fixed-field endpoints remain as corroborating full-source witnesses and the interval/exterior theorem as a presentation specialization. The two `RCLike` capability classes in the generic signature are proof capabilities with instances for both source fields, not printed source hypotheses. CONFORMANCE TIED BY NAME 2026-08-31. The `_ofRCLike` wrappers restate a type, and a restatement cannot notice if the declaration it mirrors changes. `..._ofRCLike_conforms` closes that: an equation between two constants elaborates only when both sides have the same type, so it asserts exactly that the restatement is the fixed-field endpoint's type, and `rfl` discharges it by proof irrelevance. It is a type-level check by design and says nothing about the two proofs.

2026-08-31 (second pass): canonical declarations follow the result inventory's `canonical_evidence`. Demoted to supporting: DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike -- the scalar-generic form carries proof-capability instance binders that the printed statement does not, and the two fixed-field endpoints state the result at the paper's two fields with no such binder.

**Next action.** No hostile-review hole is currently recorded for this source passage. Preserve exact source scope and re-audit if the distributable source specification changes.

### Derived review variants

#### Sharp Davis--Kahan projector-difference theorem

The canonical projector form of the factor-one sin-theta estimate: for two reducing high-side subspaces separated from their complements by the same gap g, ||P_U - P_W|| <= ||B-A||/g.

**Provenance.** Derived review target: this is the sharp projector formulation obtained from the Davis--Kahan sin-theta theorem together with the two-projection norm identity, not a fifth separately printed Section 2 theorem.

### Normalized source statement

**Setup**
- A and B are self-adjoint operators; U and W are reducing selected subspaces; P_U and P_W are their orthogonal projections.

**Hypotheses**
- There is a cut c and g>0 such that U and W lie on the high side c+g while U^perp and W^perp lie on the low side c.

**Conclusions**
- ||P_U - P_W|| <= ||B-A|| / g.

**Scope**
- This packet asks the reviewer to validate the mathematical provenance from the source sin-theta theorem, not to treat this as a separately printed Davis--Kahan theorem.

### Canonical Lean declarations

#### `Submodule.opNorm_starProjection_sub_le_of_coercive`

**Human-written Lean statement**

`ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean:59`

~~~~lean
variable {𝕜 H : Type*} [RCLike 𝕜]
theorem opNorm_starProjection_sub_le_of_coercive
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUlo : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hWlo : ∀ x ∈ Wᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g
~~~~

**Elaborated signature** (statement pin: unpinned)

~~~~lean
Submodule.opNorm_starProjection_sub_le_of_coercive.{u_1, u_2} {𝕜 : Type u_1} {H : Type u_2}
  [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] {A B : H →L[𝕜] H}
  (hA : (↑A).IsSymmetric) (hB : (↑B).IsSymmetric) {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection]
  [W.HasOrthogonalProjection] (hU : A.Reduces U) (hW : B.Reduces W) {c g : ℝ} (hg : 0 < g)
  (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x))
  (hUlo : ∀ x ∈ Uᗮ, RCLike.re (inner 𝕜 (A x) x) ≤ c * ‖x‖ ^ 2)
  (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B x) x))
  (hWlo : ∀ x ∈ Wᗮ, RCLike.re (inner 𝕜 (B x) x) ≤ c * ‖x‖ ^ 2) :
  ‖U.starProjection - W.starProjection‖ ≤ ‖B - A‖ / g
~~~~

Structural type hash `1804902662`, printed-type hash `fe1a949cdb3b8cc9`.

Statement closure: 1 project constant(s) unfolded, 0 project leaf/leaves, 15 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `ContinuousLinearMap.Reduces`
Boundary vocabulary: `RCLike`, `NormedAddCommGroup`, `InnerProductSpace`, `CompleteSpace`, `ContinuousLinearMap`, `RingHom.id`, `LinearMap.IsSymmetric`, `Submodule`, `Submodule.HasOrthogonalProjection`, `Real`, `Nat`, `AddMonoidHom`, `Submodule.orthogonal`, `Submodule.starProjection`, `And`

<details><summary>Statement closure tree</summary>

~~~~text
Submodule.opNorm_starProjection_sub_le_of_coercive  (theorem, ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Projector.lean:48)
    Submodule.opNorm_starProjection_sub_le_of_coercive.{u_1, u_2} {𝕜 : Type u_1} {H : Type u_2}
      [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] {A B : H →L[𝕜] H}
      (hA : (↑A).IsSymmetric) (hB : (↑B).IsSymmetric) {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection]
      [W.HasOrthogonalProjection] (hU : A.Reduces U) (hW : B.Reduces W) {c g : ℝ} (hg : 0 < g)
      (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x))
      (hUlo : ∀ x ∈ Uᗮ, RCLike.re (inner 𝕜 (A x) x) ≤ c * ‖x‖ ^ 2)
      (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B x) x))
      (hWlo : ∀ x ∈ Wᗮ, RCLike.re (inner 𝕜 (B x) x) ≤ c * ‖x‖ ^ 2) :
      ‖U.starProjection - W.starProjection‖ ≤ ‖B - A‖ / g
    hash: expr=1804902662 text=fe1a949cdb3b8cc9
  [type] ContinuousLinearMap.Reduces  (def, ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean:41)
      ContinuousLinearMap.Reduces.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop
      hash: expr=948805368 text=3ab3db7a55bae951

1 project constant(s) unfolded, 0 project leaf/leaves, 15 boundary constant(s), 70 instance/projection constant(s)
boundary: RCLike, NormedAddCommGroup, InnerProductSpace, CompleteSpace, ContinuousLinearMap, RingHom.id, LinearMap.IsSymmetric, Submodule, Submodule.HasOrthogonalProjection, Real, Nat, AddMonoidHom, Submodule.orthogonal, Submodule.starProjection, And
~~~~

</details>

### Supporting scope declarations

- `TauCeti.opNorm_spectralSubspace_sub_le` — elaborated; source located

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| A common two-sided gap g separates each selected subspace from its orthogonal complement. | The four quadratic-form inequalities around c and c+g are written literally in the canonical theorem. | derived |
| Projector distance is bounded with factor one. | The conclusion is \|\|U.starProjection - W.starProjection\|\| <= \|\|B-A\|\| / g. | derived |

## C. Davis and W. M. Kahan, The Rotation of Eigenvectors by a Perturbation. III, SIAM J. Numer. Anal. 7(1), 1970, 1–46.: Davis--Kahan single-angle tan theta theorem

The Section 2 tan-theta theorem: an ordered one-sided gap plus the Rayleigh--Ritz/off-diagonal condition gives the directed residual and ambient perturbation tangent bounds with sharp factor one.

### Normalized source statement

**Setup**
- A0 is the Rayleigh--Ritz compression on the trial subspace, Lambda1 is the unwanted exact block, R is the Ritz residual, H is the full perturbation, and Theta0/Theta are directed/ambient angles.

**Hypotheses**
- spec(A0) is contained in [beta,alpha], spec(Lambda1) is contained in [alpha+delta,infinity), and delta>0.
- H0=0, equivalently A0 is the Rayleigh--Ritz compression in the paper setup.
- For the ambient tangent statement, the standing Section 3 direct-rotation existence condition is required whenever the angle norm would otherwise be undefined.

**Conclusions**
- delta * ||tan Theta0|| <= ||R||.
- delta * ||tan Theta|| <= ||H||.

**Scope**
- Every source unitary-invariant norm; finite/infinite dimensional and real/complex scope, with the appendix unbounded extension when the residual/perturbation is bounded.  The Appendix's tangent extension is specifically that BOTH A0 and Lambda1 may be unbounded, so the canonical directed and ambient witnesses must both carry a Ritz compression that is itself a densely defined partial map; a bounded compression under an unbounded ambient operator is a specialization, not this scope.

### Canonical Lean declarations

#### `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:543`

~~~~lean
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem tanTheta_ambient_unboundedRitz_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge H
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_complex.{u} {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℂ] E}
  {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace ↥U]
  (D : TauCeti.DavisKahan.UnboundedRitzPair A U) (hV : TauCeti.DavisKahan.ReducingComplement A V)
  (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) {alpha delta : ℝ} (hdelta : 0 < delta)
  (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
  (hUnwanted :
    ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A ⟨y, hy⟩) y))
  (h35 : TauCeti.DavisKahan.CrossedDefectsEquivalent U V)
  (hResidual : D.trial.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL) (hMem : N.Mem H) :
  N.Mem (TauCeti.DavisKahanExt.tanAngleOperatorC U V) ∧
    delta * N.gauge (TauCeti.DavisKahanExt.tanAngleOperatorC U V) ≤ N.gauge H
~~~~

Structural type hash `3755748480`, printed-type hash `3ea82407819fc25d`.

Statement closure: 25 project constant(s) unfolded, 0 project leaf/leaves, 58 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.UnboundedRitzPair`, `TauCeti.DavisKahan.ReducingComplement`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action`, `TauCeti.DavisKahan.halmosSourceDefect`, `TauCeti.DavisKahan.halmosTargetDefect`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.DavisKahanExt.angleOperatorC`, `TauCeti.diagOp`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.DavisKahanExt.sinAngleOperatorC`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `ContinuousLinearMap.modulus`, `TauCeti.ApproximationNumber.approximationSingularValue`, `ContinuousLinearMap.approximationNumber`
Dictionary definitions this statement never reaches: `TauCeti.principalTangents`, `TauCeti.ritzResidual`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `Submodule`, `Submodule.HasOrthogonalProjection`, `Subtype`, `ContinuousLinearMap`, `IsSelfAdjoint`, `Real`, `Submodule.orthogonal`, `Nat`, `AddMonoidHom`, `LinearPMap.toFun'`, `Eq`, `ContinuousLinearMap.comp`, `Submodule.starProjection`, `Submodule.subtypeL`, `And`, `EuclideanSpace`, `Fin`, `ENNReal`, `EuclideanSpace.basisFun`, `RCLike`, `Nonempty`, `LinearIsometryEquiv`, `Ne`, `cfc`, `Real.tan`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `iSup`, `ENNReal.ofReal`, `Real.arcsin`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.adjoint`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `NormedSpace`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:535)
    TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_complex.{u} {E : Type u}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℂ] E}
      {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace ↥U]
      (D : TauCeti.DavisKahan.UnboundedRitzPair A U) (hV : TauCeti.DavisKahan.ReducingComplement A V)
      (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) {alpha delta : ℝ} (hdelta : 0 < delta)
      (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
      (hUnwanted :
        ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A ⟨y, hy⟩) y))
      (h35 : TauCeti.DavisKahan.CrossedDefectsEquivalent U V)
      (hResidual : D.trial.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL) (hMem : N.Mem H) :
      N.Mem (TauCeti.DavisKahanExt.tanAngleOperatorC U V) ∧
        delta * N.gauge (TauCeti.DavisKahanExt.tanAngleOperatorC U V) ≤ N.gauge H
    hash: expr=3755748480 text=3ea82407819fc25d
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.UnboundedRitzPair  (structure, DavisKahan/TanTheta/RitzPair.lean:53)
      TauCeti.DavisKahan.UnboundedRitzPair.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
        [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type v
      field trial : {𝕜 : Type u} → [inst : RCLike 𝕜] → {H : Type v} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {A : H →ₗ.[𝕜] H} → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.UnboundedRitzPair A Z → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z
      field mem_domain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), ↑↑z ∈ A.domain
      field action_eq : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), self.trial.action z = ↑A ⟨↑↑z, ⋯⟩
      hash: expr=1041214427 text=5389305b6685c32e
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (structure, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:90)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜]
          {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (Z : Submodule 𝕜 H)
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type u
        field compression : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →ₗ.[𝕜] ↥Z
        field compression_isSelfAdjoint : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z), IsSelfAdjoint self.compression
        field residual : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →L[𝕜] H
        field residual_orthogonal : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z) (z z' : ↥Z), inner 𝕜 (self.residual z) ↑z' = 0
        hash: expr=1788257613 text=ba6c9f3809856f0d
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action  (def, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:114)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action.{u, u_1} {𝕜 : Type u_1}
          [RCLike 𝕜] {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H}
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z]
          (D : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z)
          (z : ↥D.compression.domain) : H
        hash: expr=957381741 text=95550eba98fc6d55
      [type] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (above)
  [type] TauCeti.DavisKahan.ReducingComplement  (structure, DavisKahan/TanTheta/RitzPair.lean:68)
      TauCeti.DavisKahan.ReducingComplement.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (V : Submodule 𝕜 H)
        [V.HasOrthogonalProjection] : Prop
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection], TauCeti.DavisKahan.ReducingComplement A V → ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain
      field commutes : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection] (self : TauCeti.DavisKahan.ReducingComplement A V) (x : ↥A.domain), Vᗮ.starProjection (↑A x) = ↑A ⟨Vᗮ.starProjection ↑x, ⋯⟩
      hash: expr=2182083140 text=f405375b390dedf0
  [type] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
      TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
      hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.CrossedDefectsEquivalent  (def, DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean:61)
      TauCeti.DavisKahan.CrossedDefectsEquivalent.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {H : Type u}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : Prop
      hash: expr=3262849228 text=64f9facf027bbeea
    [body] TauCeti.DavisKahan.halmosSourceDefect  (def, DavisKahan/Geometry/Halmos/TwoProjections.lean:111)
        TauCeti.DavisKahan.halmosSourceDefect.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {H : Type u_2}
          [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) : Submodule 𝕜 H
        hash: expr=1773535531 text=175b124071948810
    [body] TauCeti.DavisKahan.halmosTargetDefect  (def, DavisKahan/Geometry/Halmos/TwoProjections.lean:115)
        TauCeti.DavisKahan.halmosTargetDefect.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {H : Type u_2}
          [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) : Submodule 𝕜 H
        hash: expr=1773535531 text=175b124071948810
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.tanAngleOperatorC  (def, DavisKahan/Geometry/Angle/TanAngleFunctionalCalculus.lean:74)
      TauCeti.DavisKahanExt.tanAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℂ] E
      hash: expr=187490045 text=178745a4708f5513
    [body] TauCeti.DavisKahanExt.angleOperatorC  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean:84)
        TauCeti.DavisKahanExt.angleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.sinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:38)
          TauCeti.DavisKahanExt.sinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
            ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
              [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
              [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
            hash: expr=299460441 text=f21cf18f7b7963ad
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

25 project constant(s) unfolded, 0 project leaf/leaves, 58 boundary constant(s), 213 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, Submodule, Submodule.HasOrthogonalProjection, Subtype, ContinuousLinearMap, IsSelfAdjoint, Real, Submodule.orthogonal, Nat, AddMonoidHom, LinearPMap.toFun', Eq, ContinuousLinearMap.comp, Submodule.starProjection, Submodule.subtypeL, And, EuclideanSpace, Fin, ENNReal, EuclideanSpace.basisFun, RCLike, Nonempty, LinearIsometryEquiv, Ne, cfc, Real.tan, ENNReal.toReal, FiniteDimensional, LinearMap, LinearMap.comp, OrthonormalBasis, Fin.lastCases, iSup, ENNReal.ofReal, Real.arcsin, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.adjoint, NontriviallyNormedField, SeminormedAddCommGroup, NormedSpace, iInf, Cardinal, LinearMap.rank, Nat.cast
~~~~

</details>

#### `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean:392`

~~~~lean
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
theorem tanTheta_ambient_unboundedRitz_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E}
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (tanAngleOperatorR U V) ∧
      delta * N.gauge (tanAngleOperatorR U V) ≤ N.gauge H
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_real.{v} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {U V : Submodule ℝ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E}
  (D : TauCeti.DavisKahan.UnboundedRitzPair A U) (hV : TauCeti.DavisKahan.ReducingComplement A V)
  (H : E →L[ℝ] E) (hH : IsSelfAdjoint H) {alpha delta : ℝ} (hdelta : 0 < delta)
  (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
  (hUnwanted : ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (↑A ⟨y, hy⟩) y)
  (h35 : TauCeti.DavisKahan.CrossedDefectsEquivalent U V)
  (hResidual : D.trial.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL) (hMem : N.Mem H) :
  N.Mem (TauCeti.DavisKahanExt.tanAngleOperatorR U V) ∧
    delta * N.gauge (TauCeti.DavisKahanExt.tanAngleOperatorR U V) ≤ N.gauge H
~~~~

Structural type hash `632860847`, printed-type hash `2b99dabf29e4fb9b`.

Statement closure: 33 project constant(s) unfolded, 1 project leaf/leaves, 67 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.UnboundedRitzPair`, `TauCeti.DavisKahan.ReducingComplement`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahanExt.tanAngleOperatorR`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action`, `TauCeti.DavisKahan.halmosSourceDefect`, `TauCeti.DavisKahan.halmosTargetDefect`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.RealComplexification.realPartOperator`, `TauCeti.RealComplexification`, `TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule`, `TauCeti.diagOp`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.RealComplexification.re`, `TauCeti.RealComplexification.ofReal`, `TauCeti.DavisKahanExt.angleOperatorC`, `TauCeti.RealComplexification.im`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.RealComplexification.mk`, `TauCeti.DavisKahanExt.sinAngleOperatorC`, `TauCeti.ApproximationNumber.approximationSingularValue`, `ContinuousLinearMap.modulus`, `ContinuousLinearMap.approximationNumber`, `TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedAmbientReal`
Dictionary definitions this statement never reaches: `TauCeti.principalTangents`, `TauCeti.ritzResidual`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `Submodule`, `Submodule.HasOrthogonalProjection`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `IsSelfAdjoint`, `Subtype`, `Submodule.orthogonal`, `Nat`, `LinearPMap.toFun'`, `Eq`, `ContinuousLinearMap.comp`, `Submodule.starProjection`, `Submodule.subtypeL`, `And`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `EuclideanSpace.basisFun`, `RCLike`, `AddMonoidHom`, `Nonempty`, `LinearIsometryEquiv`, `Ne`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `iSup`, `ENNReal.ofReal`, `LinearIsometry`, `LinearMap.mkContinuous`, `cfc`, `Real.tan`, `WithLp`, `Prod`, `Set.ofPred`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `AddCommGroup`, `Module`, `Module.ofMinimalAxioms`, `NormedSpace`, `Real.arcsin`, `SMul`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.adjoint`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean:381)
    TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_symmetricNorming_real.{v} {E : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {U V : Submodule ℝ E}
      [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E}
      (D : TauCeti.DavisKahan.UnboundedRitzPair A U) (hV : TauCeti.DavisKahan.ReducingComplement A V)
      (H : E →L[ℝ] E) (hH : IsSelfAdjoint H) {alpha delta : ℝ} (hdelta : 0 < delta)
      (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
      (hUnwanted : ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (↑A ⟨y, hy⟩) y)
      (h35 : TauCeti.DavisKahan.CrossedDefectsEquivalent U V)
      (hResidual : D.trial.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL) (hMem : N.Mem H) :
      N.Mem (TauCeti.DavisKahanExt.tanAngleOperatorR U V) ∧
        delta * N.gauge (TauCeti.DavisKahanExt.tanAngleOperatorR U V) ≤ N.gauge H
    hash: expr=632860847 text=2b99dabf29e4fb9b
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.UnboundedRitzPair  (structure, DavisKahan/TanTheta/RitzPair.lean:53)
      TauCeti.DavisKahan.UnboundedRitzPair.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
        [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type v
      field trial : {𝕜 : Type u} → [inst : RCLike 𝕜] → {H : Type v} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {A : H →ₗ.[𝕜] H} → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.UnboundedRitzPair A Z → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z
      field mem_domain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), ↑↑z ∈ A.domain
      field action_eq : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), self.trial.action z = ↑A ⟨↑↑z, ⋯⟩
      hash: expr=1041214427 text=5389305b6685c32e
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (structure, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:90)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜]
          {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (Z : Submodule 𝕜 H)
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type u
        field compression : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →ₗ.[𝕜] ↥Z
        field compression_isSelfAdjoint : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z), IsSelfAdjoint self.compression
        field residual : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →L[𝕜] H
        field residual_orthogonal : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z) (z z' : ↥Z), inner 𝕜 (self.residual z) ↑z' = 0
        hash: expr=1788257613 text=ba6c9f3809856f0d
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action  (def, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:114)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action.{u, u_1} {𝕜 : Type u_1}
          [RCLike 𝕜] {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H}
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z]
          (D : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z)
          (z : ↥D.compression.domain) : H
        hash: expr=957381741 text=95550eba98fc6d55
      [type] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (above)
  [type] TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedAmbientReal  (theorem, DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean:75)
      TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedAmbientReal.{v, u_1}
        {k : Type u_1} [RCLike k] {G : Type v} [NormedAddCommGroup G] [InnerProductSpace k G]
        [CompleteSpace G] (Z : Submodule k G) [Z.HasOrthogonalProjection] : CompleteSpace ↥Z
      hash: expr=2414728822 text=584bd57452ff4a83
  [type] TauCeti.DavisKahan.ReducingComplement  (structure, DavisKahan/TanTheta/RitzPair.lean:68)
      TauCeti.DavisKahan.ReducingComplement.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (V : Submodule 𝕜 H)
        [V.HasOrthogonalProjection] : Prop
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection], TauCeti.DavisKahan.ReducingComplement A V → ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain
      field commutes : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection] (self : TauCeti.DavisKahan.ReducingComplement A V) (x : ↥A.domain), Vᗮ.starProjection (↑A x) = ↑A ⟨Vᗮ.starProjection ↑x, ⋯⟩
      hash: expr=2182083140 text=f405375b390dedf0
  [type] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
      TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
      hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.CrossedDefectsEquivalent  (def, DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean:61)
      TauCeti.DavisKahan.CrossedDefectsEquivalent.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {H : Type u}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : Prop
      hash: expr=3262849228 text=64f9facf027bbeea
    [body] TauCeti.DavisKahan.halmosSourceDefect  (def, DavisKahan/Geometry/Halmos/TwoProjections.lean:111)
        TauCeti.DavisKahan.halmosSourceDefect.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {H : Type u_2}
          [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) : Submodule 𝕜 H
        hash: expr=1773535531 text=175b124071948810
    [body] TauCeti.DavisKahan.halmosTargetDefect  (def, DavisKahan/Geometry/Halmos/TwoProjections.lean:115)
        TauCeti.DavisKahan.halmosTargetDefect.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {H : Type u_2}
          [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) : Submodule 𝕜 H
        hash: expr=1773535531 text=175b124071948810
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.tanAngleOperatorR  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculusReal.lean:126)
      TauCeti.DavisKahanExt.tanAngleOperatorR.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℝ E] [CompleteSpace E] (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℝ] E
      hash: expr=2215108693 text=ca05c2be87f84df1
    [body] TauCeti.RealComplexification.realPartOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:509)
        TauCeti.RealComplexification.realPartOperator.{u_1, u_2} {E : Type u_1} {F : Type u_2}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
          (T : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification F) : E →L[ℝ] F
        hash: expr=3255006892 text=5b4b316d076d7dac
      [type] TauCeti.RealComplexification  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:66)
          TauCeti.RealComplexification.{u_1} (E : Type u_1) : Type u_1
          hash: expr=1219222929 text=b115962a62bfdf78
      [body] TauCeti.RealComplexification.re  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:110)
          TauCeti.RealComplexification.re.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
          hash: expr=2897469443 text=1ee09de9c3b20d00
        [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.RealComplexification.ofReal  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:263)
          TauCeti.RealComplexification.ofReal.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℝ E] : E →ₗᵢ[ℝ] TauCeti.RealComplexification E
          hash: expr=2088652411 text=71b15fd88eac82fd
        [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.RealComplexification.mk  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:105)
            TauCeti.RealComplexification.mk.{u_1} {E : Type u_1} (x y : E) : TauCeti.RealComplexification E
            hash: expr=2390836649 text=76af0c3ed38ec24a
          [type] TauCeti.RealComplexification  (above)
    [body] TauCeti.DavisKahanExt.tanAngleOperatorC  (def, DavisKahan/Geometry/Angle/TanAngleFunctionalCalculus.lean:74)
        TauCeti.DavisKahanExt.tanAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.angleOperatorC  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean:84)
          TauCeti.DavisKahanExt.angleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] TauCeti.DavisKahanExt.sinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:38)
            TauCeti.DavisKahanExt.sinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
              [V.HasOrthogonalProjection] : E →L[ℂ] E
            hash: expr=187490045 text=178745a4708f5513
          [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
              ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
                [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
                [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
              hash: expr=299460441 text=f21cf18f7b7963ad
    [body] TauCeti.RealComplexification  (above)
    [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (def, DavisKahan/SpectralTheory/Complexification/Subspace.lean:45)
        TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule.{u_1} {E : Type u_1}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Submodule ℝ E) :
          Submodule ℂ (TauCeti.RealComplexification E)
        hash: expr=3786915484 text=ce5d0cdd7318abdd
      [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.RealComplexification.re  (above)
      [body] TauCeti.RealComplexification.im  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:115)
          TauCeti.RealComplexification.im.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
          hash: expr=2897469443 text=1ee09de9c3b20d00
        [type] TauCeti.RealComplexification  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

33 project constant(s) unfolded, 1 project leaf/leaves, 67 boundary constant(s), 273 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, Submodule, Submodule.HasOrthogonalProjection, LinearPMap, RingHom.id, ContinuousLinearMap, IsSelfAdjoint, Subtype, Submodule.orthogonal, Nat, LinearPMap.toFun', Eq, ContinuousLinearMap.comp, Submodule.starProjection, Submodule.subtypeL, And, Complex, EuclideanSpace, Fin, ENNReal, EuclideanSpace.basisFun, RCLike, AddMonoidHom, Nonempty, LinearIsometryEquiv, Ne, ENNReal.toReal, FiniteDimensional, LinearMap, LinearMap.comp, OrthonormalBasis, Fin.lastCases, iSup, ENNReal.ofReal, LinearIsometry, LinearMap.mkContinuous, cfc, Real.tan, WithLp, Prod, Set.ofPred, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, AddCommGroup, Module, Module.ofMinimalAxioms, NormedSpace, Real.arcsin, SMul, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.adjoint, NontriviallyNormedField, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast
~~~~

</details>

#### `TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:212`

~~~~lean
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem tanTheta_directed_unboundedRitz_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem D.trial.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex.{v} {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : H →ₗ.[ℂ] H}
  {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace ↥Z]
  (D : TauCeti.DavisKahan.UnboundedRitzPair A Z) (hV : TauCeti.DavisKahan.ReducingComplement A V)
  {alpha delta : ℝ} (hdelta : 0 < delta)
  (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
  (hUnwanted :
    ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A ⟨y, hy⟩) y))
  (tanTheta0 : ↥Z →L[ℂ] H)
  (htan :
    TauCeti.DavisKahan.TanTheta.HasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      tanTheta0)
  (hResidual : N.Mem D.trial.residual) :
  N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual
~~~~

Structural type hash `2428269602`, printed-type hash `2c050cb47b0c8013`.

Statement closure: 20 project constant(s) unfolded, 0 project leaf/leaves, 50 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.UnboundedRitzPair`, `TauCeti.DavisKahan.ReducingComplement`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.TanTheta.HasTheorem63DirectedTangentApproximationNumbersInfinite`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.DavisKahan.TanTheta.theorem63DirectedSineBlock`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.diagOp`, `ContinuousLinearMap.approximationNumber`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.CrossedDefectsEquivalent`, `TauCeti.principalTangents`, `TauCeti.ritzResidual`, `TauCeti.DavisKahanExt.tanAngleOperatorC`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `Submodule`, `Submodule.HasOrthogonalProjection`, `Subtype`, `Real`, `Submodule.orthogonal`, `Nat`, `AddMonoidHom`, `LinearPMap.toFun'`, `ContinuousLinearMap`, `And`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `Submodule.starProjection`, `Real.tan`, `Real.arcsin`, `Ne`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `IsSelfAdjoint`, `ContinuousLinearMap.comp`, `Submodule.subtypeL`, `iSup`, `ENNReal.ofReal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `NormedSpace`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:193)
    TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_complex.{v} {H : Type v}
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : H →ₗ.[ℂ] H}
      {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace ↥Z]
      (D : TauCeti.DavisKahan.UnboundedRitzPair A Z) (hV : TauCeti.DavisKahan.ReducingComplement A V)
      {alpha delta : ℝ} (hdelta : 0 < delta)
      (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
      (hUnwanted :
        ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A ⟨y, hy⟩) y))
      (tanTheta0 : ↥Z →L[ℂ] H)
      (htan :
        TauCeti.DavisKahan.TanTheta.HasTheorem63DirectedTangentApproximationNumbersInfinite Z V
          tanTheta0)
      (hResidual : N.Mem D.trial.residual) :
      N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual
    hash: expr=2428269602 text=2c050cb47b0c8013
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.UnboundedRitzPair  (structure, DavisKahan/TanTheta/RitzPair.lean:53)
      TauCeti.DavisKahan.UnboundedRitzPair.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
        [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type v
      field trial : {𝕜 : Type u} → [inst : RCLike 𝕜] → {H : Type v} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {A : H →ₗ.[𝕜] H} → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.UnboundedRitzPair A Z → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z
      field mem_domain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), ↑↑z ∈ A.domain
      field action_eq : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), self.trial.action z = ↑A ⟨↑↑z, ⋯⟩
      hash: expr=1041214427 text=5389305b6685c32e
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (structure, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:90)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜]
          {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (Z : Submodule 𝕜 H)
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type u
        field compression : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →ₗ.[𝕜] ↥Z
        field compression_isSelfAdjoint : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z), IsSelfAdjoint self.compression
        field residual : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →L[𝕜] H
        field residual_orthogonal : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z) (z z' : ↥Z), inner 𝕜 (self.residual z) ↑z' = 0
        hash: expr=1788257613 text=ba6c9f3809856f0d
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action  (def, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:114)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action.{u, u_1} {𝕜 : Type u_1}
          [RCLike 𝕜] {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H}
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z]
          (D : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z)
          (z : ↥D.compression.domain) : H
        hash: expr=957381741 text=95550eba98fc6d55
      [type] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (above)
  [type] TauCeti.DavisKahan.ReducingComplement  (structure, DavisKahan/TanTheta/RitzPair.lean:68)
      TauCeti.DavisKahan.ReducingComplement.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (V : Submodule 𝕜 H)
        [V.HasOrthogonalProjection] : Prop
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection], TauCeti.DavisKahan.ReducingComplement A V → ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain
      field commutes : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection] (self : TauCeti.DavisKahan.ReducingComplement A V) (x : ↥A.domain), Vᗮ.starProjection (↑A x) = ↑A ⟨Vᗮ.starProjection ↑x, ⋯⟩
      hash: expr=2182083140 text=f405375b390dedf0
  [type] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
      TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
      hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.TanTheta.HasTheorem63DirectedTangentApproximationNumbersInfinite  (def, DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:627)
      TauCeti.DavisKahan.TanTheta.HasTheorem63DirectedTangentApproximationNumbersInfinite.{u}
        {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Z V : Submodule ℂ H)
        [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] (tanTheta0 : ↥Z →L[ℂ] H) : Prop
      hash: expr=3925669398 text=d52d173b1b5eca77
    [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
        TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
          {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
        hash: expr=4158989512 text=be2938934bb498aa
      [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
          ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
            {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
            [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
          hash: expr=2527437639 text=7dc5679d2ff68267
    [body] TauCeti.DavisKahan.TanTheta.theorem63DirectedSineBlock  (def, DavisKahan/TanTheta/Theorem63FiniteSource.lean:57)
        TauCeti.DavisKahan.TanTheta.theorem63DirectedSineBlock.{u} {H : Type u} [NormedAddCommGroup H]
          [InnerProductSpace ℂ H] (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : ↥Z →L[ℂ] H
        hash: expr=3283385770 text=19c6cfa8216f894f
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

20 project constant(s) unfolded, 0 project leaf/leaves, 50 boundary constant(s), 155 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, Submodule, Submodule.HasOrthogonalProjection, Subtype, Real, Submodule.orthogonal, Nat, AddMonoidHom, LinearPMap.toFun', ContinuousLinearMap, And, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, Submodule.starProjection, Real.tan, Real.arcsin, Ne, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, IsSelfAdjoint, ContinuousLinearMap.comp, Submodule.subtypeL, iSup, ENNReal.ofReal, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, NontriviallyNormedField, SeminormedAddCommGroup, NormedSpace, iInf, Cardinal, LinearMap.rank, Nat.cast
~~~~

</details>

#### `TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:256`

~~~~lean
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem tanTheta_directed_unboundedRitz_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
    (hResidual : N.Mem D.trial.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_real.{v} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E}
  {Z V : Submodule ℝ E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace ↥Z]
  (D : TauCeti.DavisKahan.UnboundedRitzPair A Z) (hV : TauCeti.DavisKahan.ReducingComplement A V)
  {alpha delta : ℝ} (hdelta : 0 < delta)
  (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
  (hUnwanted : ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (↑A ⟨y, hy⟩) y)
  (tanTheta0 : ↥Z →L[ℝ] E)
  (htan :
    TauCeti.DavisKahan1970.HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V
      tanTheta0)
  (hResidual : N.Mem D.trial.residual) :
  N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual
~~~~

Structural type hash `3110891221`, printed-type hash `e50b6b1077d11587`.

Statement closure: 20 project constant(s) unfolded, 0 project leaf/leaves, 50 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.UnboundedRitzPair`, `TauCeti.DavisKahan.ReducingComplement`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan1970.HasTheorem63DirectedTangentApproximationNumbersInfiniteReal`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData`, `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.diagOp`, `ContinuousLinearMap.approximationNumber`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.CrossedDefectsEquivalent`, `TauCeti.principalTangents`, `TauCeti.ritzResidual`, `TauCeti.DavisKahanExt.tanAngleOperatorC`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `Submodule`, `Submodule.HasOrthogonalProjection`, `Subtype`, `Submodule.orthogonal`, `Nat`, `LinearPMap.toFun'`, `ContinuousLinearMap`, `And`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `Submodule.starProjection`, `AddMonoidHom`, `Real.tan`, `Real.arcsin`, `Ne`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `IsSelfAdjoint`, `ContinuousLinearMap.comp`, `Submodule.subtypeL`, `iSup`, `ENNReal.ofReal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `NormedSpace`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:250)
    TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_symmetricNorming_real.{v} {E : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E}
      {Z V : Submodule ℝ E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace ↥Z]
      (D : TauCeti.DavisKahan.UnboundedRitzPair A Z) (hV : TauCeti.DavisKahan.ReducingComplement A V)
      {alpha delta : ℝ} (hdelta : 0 < delta)
      (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
      (hUnwanted : ∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (↑A ⟨y, hy⟩) y)
      (tanTheta0 : ↥Z →L[ℝ] E)
      (htan :
        TauCeti.DavisKahan1970.HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V
          tanTheta0)
      (hResidual : N.Mem D.trial.residual) :
      N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual
    hash: expr=3110891221 text=e50b6b1077d11587
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.UnboundedRitzPair  (structure, DavisKahan/TanTheta/RitzPair.lean:53)
      TauCeti.DavisKahan.UnboundedRitzPair.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
        [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type v
      field trial : {𝕜 : Type u} → [inst : RCLike 𝕜] → {H : Type v} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {A : H →ₗ.[𝕜] H} → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.UnboundedRitzPair A Z → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z
      field mem_domain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), ↑↑z ∈ A.domain
      field action_eq : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.UnboundedRitzPair A Z) (z : ↥self.trial.compression.domain), self.trial.action z = ↑A ⟨↑↑z, ⋯⟩
      hash: expr=1041214427 text=5389305b6685c32e
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (structure, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:90)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜]
          {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (Z : Submodule 𝕜 H)
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z] : Type u
        field compression : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →ₗ.[𝕜] ↥Z
        field compression_isSelfAdjoint : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z), IsSelfAdjoint self.compression
        field residual : {𝕜 : Type u_1} → [inst : RCLike 𝕜] → {H : Type u} → [inst_1 : NormedAddCommGroup H] → [inst_2 : InnerProductSpace 𝕜 H] → {Z : Submodule 𝕜 H} → [inst_3 : Z.HasOrthogonalProjection] → [inst_4 : CompleteSpace ↥Z] → TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z → ↥Z →L[𝕜] H
        field residual_orthogonal : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H} [inst_3 : Z.HasOrthogonalProjection] [inst_4 : CompleteSpace ↥Z] (self : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z) (z z' : ↥Z), inner 𝕜 (self.residual z) ↑z' = 0
        hash: expr=1788257613 text=ba6c9f3809856f0d
    [body] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action  (def, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:114)
        TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.action.{u, u_1} {𝕜 : Type u_1}
          [RCLike 𝕜] {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Z : Submodule 𝕜 H}
          [Z.HasOrthogonalProjection] [CompleteSpace ↥Z]
          (D : TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData Z)
          (z : ↥D.compression.domain) : H
        hash: expr=957381741 text=95550eba98fc6d55
      [type] TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData  (above)
  [type] TauCeti.DavisKahan.ReducingComplement  (structure, DavisKahan/TanTheta/RitzPair.lean:68)
      TauCeti.DavisKahan.ReducingComplement.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (V : Submodule 𝕜 H)
        [V.HasOrthogonalProjection] : Prop
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection], TauCeti.DavisKahan.ReducingComplement A V → ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain
      field commutes : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection] (self : TauCeti.DavisKahan.ReducingComplement A V) (x : ↥A.domain), Vᗮ.starProjection (↑A x) = ↑A ⟨Vᗮ.starProjection ↑x, ⋯⟩
      hash: expr=2182083140 text=f405375b390dedf0
  [type] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
      TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
      hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan1970.HasTheorem63DirectedTangentApproximationNumbersInfiniteReal  (def, DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:246)
      TauCeti.DavisKahan1970.HasTheorem63DirectedTangentApproximationNumbersInfiniteReal.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] (tanTheta0 : ↥Z →L[ℝ] E) : Prop
      hash: expr=3952191189 text=cde50ffa985a97af
    [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
        TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
          {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
        hash: expr=4158989512 text=be2938934bb498aa
      [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
          ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
            {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
            [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
          hash: expr=2527437639 text=7dc5679d2ff68267
    [body] TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal  (def, DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:53)
        TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal.{v} {E : Type v} [NormedAddCommGroup E]
          [InnerProductSpace ℝ E] (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : ↥Z →L[ℝ] E
        hash: expr=1438324023 text=13f16495f4efac5e
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

20 project constant(s) unfolded, 0 project leaf/leaves, 50 boundary constant(s), 156 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, LinearPMap, RingHom.id, Submodule, Submodule.HasOrthogonalProjection, Subtype, Submodule.orthogonal, Nat, LinearPMap.toFun', ContinuousLinearMap, And, Complex, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, Submodule.starProjection, AddMonoidHom, Real.tan, Real.arcsin, Ne, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, IsSelfAdjoint, ContinuousLinearMap.comp, Submodule.subtypeL, iSup, ENNReal.ofReal, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, NontriviallyNormedField, SeminormedAddCommGroup, NormedSpace, iInf, Cardinal, LinearMap.rank, Nat.cast
~~~~

</details>

### Supporting scope declarations

- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_complex_of_crossedDefects` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_symmetricNorming_real_of_crossedDefects` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_symmetricNorming_rclike` — elaborated; source located
- `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial` — elaborated; source located
- `TauCeti.DavisKahan.FiniteDimensional.partIII_tanTheta_ritzResidual_uiNorm` — not in environment; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan.TanTheta.UnboundedCompressionTrialData.ideal_of_formBounds` — elaborated; source located
- `TauCeti.DavisKahan1970.theorem6_3_unboundedCompression_ideal_real` — elaborated; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction`

The literal dimension-coherent source unitary-invariant norm. The new generic directed headline theorem uses it directly over arbitrary RCLike scalars.

#### `TauCeti.principalTangents`

The directed principal-tangent singular-value sequence used in the paper definition of tan Theta0.

#### `TauCeti.ritzResidual`

The Rayleigh--Ritz residual. In the generic headline theorem it appears directly on the right-hand side rather than through a bundled problem record.

#### `TauCeti.DavisKahan.CrossedDefectsEquivalent`

The paper-wide nonacute direct-rotation existence condition (3.5), needed only for the ambient whole-space tangent semantics in the general infinite-dimensional case.

#### `TauCeti.DavisKahanExt.tanAngleOperatorC`

The canonical complex ambient tan(Theta) operator used by the unbounded whole-space scope companion.

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜]; no ℂ specialization appears in that headline type. Field-specific unbounded ambient declarations remain scope companions. | claimed_exact |
| spec(A0) subset [beta,alpha] and unwanted exact spectrum subset [alpha+delta,infinity). | hCompressionSpectrum and hUnwantedSpectrum are literal SpectrumIn hypotheses in tanTheta_directed_finiteDimensional_symmetricNorming_rclike; TanThetaIntervalGap is constructed only inside the proof and is not part of the public signature. | claimed_exact |
| H0=0 / Rayleigh--Ritz choice. | The public conclusion is written directly in terms of ritzResidual A X, where X is the trial isometry and the coordinate compression is the Rayleigh--Ritz compression. | claimed_exact |
| delta \|\|tan Theta0\|\| <= \|\|R\|\|. | tanTheta_directed_finiteDimensional_symmetricNorming_rclike concludes δ * N.gauge tanTheta0.toContinuousLinearMap <= N.gauge (ritzResidual A X).toContinuousLinearMap, with tanTheta0 constrained to have the principal-tangent singular values. | claimed_exact |
| delta \|\|tan Theta\|\| <= \|\|H\|\|. | The unbounded ambient source companion concludes the factor-one estimate for tanAngleOperatorC; its real sibling is compiler-checked as supporting scalar scope. | scope_companion |
| No separately assumed tangent-pole exclusion in the printed theorem. | The scalar-generic directed theorem assumes only the spectral placement and derives transversality in its engine. The ambient source companion uses the accepted nonlocal (3.5) semantics rather than a numerical pole hypothesis. | claimed_exact |

**Review note.** The directed residual half now has a scalar-generic, SymmetricNormingFunction, source-shaped canonical theorem whose public signature exposes the Ritz spectral placement instead of TanThetaIntervalGap. The harder ambient/unbounded half remains represented by the accepted source-shaped complex theorem plus its real companion because the current whole-space angle-operator implementation is field-specific. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

2026-08-31: the canonical declaration list here is now the counted result's `canonical_evidence` in `dev/davis-kahan-1970-formalization-result-inventory.json`, and the checker enforces that. Demoted to supporting: TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_symmetricNorming_rclike -- a finite-dimensional or capability-class facade cannot be the canonical witness for a result certified at unbounded infinite-dimensional scope.

2026-08-31 (coherent-clause audit): demoted to supporting because the compiler-printed type does not carry the scope the declaration was credited with: TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial, TauCeti.DavisKahan.FiniteDimensional.partIII_tanTheta_ritzResidual_uiNorm.

**Next action.** No counted-result gap remains. Preserve the accepted nonlocal source interpretation and the bounded/unbounded, real/complex source-facing endpoints; re-audit only if the distributable source specification changes.

## C. Davis and W. M. Kahan, The Rotation of Eigenvectors by a Perturbation. III, SIAM J. Numer. Anal. 7(1), 1970, 1–46.: Davis--Kahan double-angle sin 2 theta theorem

The Section 2 sin(2 theta) theorem: interval/exterior separation gives directed residual and ambient perturbation bounds with factor two.

### Normalized source statement

**Setup**
- Lambda0 and Lambda1 are the exact/perturbed diagonal blocks used by the paper, R is the residual, H is the perturbation, and Theta0/Theta are directed/ambient angles.

**Hypotheses**
- For beta<=alpha and delta>0, spec(Lambda0) is contained in [beta,alpha] and spec(Lambda1) avoids (beta-delta,alpha+delta).

**Conclusions**
- delta * ||sin(2 Theta0)|| <= 2 ||R||.
- delta * ||sin(2 Theta)|| <= 2 ||H||.

**Scope**
- Arbitrary source unitary-invariant norm; real/complex and infinite-dimensional scope, with the maintained unbounded directed-residual extension.

### Canonical Lean declarations

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidual.lean:370`

~~~~lean
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Submodule ℂ H} [V.HasOrthogonalProjection]
  {M : V →L[ℂ] V} {R : V →L[ℂ] H}
  {A : H →ₗ.[ℂ] H}
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : DavisKahan.ExactSinTheta.FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge
          (sinTwoThetaIdealBlock (selfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * N.gauge R
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex.{v}
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Submodule ℂ H}
  [V.HasOrthogonalProjection] {M : ↥V →L[ℂ] ↥V} {R : ↥V →L[ℂ] H} {A : H →ₗ.[ℂ] H}
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (hA : IsSelfAdjoint A) (B : Set ℝ)
  (hB : MeasurableSet B) (hVdom : ∀ (v : ↥V), ↑v ∈ A.domain)
  (hres : ∀ (v : ↥V), ↑A ⟨↑v, ⋯⟩ = R v + ↑(M v)) {δ : ℝ} (hδ : 0 < δ)
  (hgap :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
  (hRmem : N.Mem R) :
  N.Mem
      (TauCeti.DavisKahan.sinTwoThetaIdealBlock
        (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) V) ∧
    δ *
        N.gauge
          (TauCeti.DavisKahan.sinTwoThetaIdealBlock
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) V) ≤
      2 * N.gauge R
~~~~

Structural type hash `414547591`, printed-type hash `0c92903ffa5097fc`.

Statement closure: 45 project constant(s) unfolded, 7 project leaf/leaves, 88 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.selfAdjointSpectralSubspace`, `TauCeti.DavisKahan.selfAdjointSpectralRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.sinTwoThetaIdealBlock`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.pvmRangeSubspace`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.LinearPMap.specRestrict`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.diagOp`, `TauCeti.LinearPMap.realSpectrum`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.LinearPMap.specRange`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.LinearPMap.specProjection`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidual`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`, `TauCeti.DavisKahanExt.sinTwoAngleOperatorC`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `Submodule`, `Submodule.HasOrthogonalProjection`, `ContinuousLinearMap`, `RingHom.id`, `Subtype`, `LinearPMap`, `IsSelfAdjoint`, `Set`, `Real`, `MeasurableSet`, `Eq`, `LinearPMap.toFun'`, `MeasurableSet.compl`, `And`, `Nat`, `EuclideanSpace`, `Fin`, `ENNReal`, `EuclideanSpace.basisFun`, `RCLike`, `Ne`, `ContinuousLinearMap.comp`, `Submodule.starProjection`, `Submodule.map`, `Submodule.reflection`, `Submodule.orthogonal`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `LinearMap.range`, `Submodule.comap`, `Submodule.subtype`, `iSup`, `ENNReal.ofReal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Exists`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `NormedSpace`, `Exists.choose`, `LinearMap.mkContinuous`, `RealRMK.rieszMeasure`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidual.lean:356)
    TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex.{v}
      {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Submodule ℂ H}
      [V.HasOrthogonalProjection] {M : ↥V →L[ℂ] ↥V} {R : ↥V →L[ℂ] H} {A : H →ₗ.[ℂ] H}
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (hA : IsSelfAdjoint A) (B : Set ℝ)
      (hB : MeasurableSet B) (hVdom : ∀ (v : ↥V), ↑v ∈ A.domain)
      (hres : ∀ (v : ↥V), ↑A ⟨↑v, ⋯⟩ = R v + ↑(M v)) {δ : ℝ} (hδ : 0 < δ)
      (hgap :
        TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
          (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB)
          (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
      (hRmem : N.Mem R) :
      N.Mem
          (TauCeti.DavisKahan.sinTwoThetaIdealBlock
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) V) ∧
        δ *
            N.gauge
              (TauCeti.DavisKahan.sinTwoThetaIdealBlock
                (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) V) ≤
          2 * N.gauge R
    hash: expr=414547591 text=0c92903ffa5097fc
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.selfAdjointSpectralSubspace  (def, DavisKahan/SpectralTheory/SpectralRestriction.lean:62)
      TauCeti.DavisKahan.selfAdjointSpectralSubspace.{u_1} {H : Type u_1} [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
        (hB : MeasurableSet B) : Submodule ℂ H
      hash: expr=3996704367 text=e1824c7e6cb35d29
    [body] TauCeti.pvmRangeSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Subspace.lean:51)
        TauCeti.pvmRangeSubspace.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] (P : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) :
          Submodule ℂ H
        hash: expr=3793749016 text=ac2df232fd76eb3a
      [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
          TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] : Type u_2
          field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
          field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
          field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
          field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
          field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
          field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
          hash: expr=2326492630 text=8a7f2f92f7e6cb25
    [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
        TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
        hash: expr=1025771960 text=03d8a0e1bace7dda
      [type] TauCeti.ProjValMeasure  (above)
      [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
          TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
            {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
          hash: expr=3192152571 text=38dbb03b36baa07e
        [type] TauCeti.ProjValMeasure  (above)
        [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
            TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
              (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=6169287 text=22cb14432afff4f4
          [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
              TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
              hash: expr=2377768205 text=1636dc1e3618d340
            [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                hash: expr=2489458960 text=438ae027281cfbf3
            [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                hash: expr=3802524166 text=6359a60df1615396
              [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
              [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                  TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                  hash: expr=1909853194 text=b5d0ecb89e77cc8a
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                    TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                      [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                    hash: expr=3546105377 text=12fa953afc9438d3
                  [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                      TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                        MeasureTheory.Measure ↑(spectrum ℂ a)
                      hash: expr=2083923581 text=098301ad89533cf1
                    [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                        TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                          CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                        hash: expr=1299686186 text=681fa6315915ecf0
                      [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                          TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                          hash: expr=1488155521 text=8b20cf9e9db8beeb
                [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                    TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                      (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                    hash: expr=2675746042 text=64520af0639dba43
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
            [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
            [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                  ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                hash: expr=1978111998 text=fb2d00c2b9b8b360
        [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
            TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
              MeasureTheory.Measure ℝ
            hash: expr=1112489121 text=ea1d4ee13b3b4c3a
          [body] TauCeti.BorelCalculus.diagMeasure  (above)
        [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
            TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
              MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
            hash: expr=4257216657 text=b6885b32b095cce4
        [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
            TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
              inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
            hash: expr=3553813407 text=cfd94b77fa277777
        [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
            TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
              TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
            hash: expr=4063104685 text=e7abf70c80874ae5
        [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
            TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
              (hB₂ : MeasurableSet B₂) :
              TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
            hash: expr=2593835776 text=4cbdd3a7ba3e5991
      [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
          TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
            [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
          hash: expr=2980745689 text=d062a67869324a13
        [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
            TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
              [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
            hash: expr=2710346752 text=3040545541bf06a5
          [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
              TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
              hash: expr=4073139655 text=faa87465022c9f97
            [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                  (R : E →L[𝕜] E) : Prop
                field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                hash: expr=3549903545 text=cba9f82aae5d40ca
          [body] TauCeti.LinearPMap.IsResolventAt  (above)
      [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
          TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
            (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
          hash: expr=4155508021 text=b37a61963eed50ac
        [type] TauCeti.LinearPMap.cayley  (above)
      [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
          TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
            Measurable (TauCeti.LinearPMap.cayleyInv hA)
          hash: expr=321618348 text=e943baa16723572d
  [type] TauCeti.DavisKahan.selfAdjointSpectralRestriction  (def, DavisKahan/SpectralTheory/SpectralRestrictionOperator.lean:48)
      TauCeti.DavisKahan.selfAdjointSpectralRestriction.{u_1} {H : Type u_1} [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
        (hB : MeasurableSet B) :
        ↥(TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) →ₗ.[ℂ]
          ↥(TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
      hash: expr=864234461 text=f3a1baeba947f2f2
    [type] TauCeti.DavisKahan.selfAdjointSpectralSubspace  (above)
    [body] TauCeti.LinearPMap.specRestrict  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:704)
        TauCeti.LinearPMap.specRestrict.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
          ↥(TauCeti.LinearPMap.specRange hA B hB) →ₗ.[ℂ] ↥(TauCeti.LinearPMap.specRange hA B hB)
        hash: expr=2244333113 text=6e0452ccd1264842
      [type] TauCeti.LinearPMap.specRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:584)
          TauCeti.LinearPMap.specRange.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
            Submodule ℂ H
          hash: expr=3996704367 text=044a08326e510c21
        [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
            TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
              (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=1748688050 text=b7b417789e21c33b
          [body] TauCeti.LinearPMap.spectralPVM  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidual  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidual.lean:72)
      TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidual.{v}
        {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (U : Submodule ℂ G)
        [U.HasOrthogonalProjection] : CompleteSpace ↥U
      hash: expr=836250048 text=cdb33dfa9755d8b8
  [type] TauCeti.DavisKahan.sinTwoThetaIdealBlock  (def, DavisKahan/DoubleAngle/UnboundedIdeal.lean:39)
      TauCeti.DavisKahan.sinTwoThetaIdealBlock.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : H →L[𝕜] H
      hash: expr=2613108218 text=65547104dca1b58d
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

45 project constant(s) unfolded, 7 project leaf/leaves, 88 boundary constant(s), 275 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, Submodule, Submodule.HasOrthogonalProjection, ContinuousLinearMap, RingHom.id, Subtype, LinearPMap, IsSelfAdjoint, Set, Real, MeasurableSet, Eq, LinearPMap.toFun', MeasurableSet.compl, And, Nat, EuclideanSpace, Fin, ENNReal, EuclideanSpace.basisFun, RCLike, Ne, ContinuousLinearMap.comp, Submodule.starProjection, Submodule.map, Submodule.reflection, Submodule.orthogonal, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set.Icc, Set.ofPred, AddMonoidHom, LinearMap.range, Submodule.comap, Submodule.subtype, iSup, ENNReal.ofReal, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Exists, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, NormedSpace, Exists.choose, LinearMap.mkContinuous, RealRMK.rieszMeasure, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidualReal.lean:201`

~~~~lean
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {V : Submodule ℝ E} [V.HasOrthogonalProjection]
  {M : V →L[ℝ] V} {R : V →L[ℝ] E}
  {A : E →ₗ.[ℝ] E}
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge
          (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * N.gauge R
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real.{v}
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {V : Submodule ℝ E}
  [V.HasOrthogonalProjection] {M : ↥V →L[ℝ] ↥V} {R : ↥V →L[ℝ] E} {A : E →ₗ.[ℝ] E}
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (hA : IsSelfAdjoint A) (B : Set ℝ)
  (hB : MeasurableSet B) (hVdom : ∀ (v : ↥V), ↑v ∈ A.domain)
  (hres : ∀ (v : ↥V), ↑A ⟨↑v, ⋯⟩ = R v + ↑(M v)) {δ : ℝ} (hδ : 0 < δ)
  (hgap :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
  (hRmem : N.Mem R) :
  N.Mem
      (TauCeti.DavisKahan.sinTwoThetaIdealBlock
        (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) V) ∧
    δ *
        N.gauge
          (TauCeti.DavisKahan.sinTwoThetaIdealBlock
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
            V) ≤
      2 * N.gauge R
~~~~

Structural type hash `1121034465`, printed-type hash `7731a2da05b1706e`.

Statement closure: 62 project constant(s) unfolded, 9 project leaf/leaves, 93 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.sinTwoThetaIdealBlock`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection`, `TauCeti.LinearPMap.reducingRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.diagOp`, `TauCeti.LinearPMap.realSpectrum`, `TauCeti.RealComplexification.realPartOperator`, `TauCeti.DavisKahan.selfAdjointSpectralProjection`, `TauCeti.RealComplexification`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify`, `TauCeti.LinearPMap.ReducesSubspace`, `TauCeti.LinearPMap.reducingRestrictionDomain`, `TauCeti.LinearPMap.reducingRestrictionLinearMap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.RealComplexification.re`, `TauCeti.RealComplexification.ofReal`, `TauCeti.LinearPMap.specProjection`, `TauCeti.RealComplexification.im`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap`, `TauCeti.LinearPMap.InvariantSubspace`, `TauCeti.LinearPMap.reducingRestrictionDomainToAmbient`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.RealComplexification.mk`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidualReal`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`, `TauCeti.DavisKahanExt.sinTwoAngleOperatorC`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `Submodule`, `Submodule.HasOrthogonalProjection`, `ContinuousLinearMap`, `RingHom.id`, `Subtype`, `LinearPMap`, `IsSelfAdjoint`, `Set`, `MeasurableSet`, `Eq`, `LinearPMap.toFun'`, `MeasurableSet.compl`, `And`, `Nat`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `EuclideanSpace.basisFun`, `RCLike`, `LinearMap.range`, `Ne`, `ContinuousLinearMap.comp`, `Submodule.starProjection`, `Submodule.map`, `Submodule.reflection`, `Submodule.orthogonal`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `iSup`, `ENNReal.ofReal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `LinearIsometry`, `LinearMap.mkContinuous`, `WithLp`, `Prod`, `Exists`, `AddCommGroup`, `Module`, `Module.ofMinimalAxioms`, `NormedSpace`, `SMul`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `Exists.choose`, `RealRMK.rieszMeasure`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidualReal.lean:185)
    TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real.{v}
      {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {V : Submodule ℝ E}
      [V.HasOrthogonalProjection] {M : ↥V →L[ℝ] ↥V} {R : ↥V →L[ℝ] E} {A : E →ₗ.[ℝ] E}
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (hA : IsSelfAdjoint A) (B : Set ℝ)
      (hB : MeasurableSet B) (hVdom : ∀ (v : ↥V), ↑v ∈ A.domain)
      (hres : ∀ (v : ↥V), ↑A ⟨↑v, ⋯⟩ = R v + ↑(M v)) {δ : ℝ} (hδ : 0 < δ)
      (hgap :
        TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
          (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
          (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
      (hRmem : N.Mem R) :
      N.Mem
          (TauCeti.DavisKahan.sinTwoThetaIdealBlock
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) V) ∧
        δ *
            N.gauge
              (TauCeti.DavisKahan.sinTwoThetaIdealBlock
                (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
                V) ≤
          2 * N.gauge R
    hash: expr=1121034465 text=7731a2da05b1706e
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:416)
      TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
        (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) : Submodule ℝ E
      hash: expr=4005423199 text=f71755d5d60c952e
    [body] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:345)
        TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection.{v} {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
          (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) : E →L[ℝ] E
        hash: expr=3802734145 text=ac644fbaa093c418
      [body] TauCeti.RealComplexification.realPartOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:509)
          TauCeti.RealComplexification.realPartOperator.{u_1, u_2} {E : Type u_1} {F : Type u_2}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
            (T : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification F) : E →L[ℝ] F
          hash: expr=3255006892 text=5b4b316d076d7dac
        [type] TauCeti.RealComplexification  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:66)
            TauCeti.RealComplexification.{u_1} (E : Type u_1) : Type u_1
            hash: expr=1219222929 text=b115962a62bfdf78
        [body] TauCeti.RealComplexification.re  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:110)
            TauCeti.RealComplexification.re.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
            hash: expr=2897469443 text=1ee09de9c3b20d00
          [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.RealComplexification.ofReal  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:263)
            TauCeti.RealComplexification.ofReal.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] : E →ₗᵢ[ℝ] TauCeti.RealComplexification E
            hash: expr=2088652411 text=71b15fd88eac82fd
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.mk  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:105)
              TauCeti.RealComplexification.mk.{u_1} {E : Type u_1} (x y : E) : TauCeti.RealComplexification E
              hash: expr=2390836649 text=76af0c3ed38ec24a
            [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.DavisKahan.selfAdjointSpectralProjection  (def, DavisKahan/SpectralTheory/SpectralRestriction.lean:56)
          TauCeti.DavisKahan.selfAdjointSpectralProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
            (hB : MeasurableSet B) : H →L[ℂ] H
          hash: expr=1748688050 text=e4656068c7b20c48
        [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
            TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
              (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=1748688050 text=b7b417789e21c33b
          [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
              TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
              hash: expr=1025771960 text=03d8a0e1bace7dda
            [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
                TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] : Type u_2
                field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
                field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
                field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
                field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
                field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
                hash: expr=2326492630 text=8a7f2f92f7e6cb25
            [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
                TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
                hash: expr=3192152571 text=38dbb03b36baa07e
              [type] TauCeti.ProjValMeasure  (above)
              [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
                  TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                    [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                    (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
                  hash: expr=6169287 text=22cb14432afff4f4
                [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                    TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                    hash: expr=2377768205 text=1636dc1e3618d340
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                      TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                      field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                      field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                      hash: expr=2489458960 text=438ae027281cfbf3
                  [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                      TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                      hash: expr=3802524166 text=6359a60df1615396
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                    [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                        TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                          {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                        hash: expr=1909853194 text=b5d0ecb89e77cc8a
                      [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                      [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                          TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                            [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                          hash: expr=3546105377 text=12fa953afc9438d3
                        [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                            TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                              MeasureTheory.Measure ↑(spectrum ℂ a)
                            hash: expr=2083923581 text=098301ad89533cf1
                          [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                              TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                                CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                              hash: expr=1299686186 text=681fa6315915ecf0
                            [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                                TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                                hash: expr=1488155521 text=8b20cf9e9db8beeb
                      [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                          TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                            (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                          hash: expr=2675746042 text=64520af0639dba43
                        [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
                  [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                      TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                        ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                      hash: expr=1978111998 text=fb2d00c2b9b8b360
              [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
                  TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                    [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                    MeasureTheory.Measure ℝ
                  hash: expr=1112489121 text=ea1d4ee13b3b4c3a
                [body] TauCeti.BorelCalculus.diagMeasure  (above)
              [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
                  TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                    MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
                  hash: expr=4257216657 text=b6885b32b095cce4
              [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
                  TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                    inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                      ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
                  hash: expr=3553813407 text=cfd94b77fa277777
              [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
                  TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                    TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                  hash: expr=4063104685 text=e7abf70c80874ae5
              [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
                  TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                    (hB₂ : MeasurableSet B₂) :
                    TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                      TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
                  hash: expr=2593835776 text=4cbdd3a7ba3e5991
            [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
                TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
                  [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
                hash: expr=2980745689 text=d062a67869324a13
              [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
                  TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
                  hash: expr=2710346752 text=3040545541bf06a5
                [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                    TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                      [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                    hash: expr=4073139655 text=faa87465022c9f97
                  [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                      TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                        {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                        (R : E →L[𝕜] E) : Prop
                      field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                      field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                      field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                      hash: expr=3549903545 text=cba9f82aae5d40ca
                [body] TauCeti.LinearPMap.IsResolventAt  (above)
            [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
                TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
                  (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
                hash: expr=4155508021 text=b37a61963eed50ac
              [type] TauCeti.LinearPMap.cayley  (above)
            [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
                TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
                  Measurable (TauCeti.LinearPMap.cayleyInv hA)
                hash: expr=321618348 text=e943baa16723572d
      [body] TauCeti.RealComplexification  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:202)
          TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify.{v} {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
            TauCeti.RealComplexification E →ₗ.[ℂ] TauCeti.RealComplexification E
          hash: expr=319180028 text=b37652d39791961e
        [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:71)
            TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain.{v} {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
              Submodule ℂ (TauCeti.RealComplexification E)
            hash: expr=2420177506 text=e087bd3004ce1b40
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (def, DavisKahan/SpectralTheory/Complexification/Subspace.lean:45)
              TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule.{u_1} {E : Type u_1}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Submodule ℝ E) :
                Submodule ℂ (TauCeti.RealComplexification E)
              hash: expr=3786915484 text=ce5d0cdd7318abdd
            [type] TauCeti.RealComplexification  (above)
            [body] TauCeti.RealComplexification.re  (above)
            [body] TauCeti.RealComplexification.im  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:115)
                TauCeti.RealComplexification.im.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
                hash: expr=2897469443 text=1ee09de9c3b20d00
              [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:96)
            TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap.{v} {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
              ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A) →ₗ[ℂ]
                TauCeti.RealComplexification E
            hash: expr=3577002504 text=5dca1e23683a16f5
          [type] TauCeti.RealComplexification  (above)
          [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
          [body] TauCeti.RealComplexification.mk  (above)
          [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:84)
              TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe.{v} {E : Type v}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
                (z : ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A)) : ↥A.domain
              hash: expr=2785441133 text=410c166af5d8ede6
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
            [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:90)
              TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm.{v} {E : Type v}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
                (z : ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A)) : ↥A.domain
              hash: expr=2785441133 text=410c166af5d8ede6
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
            [body] TauCeti.RealComplexification.im  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify  (theorem, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:607)
          TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify.{v}
            {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E}
            (hA : IsSelfAdjoint A) :
            IsSelfAdjoint (TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify A)
          hash: expr=148782383 text=1cf221fc6bb0b7cb
  [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:650)
      TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
        (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
        ↥(TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS) →ₗ.[ℝ]
          ↥(TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS)
      hash: expr=3557671409 text=a68faeaf65be9200
    [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace  (above)
    [body] TauCeti.LinearPMap.reducingRestriction  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:236)
        TauCeti.LinearPMap.reducingRestriction.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
          [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) : ↥U →ₗ.[𝕜] ↥U
        hash: expr=919990832 text=6294b55e071b60e3
      [type] TauCeti.LinearPMap.ReducesSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:98)
          TauCeti.LinearPMap.ReducesSubspace.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
            [U.HasOrthogonalProjection] : Prop
          hash: expr=2182083140 text=ca42901128d27dd3
        [body] TauCeti.LinearPMap.InvariantSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:92)
            TauCeti.LinearPMap.InvariantSubspace.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) : Prop
            hash: expr=687545939 text=e719e4c9ef5bb4bd
      [body] TauCeti.LinearPMap.reducingRestrictionDomain  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:159)
          TauCeti.LinearPMap.reducingRestrictionDomain.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) :
            Submodule 𝕜 ↥U
          hash: expr=1322056522 text=cded76d807ce10df
      [body] TauCeti.LinearPMap.reducingRestrictionLinearMap  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:188)
          TauCeti.LinearPMap.reducingRestrictionLinearMap.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
            [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) :
            ↥(TauCeti.LinearPMap.reducingRestrictionDomain A U) →ₗ[𝕜] ↥U
          hash: expr=3070761079 text=783c5bf7467bcae2
        [type] TauCeti.LinearPMap.ReducesSubspace  (above)
        [type] TauCeti.LinearPMap.reducingRestrictionDomain  (above)
        [body] TauCeti.LinearPMap.reducingRestrictionDomainToAmbient  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:175)
            TauCeti.LinearPMap.reducingRestrictionDomainToAmbient.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
              (x : ↥(TauCeti.LinearPMap.reducingRestrictionDomain A U)) : ↥A.domain
            hash: expr=124560700 text=29ce882e442a8596
          [type] TauCeti.LinearPMap.reducingRestrictionDomain  (above)
    [body] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing  (theorem, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:596)
        TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing.{v} {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
          (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
          TauCeti.LinearPMap.ReducesSubspace A
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS)
        hash: expr=2538579909 text=bc3b439bb5002b58
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidualReal  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidualReal.lean:78)
      TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedResidualReal.{v}
        {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] (U : Submodule ℝ G)
        [U.HasOrthogonalProjection] : CompleteSpace ↥U
      hash: expr=2909647263 text=b21d4bbd0df0177b
  [type] TauCeti.DavisKahan.sinTwoThetaIdealBlock  (def, DavisKahan/DoubleAngle/UnboundedIdeal.lean:39)
      TauCeti.DavisKahan.sinTwoThetaIdealBlock.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : H →L[𝕜] H
      hash: expr=2613108218 text=65547104dca1b58d
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

62 project constant(s) unfolded, 9 project leaf/leaves, 93 boundary constant(s), 327 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, Submodule, Submodule.HasOrthogonalProjection, ContinuousLinearMap, RingHom.id, Subtype, LinearPMap, IsSelfAdjoint, Set, MeasurableSet, Eq, LinearPMap.toFun', MeasurableSet.compl, And, Nat, Complex, EuclideanSpace, Fin, ENNReal, EuclideanSpace.basisFun, RCLike, LinearMap.range, Ne, ContinuousLinearMap.comp, Submodule.starProjection, Submodule.map, Submodule.reflection, Submodule.orthogonal, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set.Icc, Set.ofPred, AddMonoidHom, iSup, ENNReal.ofReal, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, LinearIsometry, LinearMap.mkContinuous, WithLp, Prod, Exists, AddCommGroup, Module, Module.ofMinimalAxioms, NormedSpace, SMul, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, NontriviallyNormedField, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, Set.indicator, Set.preimage, MeasureTheory.Measure.map, Exists.choose, RealRMK.rieszMeasure, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:872`

~~~~lean
variable {Hc : Type v}
  [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
theorem sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex.{v}
  {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Hc →ₗ.[ℂ] Hc)
  (hA : IsSelfAdjoint A) (Eop : Hc →L[ℂ] Hc) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
  (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
  (hgap :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
  (hEmem : N.Mem Eop) :
  N.Mem
      (TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC
        (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯ S
          hS)) ∧
    δ *
        N.gauge
          (TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯
              S hS)) ≤
      2 * N.gauge Eop
~~~~

Structural type hash `1578888031`, printed-type hash `a765a31cf24794cd`.

Statement closure: 50 project constant(s) unfolded, 7 project leaf/leaves, 94 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.IsSelfAdjointOperator`, `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.selfAdjointSpectralSubspace`, `TauCeti.DavisKahan.selfAdjointSpectralRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC`, `TauCeti.LinearPMap.addBounded`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.pvmRangeSubspace`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.LinearPMap.specRestrict`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.DavisKahanExt.directedSinAngleOperatorC`, `TauCeti.DavisKahanExt.directedCosAngleOperatorC`, `TauCeti.diagOp`, `TauCeti.LinearPMap.realSpectrum`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.LinearPMap.specRange`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `ContinuousLinearMap.modulus`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.LinearPMap.specProjection`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan.addBounded_isSelfAdjoint`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`, `TauCeti.DavisKahanExt.sinTwoAngleOperatorC`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `IsSelfAdjoint`, `ContinuousLinearMap`, `Set`, `Real`, `MeasurableSet`, `Subtype`, `Submodule`, `MeasurableSet.compl`, `And`, `Nat`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `LinearMap.IsSymmetric`, `Ne`, `Submodule.HasOrthogonalProjection`, `LinearMap`, `LinearMap.domRestrict`, `ENNReal.toReal`, `FiniteDimensional`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `LinearPMap.toFun'`, `LinearMap.range`, `Submodule.comap`, `Submodule.subtype`, `iSup`, `ENNReal.ofReal`, `ContinuousLinearMap.comp`, `Submodule.starProjection`, `Submodule.orthogonal`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.adjoint`, `Exists`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `NormedSpace`, `Exists.choose`, `LinearMap.mkContinuous`, `RealRMK.rieszMeasure`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:860)
    TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex.{v}
      {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Hc →ₗ.[ℂ] Hc)
      (hA : IsSelfAdjoint A) (Eop : Hc →L[ℂ] Hc) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
      (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
      (hgap :
        TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
          (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB)
          (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
      (hEmem : N.Mem Eop) :
      N.Mem
          (TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯ S
              hS)) ∧
        δ *
            N.gauge
              (TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC
                (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
                (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯
                  S hS)) ≤
          2 * N.gauge Eop
    hash: expr=1578888031 text=a765a31cf24794cd
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.IsSelfAdjointOperator  (def, DavisKahan/BoundedOperator/Compat.lean:64)
      TauCeti.DavisKahan.IsSelfAdjointOperator.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →L[𝕜] E) : Prop
      hash: expr=2922739529 text=fcde7e035a15c851
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.selfAdjointSpectralSubspace  (def, DavisKahan/SpectralTheory/SpectralRestriction.lean:62)
      TauCeti.DavisKahan.selfAdjointSpectralSubspace.{u_1} {H : Type u_1} [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
        (hB : MeasurableSet B) : Submodule ℂ H
      hash: expr=3996704367 text=e1824c7e6cb35d29
    [body] TauCeti.pvmRangeSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Subspace.lean:51)
        TauCeti.pvmRangeSubspace.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] (P : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) :
          Submodule ℂ H
        hash: expr=3793749016 text=ac2df232fd76eb3a
      [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
          TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] : Type u_2
          field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
          field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
          field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
          field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
          field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
          field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
          hash: expr=2326492630 text=8a7f2f92f7e6cb25
    [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
        TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
        hash: expr=1025771960 text=03d8a0e1bace7dda
      [type] TauCeti.ProjValMeasure  (above)
      [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
          TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
            {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
          hash: expr=3192152571 text=38dbb03b36baa07e
        [type] TauCeti.ProjValMeasure  (above)
        [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
            TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
              (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=6169287 text=22cb14432afff4f4
          [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
              TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
              hash: expr=2377768205 text=1636dc1e3618d340
            [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                hash: expr=2489458960 text=438ae027281cfbf3
            [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                hash: expr=3802524166 text=6359a60df1615396
              [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
              [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                  TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                  hash: expr=1909853194 text=b5d0ecb89e77cc8a
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                    TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                      [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                    hash: expr=3546105377 text=12fa953afc9438d3
                  [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                      TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                        MeasureTheory.Measure ↑(spectrum ℂ a)
                      hash: expr=2083923581 text=098301ad89533cf1
                    [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                        TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                          CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                        hash: expr=1299686186 text=681fa6315915ecf0
                      [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                          TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                          hash: expr=1488155521 text=8b20cf9e9db8beeb
                [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                    TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                      (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                    hash: expr=2675746042 text=64520af0639dba43
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
            [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
            [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                  ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                hash: expr=1978111998 text=fb2d00c2b9b8b360
        [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
            TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
              MeasureTheory.Measure ℝ
            hash: expr=1112489121 text=ea1d4ee13b3b4c3a
          [body] TauCeti.BorelCalculus.diagMeasure  (above)
        [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
            TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
              MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
            hash: expr=4257216657 text=b6885b32b095cce4
        [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
            TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
              inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
            hash: expr=3553813407 text=cfd94b77fa277777
        [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
            TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
              TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
            hash: expr=4063104685 text=e7abf70c80874ae5
        [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
            TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
              (hB₂ : MeasurableSet B₂) :
              TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
            hash: expr=2593835776 text=4cbdd3a7ba3e5991
      [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
          TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
            [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
          hash: expr=2980745689 text=d062a67869324a13
        [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
            TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
              [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
            hash: expr=2710346752 text=3040545541bf06a5
          [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
              TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
              hash: expr=4073139655 text=faa87465022c9f97
            [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                  (R : E →L[𝕜] E) : Prop
                field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                hash: expr=3549903545 text=cba9f82aae5d40ca
          [body] TauCeti.LinearPMap.IsResolventAt  (above)
      [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
          TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
            (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
          hash: expr=4155508021 text=b37a61963eed50ac
        [type] TauCeti.LinearPMap.cayley  (above)
      [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
          TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
            Measurable (TauCeti.LinearPMap.cayleyInv hA)
          hash: expr=321618348 text=e943baa16723572d
  [type] TauCeti.DavisKahan.selfAdjointSpectralRestriction  (def, DavisKahan/SpectralTheory/SpectralRestrictionOperator.lean:48)
      TauCeti.DavisKahan.selfAdjointSpectralRestriction.{u_1} {H : Type u_1} [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
        (hB : MeasurableSet B) :
        ↥(TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) →ₗ.[ℂ]
          ↥(TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
      hash: expr=864234461 text=f3a1baeba947f2f2
    [type] TauCeti.DavisKahan.selfAdjointSpectralSubspace  (above)
    [body] TauCeti.LinearPMap.specRestrict  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:704)
        TauCeti.LinearPMap.specRestrict.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
          ↥(TauCeti.LinearPMap.specRange hA B hB) →ₗ.[ℂ] ↥(TauCeti.LinearPMap.specRange hA B hB)
        hash: expr=2244333113 text=6e0452ccd1264842
      [type] TauCeti.LinearPMap.specRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:584)
          TauCeti.LinearPMap.specRange.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
            Submodule ℂ H
          hash: expr=3996704367 text=044a08326e510c21
        [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
            TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
              (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=1748688050 text=b7b417789e21c33b
          [body] TauCeti.LinearPMap.spectralPVM  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:255)
      TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℂ] E
      hash: expr=187490045 text=178745a4708f5513
    [body] TauCeti.DavisKahanExt.directedSinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:109)
        TauCeti.DavisKahanExt.directedSinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
          ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
            [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
            [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
          hash: expr=299460441 text=f21cf18f7b7963ad
    [body] TauCeti.DavisKahanExt.directedCosAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:70)
        TauCeti.DavisKahanExt.directedCosAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] ContinuousLinearMap.modulus  (above)
  [type] TauCeti.LinearPMap.addBounded  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:872)
      TauCeti.LinearPMap.addBounded.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E
      hash: expr=66748006 text=2a4b564ad9f00a78
  [type] TauCeti.DavisKahan.addBounded_isSelfAdjoint  (theorem, DavisKahan/SinTheta/BoundedPerturbation.lean:60)
      TauCeti.DavisKahan.addBounded_isSelfAdjoint.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H →ₗ.[𝕜] H)
        (hA : IsSelfAdjoint A) (V : H →L[𝕜] H) (hV : TauCeti.DavisKahan.IsSelfAdjointOperator V) :
        IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
      hash: expr=611105799 text=2114ceedd875afc0
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

50 project constant(s) unfolded, 7 project leaf/leaves, 94 boundary constant(s), 295 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, IsSelfAdjoint, ContinuousLinearMap, Set, Real, MeasurableSet, Subtype, Submodule, MeasurableSet.compl, And, Nat, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, LinearMap.IsSymmetric, Ne, Submodule.HasOrthogonalProjection, LinearMap, LinearMap.domRestrict, ENNReal.toReal, FiniteDimensional, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set.Icc, Set.ofPred, AddMonoidHom, LinearPMap.toFun', LinearMap.range, Submodule.comap, Submodule.subtype, iSup, ENNReal.ofReal, ContinuousLinearMap.comp, Submodule.starProjection, Submodule.orthogonal, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.adjoint, Exists, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, NormedSpace, Exists.choose, LinearMap.mkContinuous, RealRMK.rieszMeasure, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:576`

~~~~lean
variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
theorem sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real.{v}
  {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Er →ₗ.[ℝ] Er)
  (hA : IsSelfAdjoint A) (Eop : Er →L[ℝ] Er) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
  (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
  (hgap :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
  (hEmem : N.Mem Eop) :
  N.Mem
      (TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC
        (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
        (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
          (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ∧
    δ *
        N.gauge
          (TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
              (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ≤
      2 * N.gauge Eop
~~~~

Structural type hash `649378079`, printed-type hash `ec98148251647147`.

Statement closure: 68 project constant(s) unfolded, 9 project leaf/leaves, 99 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.IsSelfAdjointOperator`, `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.RealComplexification`, `TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC`, `TauCeti.LinearPMap.addBounded`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection`, `TauCeti.LinearPMap.reducingRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.RealComplexification.re`, `TauCeti.RealComplexification.im`, `TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC`, `TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule`, `TauCeti.diagOp`, `TauCeti.LinearPMap.realSpectrum`, `TauCeti.RealComplexification.realPartOperator`, `TauCeti.DavisKahan.selfAdjointSpectralProjection`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify`, `TauCeti.LinearPMap.ReducesSubspace`, `TauCeti.LinearPMap.reducingRestrictionDomain`, `TauCeti.LinearPMap.reducingRestrictionLinearMap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.DavisKahanExt.directedSinAngleOperatorC`, `TauCeti.DavisKahanExt.directedCosAngleOperatorC`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.RealComplexification.ofReal`, `TauCeti.LinearPMap.specProjection`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap`, `TauCeti.LinearPMap.InvariantSubspace`, `TauCeti.LinearPMap.reducingRestrictionDomainToAmbient`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.RealComplexification.mk`, `ContinuousLinearMap.modulus`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan.addBounded_isSelfAdjoint`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`, `TauCeti.DavisKahanExt.sinTwoAngleOperatorC`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `IsSelfAdjoint`, `ContinuousLinearMap`, `Set`, `MeasurableSet`, `Subtype`, `Submodule`, `MeasurableSet.compl`, `And`, `Complex`, `Nat`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `LinearMap.IsSymmetric`, `LinearMap.range`, `Ne`, `WithLp`, `Prod`, `Submodule.HasOrthogonalProjection`, `LinearMap`, `LinearMap.domRestrict`, `ENNReal.toReal`, `FiniteDimensional`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `LinearPMap.toFun'`, `iSup`, `ENNReal.ofReal`, `AddCommGroup`, `NormedSpace`, `Module`, `Module.ofMinimalAxioms`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `LinearIsometry`, `LinearMap.mkContinuous`, `Submodule.starProjection`, `Submodule.orthogonal`, `SMul`, `ContinuousLinearMap.comp`, `Exists`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.adjoint`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `Exists.choose`, `RealRMK.rieszMeasure`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:559)
    TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_real.{v}
      {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Er →ₗ.[ℝ] Er)
      (hA : IsSelfAdjoint A) (Eop : Er →L[ℝ] Er) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
      (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
      (hgap :
        TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
          (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
          (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
      (hEmem : N.Mem Eop) :
      N.Mem
          (TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
              (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ∧
        δ *
            N.gauge
              (TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC
                (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
                (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
                  (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ≤
          2 * N.gauge Eop
    hash: expr=649378079 text=ec98148251647147
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.IsSelfAdjointOperator  (def, DavisKahan/BoundedOperator/Compat.lean:64)
      TauCeti.DavisKahan.IsSelfAdjointOperator.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →L[𝕜] E) : Prop
      hash: expr=2922739529 text=fcde7e035a15c851
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:416)
      TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
        (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) : Submodule ℝ E
      hash: expr=4005423199 text=f71755d5d60c952e
    [body] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:345)
        TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection.{v} {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
          (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) : E →L[ℝ] E
        hash: expr=3802734145 text=ac644fbaa093c418
      [body] TauCeti.RealComplexification.realPartOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:509)
          TauCeti.RealComplexification.realPartOperator.{u_1, u_2} {E : Type u_1} {F : Type u_2}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
            (T : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification F) : E →L[ℝ] F
          hash: expr=3255006892 text=5b4b316d076d7dac
        [type] TauCeti.RealComplexification  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:66)
            TauCeti.RealComplexification.{u_1} (E : Type u_1) : Type u_1
            hash: expr=1219222929 text=b115962a62bfdf78
        [body] TauCeti.RealComplexification.re  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:110)
            TauCeti.RealComplexification.re.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
            hash: expr=2897469443 text=1ee09de9c3b20d00
          [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.RealComplexification.ofReal  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:263)
            TauCeti.RealComplexification.ofReal.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] : E →ₗᵢ[ℝ] TauCeti.RealComplexification E
            hash: expr=2088652411 text=71b15fd88eac82fd
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.mk  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:105)
              TauCeti.RealComplexification.mk.{u_1} {E : Type u_1} (x y : E) : TauCeti.RealComplexification E
              hash: expr=2390836649 text=76af0c3ed38ec24a
            [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.DavisKahan.selfAdjointSpectralProjection  (def, DavisKahan/SpectralTheory/SpectralRestriction.lean:56)
          TauCeti.DavisKahan.selfAdjointSpectralProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
            (hB : MeasurableSet B) : H →L[ℂ] H
          hash: expr=1748688050 text=e4656068c7b20c48
        [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
            TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
              (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=1748688050 text=b7b417789e21c33b
          [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
              TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
              hash: expr=1025771960 text=03d8a0e1bace7dda
            [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
                TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] : Type u_2
                field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
                field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
                field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
                field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
                field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
                hash: expr=2326492630 text=8a7f2f92f7e6cb25
            [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
                TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
                hash: expr=3192152571 text=38dbb03b36baa07e
              [type] TauCeti.ProjValMeasure  (above)
              [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
                  TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                    [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                    (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
                  hash: expr=6169287 text=22cb14432afff4f4
                [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                    TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                    hash: expr=2377768205 text=1636dc1e3618d340
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                      TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                      field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                      field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                      hash: expr=2489458960 text=438ae027281cfbf3
                  [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                      TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                      hash: expr=3802524166 text=6359a60df1615396
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                    [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                        TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                          {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                        hash: expr=1909853194 text=b5d0ecb89e77cc8a
                      [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                      [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                          TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                            [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                          hash: expr=3546105377 text=12fa953afc9438d3
                        [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                            TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                              MeasureTheory.Measure ↑(spectrum ℂ a)
                            hash: expr=2083923581 text=098301ad89533cf1
                          [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                              TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                                CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                              hash: expr=1299686186 text=681fa6315915ecf0
                            [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                                TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                                hash: expr=1488155521 text=8b20cf9e9db8beeb
                      [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                          TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                            (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                          hash: expr=2675746042 text=64520af0639dba43
                        [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
                  [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                      TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                        ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                      hash: expr=1978111998 text=fb2d00c2b9b8b360
              [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
                  TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                    [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                    MeasureTheory.Measure ℝ
                  hash: expr=1112489121 text=ea1d4ee13b3b4c3a
                [body] TauCeti.BorelCalculus.diagMeasure  (above)
              [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
                  TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                    MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
                  hash: expr=4257216657 text=b6885b32b095cce4
              [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
                  TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                    inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                      ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
                  hash: expr=3553813407 text=cfd94b77fa277777
              [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
                  TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                    TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                  hash: expr=4063104685 text=e7abf70c80874ae5
              [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
                  TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                    (hB₂ : MeasurableSet B₂) :
                    TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                      TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
                  hash: expr=2593835776 text=4cbdd3a7ba3e5991
            [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
                TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
                  [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
                hash: expr=2980745689 text=d062a67869324a13
              [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
                  TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
                  hash: expr=2710346752 text=3040545541bf06a5
                [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                    TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                      [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                    hash: expr=4073139655 text=faa87465022c9f97
                  [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                      TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                        {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                        (R : E →L[𝕜] E) : Prop
                      field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                      field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                      field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                      hash: expr=3549903545 text=cba9f82aae5d40ca
                [body] TauCeti.LinearPMap.IsResolventAt  (above)
            [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
                TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
                  (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
                hash: expr=4155508021 text=b37a61963eed50ac
              [type] TauCeti.LinearPMap.cayley  (above)
            [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
                TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
                  Measurable (TauCeti.LinearPMap.cayleyInv hA)
                hash: expr=321618348 text=e943baa16723572d
      [body] TauCeti.RealComplexification  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:202)
          TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify.{v} {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
            TauCeti.RealComplexification E →ₗ.[ℂ] TauCeti.RealComplexification E
          hash: expr=319180028 text=b37652d39791961e
        [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:71)
            TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain.{v} {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
              Submodule ℂ (TauCeti.RealComplexification E)
            hash: expr=2420177506 text=e087bd3004ce1b40
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (def, DavisKahan/SpectralTheory/Complexification/Subspace.lean:45)
              TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule.{u_1} {E : Type u_1}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Submodule ℝ E) :
                Submodule ℂ (TauCeti.RealComplexification E)
              hash: expr=3786915484 text=ce5d0cdd7318abdd
            [type] TauCeti.RealComplexification  (above)
            [body] TauCeti.RealComplexification.re  (above)
            [body] TauCeti.RealComplexification.im  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:115)
                TauCeti.RealComplexification.im.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
                hash: expr=2897469443 text=1ee09de9c3b20d00
              [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:96)
            TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap.{v} {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
              ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A) →ₗ[ℂ]
                TauCeti.RealComplexification E
            hash: expr=3577002504 text=5dca1e23683a16f5
          [type] TauCeti.RealComplexification  (above)
          [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
          [body] TauCeti.RealComplexification.mk  (above)
          [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:84)
              TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe.{v} {E : Type v}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
                (z : ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A)) : ↥A.domain
              hash: expr=2785441133 text=410c166af5d8ede6
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
            [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:90)
              TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm.{v} {E : Type v}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
                (z : ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A)) : ↥A.domain
              hash: expr=2785441133 text=410c166af5d8ede6
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
            [body] TauCeti.RealComplexification.im  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify  (theorem, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:607)
          TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify.{v}
            {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E}
            (hA : IsSelfAdjoint A) :
            IsSelfAdjoint (TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify A)
          hash: expr=148782383 text=1cf221fc6bb0b7cb
  [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:650)
      TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
        (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
        ↥(TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS) →ₗ.[ℝ]
          ↥(TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS)
      hash: expr=3557671409 text=a68faeaf65be9200
    [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace  (above)
    [body] TauCeti.LinearPMap.reducingRestriction  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:236)
        TauCeti.LinearPMap.reducingRestriction.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
          [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) : ↥U →ₗ.[𝕜] ↥U
        hash: expr=919990832 text=6294b55e071b60e3
      [type] TauCeti.LinearPMap.ReducesSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:98)
          TauCeti.LinearPMap.ReducesSubspace.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
            [U.HasOrthogonalProjection] : Prop
          hash: expr=2182083140 text=ca42901128d27dd3
        [body] TauCeti.LinearPMap.InvariantSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:92)
            TauCeti.LinearPMap.InvariantSubspace.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) : Prop
            hash: expr=687545939 text=e719e4c9ef5bb4bd
      [body] TauCeti.LinearPMap.reducingRestrictionDomain  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:159)
          TauCeti.LinearPMap.reducingRestrictionDomain.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) :
            Submodule 𝕜 ↥U
          hash: expr=1322056522 text=cded76d807ce10df
      [body] TauCeti.LinearPMap.reducingRestrictionLinearMap  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:188)
          TauCeti.LinearPMap.reducingRestrictionLinearMap.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
            [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) :
            ↥(TauCeti.LinearPMap.reducingRestrictionDomain A U) →ₗ[𝕜] ↥U
          hash: expr=3070761079 text=783c5bf7467bcae2
        [type] TauCeti.LinearPMap.ReducesSubspace  (above)
        [type] TauCeti.LinearPMap.reducingRestrictionDomain  (above)
        [body] TauCeti.LinearPMap.reducingRestrictionDomainToAmbient  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:175)
            TauCeti.LinearPMap.reducingRestrictionDomainToAmbient.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
              (x : ↥(TauCeti.LinearPMap.reducingRestrictionDomain A U)) : ↥A.domain
            hash: expr=124560700 text=29ce882e442a8596
          [type] TauCeti.LinearPMap.reducingRestrictionDomain  (above)
    [body] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing  (theorem, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:596)
        TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing.{v} {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
          (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
          TauCeti.LinearPMap.ReducesSubspace A
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS)
        hash: expr=2538579909 text=bc3b439bb5002b58
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.RealComplexification  (above)
  [type] TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC  (def, DavisKahan/Geometry/Angle/OperatorAngleReal.lean:61)
      TauCeti.DavisKahanExt.Real.directedSinTwoAngleOperatorRC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℝ E] [CompleteSpace E] (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification E
      hash: expr=3009427235 text=a8debc00391f4005
    [type] TauCeti.RealComplexification  (above)
    [body] TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:255)
        TauCeti.DavisKahanExt.directedSinTwoAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.directedSinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:109)
          TauCeti.DavisKahanExt.directedSinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
            ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
              [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
              [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
            hash: expr=299460441 text=f21cf18f7b7963ad
      [body] TauCeti.DavisKahanExt.directedCosAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:70)
          TauCeti.DavisKahanExt.directedCosAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] ContinuousLinearMap.modulus  (above)
    [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (above)
  [type] TauCeti.LinearPMap.addBounded  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:872)
      TauCeti.LinearPMap.addBounded.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E
      hash: expr=66748006 text=2a4b564ad9f00a78
  [type] TauCeti.DavisKahan.addBounded_isSelfAdjoint  (theorem, DavisKahan/SinTheta/BoundedPerturbation.lean:60)
      TauCeti.DavisKahan.addBounded_isSelfAdjoint.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H →ₗ.[𝕜] H)
        (hA : IsSelfAdjoint A) (V : H →L[𝕜] H) (hV : TauCeti.DavisKahan.IsSelfAdjointOperator V) :
        IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
      hash: expr=611105799 text=2114ceedd875afc0
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

68 project constant(s) unfolded, 9 project leaf/leaves, 99 boundary constant(s), 347 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, LinearPMap, RingHom.id, IsSelfAdjoint, ContinuousLinearMap, Set, MeasurableSet, Subtype, Submodule, MeasurableSet.compl, And, Complex, Nat, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, LinearMap.IsSymmetric, LinearMap.range, Ne, WithLp, Prod, Submodule.HasOrthogonalProjection, LinearMap, LinearMap.domRestrict, ENNReal.toReal, FiniteDimensional, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set.Icc, Set.ofPred, AddMonoidHom, LinearPMap.toFun', iSup, ENNReal.ofReal, AddCommGroup, NormedSpace, Module, Module.ofMinimalAxioms, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, LinearIsometry, LinearMap.mkContinuous, Submodule.starProjection, Submodule.orthogonal, SMul, ContinuousLinearMap.comp, Exists, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.adjoint, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, NontriviallyNormedField, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, Set.indicator, Set.preimage, MeasureTheory.Measure.map, Exists.choose, RealRMK.rieszMeasure, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean:286`

~~~~lean
variable {Hc : Type v}
  [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
theorem sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex.{v}
  {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Hc →ₗ.[ℂ] Hc)
  (hA : IsSelfAdjoint A) (Eop : Hc →L[ℂ] Hc) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
  (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
  (hgap :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
  (hEmem : N.Mem Eop) :
  N.Mem
      (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
        (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯ S
          hS)) ∧
    δ *
        N.gauge
          (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯
              S hS)) ≤
      2 * N.gauge Eop
~~~~

Structural type hash `2000542141`, printed-type hash `b0e505a8268c9814`.

Statement closure: 50 project constant(s) unfolded, 7 project leaf/leaves, 96 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.IsSelfAdjointOperator`, `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.selfAdjointSpectralSubspace`, `TauCeti.DavisKahan.selfAdjointSpectralRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.LinearPMap.addBounded`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.pvmRangeSubspace`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.LinearPMap.specRestrict`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.DavisKahanExt.angleOperatorC`, `TauCeti.diagOp`, `TauCeti.LinearPMap.realSpectrum`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.LinearPMap.specRange`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.DavisKahanExt.sinAngleOperatorC`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.LinearPMap.specProjection`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `ContinuousLinearMap.modulus`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.ApproximationNumber.approximationSingularValue`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan.addBounded_isSelfAdjoint`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `IsSelfAdjoint`, `ContinuousLinearMap`, `Set`, `Real`, `MeasurableSet`, `Subtype`, `Submodule`, `MeasurableSet.compl`, `And`, `Nat`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `LinearMap.IsSymmetric`, `Ne`, `Submodule.HasOrthogonalProjection`, `cfc`, `Real.sin`, `LinearMap`, `LinearMap.domRestrict`, `ENNReal.toReal`, `FiniteDimensional`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `LinearPMap.toFun'`, `LinearMap.range`, `Submodule.comap`, `Submodule.subtype`, `iSup`, `ENNReal.ofReal`, `Real.arcsin`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Submodule.starProjection`, `Exists`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `NormedSpace`, `Exists.choose`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.comp`, `ContinuousLinearMap.adjoint`, `LinearMap.mkContinuous`, `RealRMK.rieszMeasure`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean:271)
    TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex.{v}
      {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Hc →ₗ.[ℂ] Hc)
      (hA : IsSelfAdjoint A) (Eop : Hc →L[ℂ] Hc) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
      (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
      (hgap :
        TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
          (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB)
          (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
      (hEmem : N.Mem Eop) :
      N.Mem
          (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯ S
              hS)) ∧
        δ *
            N.gauge
              (TauCeti.DavisKahanExt.sinTwoAngleOperatorC
                (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
                (TauCeti.DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop) ⋯
                  S hS)) ≤
          2 * N.gauge Eop
    hash: expr=2000542141 text=b0e505a8268c9814
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.IsSelfAdjointOperator  (def, DavisKahan/BoundedOperator/Compat.lean:64)
      TauCeti.DavisKahan.IsSelfAdjointOperator.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →L[𝕜] E) : Prop
      hash: expr=2922739529 text=fcde7e035a15c851
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.selfAdjointSpectralSubspace  (def, DavisKahan/SpectralTheory/SpectralRestriction.lean:62)
      TauCeti.DavisKahan.selfAdjointSpectralSubspace.{u_1} {H : Type u_1} [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
        (hB : MeasurableSet B) : Submodule ℂ H
      hash: expr=3996704367 text=e1824c7e6cb35d29
    [body] TauCeti.pvmRangeSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Subspace.lean:51)
        TauCeti.pvmRangeSubspace.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] (P : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) :
          Submodule ℂ H
        hash: expr=3793749016 text=ac2df232fd76eb3a
      [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
          TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] : Type u_2
          field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
          field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
          field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
          field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
          field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
          field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
          hash: expr=2326492630 text=8a7f2f92f7e6cb25
    [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
        TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
        hash: expr=1025771960 text=03d8a0e1bace7dda
      [type] TauCeti.ProjValMeasure  (above)
      [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
          TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
            {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
          hash: expr=3192152571 text=38dbb03b36baa07e
        [type] TauCeti.ProjValMeasure  (above)
        [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
            TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
              (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=6169287 text=22cb14432afff4f4
          [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
              TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
              hash: expr=2377768205 text=1636dc1e3618d340
            [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                hash: expr=2489458960 text=438ae027281cfbf3
            [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                hash: expr=3802524166 text=6359a60df1615396
              [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
              [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                  TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                  hash: expr=1909853194 text=b5d0ecb89e77cc8a
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                    TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                      [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                    hash: expr=3546105377 text=12fa953afc9438d3
                  [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                      TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                        MeasureTheory.Measure ↑(spectrum ℂ a)
                      hash: expr=2083923581 text=098301ad89533cf1
                    [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                        TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                          CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                        hash: expr=1299686186 text=681fa6315915ecf0
                      [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                          TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                          hash: expr=1488155521 text=8b20cf9e9db8beeb
                [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                    TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                      (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                    hash: expr=2675746042 text=64520af0639dba43
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
            [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
            [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                  ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                hash: expr=1978111998 text=fb2d00c2b9b8b360
        [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
            TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
              MeasureTheory.Measure ℝ
            hash: expr=1112489121 text=ea1d4ee13b3b4c3a
          [body] TauCeti.BorelCalculus.diagMeasure  (above)
        [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
            TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
              MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
            hash: expr=4257216657 text=b6885b32b095cce4
        [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
            TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
              inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
            hash: expr=3553813407 text=cfd94b77fa277777
        [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
            TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
              TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
            hash: expr=4063104685 text=e7abf70c80874ae5
        [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
            TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
              (hB₂ : MeasurableSet B₂) :
              TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
            hash: expr=2593835776 text=4cbdd3a7ba3e5991
      [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
          TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
            [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
          hash: expr=2980745689 text=d062a67869324a13
        [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
            TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
              [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
            hash: expr=2710346752 text=3040545541bf06a5
          [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
              TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
              hash: expr=4073139655 text=faa87465022c9f97
            [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                  (R : E →L[𝕜] E) : Prop
                field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                hash: expr=3549903545 text=cba9f82aae5d40ca
          [body] TauCeti.LinearPMap.IsResolventAt  (above)
      [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
          TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
            (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
          hash: expr=4155508021 text=b37a61963eed50ac
        [type] TauCeti.LinearPMap.cayley  (above)
      [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
          TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
            Measurable (TauCeti.LinearPMap.cayleyInv hA)
          hash: expr=321618348 text=e943baa16723572d
  [type] TauCeti.DavisKahan.selfAdjointSpectralRestriction  (def, DavisKahan/SpectralTheory/SpectralRestrictionOperator.lean:48)
      TauCeti.DavisKahan.selfAdjointSpectralRestriction.{u_1} {H : Type u_1} [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
        (hB : MeasurableSet B) :
        ↥(TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) →ₗ.[ℂ]
          ↥(TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB)
      hash: expr=864234461 text=f3a1baeba947f2f2
    [type] TauCeti.DavisKahan.selfAdjointSpectralSubspace  (above)
    [body] TauCeti.LinearPMap.specRestrict  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:704)
        TauCeti.LinearPMap.specRestrict.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
          [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
          ↥(TauCeti.LinearPMap.specRange hA B hB) →ₗ.[ℂ] ↥(TauCeti.LinearPMap.specRange hA B hB)
        hash: expr=2244333113 text=6e0452ccd1264842
      [type] TauCeti.LinearPMap.specRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:584)
          TauCeti.LinearPMap.specRange.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
            Submodule ℂ H
          hash: expr=3996704367 text=044a08326e510c21
        [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
            TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
              (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=1748688050 text=b7b417789e21c33b
          [body] TauCeti.LinearPMap.spectralPVM  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.sinTwoAngleOperatorC  (def, DavisKahan/Geometry/Angle/DoubleAngleFunctionalCalculus.lean:60)
      TauCeti.DavisKahanExt.sinTwoAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℂ] E
      hash: expr=187490045 text=178745a4708f5513
    [body] TauCeti.DavisKahanExt.angleOperatorC  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean:84)
        TauCeti.DavisKahanExt.angleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.sinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:38)
          TauCeti.DavisKahanExt.sinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
            ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
              [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
              [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
            hash: expr=299460441 text=f21cf18f7b7963ad
  [type] TauCeti.LinearPMap.addBounded  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:872)
      TauCeti.LinearPMap.addBounded.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E
      hash: expr=66748006 text=2a4b564ad9f00a78
  [type] TauCeti.DavisKahan.addBounded_isSelfAdjoint  (theorem, DavisKahan/SinTheta/BoundedPerturbation.lean:60)
      TauCeti.DavisKahan.addBounded_isSelfAdjoint.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H →ₗ.[𝕜] H)
        (hA : IsSelfAdjoint A) (V : H →L[𝕜] H) (hV : TauCeti.DavisKahan.IsSelfAdjointOperator V) :
        IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
      hash: expr=611105799 text=2114ceedd875afc0
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

50 project constant(s) unfolded, 7 project leaf/leaves, 96 boundary constant(s), 294 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, IsSelfAdjoint, ContinuousLinearMap, Set, Real, MeasurableSet, Subtype, Submodule, MeasurableSet.compl, And, Nat, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, LinearMap.IsSymmetric, Ne, Submodule.HasOrthogonalProjection, cfc, Real.sin, LinearMap, LinearMap.domRestrict, ENNReal.toReal, FiniteDimensional, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set.Icc, Set.ofPred, AddMonoidHom, LinearPMap.toFun', LinearMap.range, Submodule.comap, Submodule.subtype, iSup, ENNReal.ofReal, Real.arcsin, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Submodule.starProjection, Exists, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, NormedSpace, Exists.choose, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.comp, ContinuousLinearMap.adjoint, LinearMap.mkContinuous, RealRMK.rieszMeasure, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean:421`

~~~~lean
variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
theorem sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : Er →ₗ.[ℝ] Er) (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.sinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.sinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real.{v}
  {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Er →ₗ.[ℝ] Er)
  (hA : IsSelfAdjoint A) (Eop : Er →L[ℝ] Er) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
  (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
  (hgap :
    TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
  (hEmem : N.Mem Eop) :
  N.Mem
      (TauCeti.DavisKahanExt.sinTwoAngleOperatorR
        (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
        (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
          (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ∧
    δ *
        N.gauge
          (TauCeti.DavisKahanExt.sinTwoAngleOperatorR
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
              (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ≤
      2 * N.gauge Eop
~~~~

Structural type hash `369870179`, printed-type hash `52bfefcf38cbbebd`.

Statement closure: 68 project constant(s) unfolded, 9 project leaf/leaves, 102 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.DavisKahan.IsSelfAdjointOperator`, `TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahanExt.sinTwoAngleOperatorR`, `TauCeti.LinearPMap.addBounded`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap`, `TauCeti.LinearPMap.SemiboundedBelow`, `TauCeti.LinearPMap.SemiboundedAbove`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection`, `TauCeti.LinearPMap.reducingRestriction`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.RealComplexification.realPartOperator`, `TauCeti.RealComplexification`, `TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule`, `TauCeti.diagOp`, `TauCeti.LinearPMap.realSpectrum`, `TauCeti.DavisKahan.selfAdjointSpectralProjection`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify`, `TauCeti.LinearPMap.ReducesSubspace`, `TauCeti.LinearPMap.reducingRestrictionDomain`, `TauCeti.LinearPMap.reducingRestrictionLinearMap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.RealComplexification.re`, `TauCeti.RealComplexification.ofReal`, `TauCeti.DavisKahanExt.angleOperatorC`, `TauCeti.RealComplexification.im`, `TauCeti.LinearPMap.realResolventSet`, `TauCeti.LinearPMap.specProjection`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap`, `TauCeti.LinearPMap.InvariantSubspace`, `TauCeti.LinearPMap.reducingRestrictionDomainToAmbient`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.RealComplexification.mk`, `TauCeti.DavisKahanExt.sinAngleOperatorC`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm`, `TauCeti.ApproximationNumber.approximationSingularValue`, `ContinuousLinearMap.modulus`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan.addBounded_isSelfAdjoint`, `TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing`, `TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.residual`, `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `IsSelfAdjoint`, `ContinuousLinearMap`, `Set`, `MeasurableSet`, `Subtype`, `Submodule`, `MeasurableSet.compl`, `And`, `Nat`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `LinearMap.IsSymmetric`, `LinearMap.range`, `Ne`, `Submodule.HasOrthogonalProjection`, `LinearMap`, `LinearMap.domRestrict`, `ENNReal.toReal`, `FiniteDimensional`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `Or`, `Set.Icc`, `Set.ofPred`, `AddMonoidHom`, `LinearPMap.toFun'`, `iSup`, `ENNReal.ofReal`, `LinearIsometry`, `LinearMap.mkContinuous`, `cfc`, `Real.sin`, `WithLp`, `Prod`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `Submodule.starProjection`, `Submodule.orthogonal`, `AddCommGroup`, `Module`, `Module.ofMinimalAxioms`, `NormedSpace`, `Real.arcsin`, `Exists`, `SMul`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.comp`, `ContinuousLinearMap.adjoint`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `NontriviallyNormedField`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `Exists.choose`, `RealRMK.rieszMeasure`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean:405)
    TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_real.{v}
      {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : Er →ₗ.[ℝ] Er)
      (hA : IsSelfAdjoint A) (Eop : Er →L[ℝ] Er) (hEop : TauCeti.DavisKahan.IsSelfAdjointOperator Eop)
      (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
      (hgap :
        TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
          (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
          (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ)
      (hEmem : N.Mem Eop) :
      N.Mem
          (TauCeti.DavisKahanExt.sinTwoAngleOperatorR
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
              (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ∧
        δ *
            N.gauge
              (TauCeti.DavisKahanExt.sinTwoAngleOperatorR
                (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB)
                (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace
                  (TauCeti.LinearPMap.addBounded A Eop) ⋯ S hS)) ≤
          2 * N.gauge Eop
    hash: expr=369870179 text=52bfefcf38cbbebd
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.DavisKahan.IsSelfAdjointOperator  (def, DavisKahan/BoundedOperator/Compat.lean:64)
      TauCeti.DavisKahan.IsSelfAdjointOperator.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →L[𝕜] E) : Prop
      hash: expr=2922739529 text=fcde7e035a15c851
  [type] TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap  (inductive, DavisKahan/Sylvester/Gap.lean:89)
      TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop
      hash: expr=2173696262 text=0a578031be748839
    [body] TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap  (def, DavisKahan/Sylvester/Gap.lean:69)
        TauCeti.DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap.{u, v} {𝕜 : Type u} [RCLike 𝕜]
          {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop
        hash: expr=2863710028 text=d03decb261dc925e
      [body] TauCeti.LinearPMap.realSpectrum  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1014)
          TauCeti.LinearPMap.realSpectrum.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
          hash: expr=2431531687 text=f80cdbeca9241fe9
        [body] TauCeti.LinearPMap.realResolventSet  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:993)
            TauCeti.LinearPMap.realResolventSet.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set ℝ
            hash: expr=2431531687 text=f80cdbeca9241fe9
    [body] TauCeti.LinearPMap.SemiboundedBelow  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:41)
        TauCeti.LinearPMap.SemiboundedBelow.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
    [body] TauCeti.LinearPMap.SemiboundedAbove  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean:46)
        TauCeti.LinearPMap.SemiboundedAbove.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (c : ℝ) : Prop
        hash: expr=2572923451 text=35989daa25bdd1c4
  [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:416)
      TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
        (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) : Submodule ℝ E
      hash: expr=4005423199 text=f71755d5d60c952e
    [body] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:345)
        TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralProjection.{v} {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
          (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) : E →L[ℝ] E
        hash: expr=3802734145 text=ac644fbaa093c418
      [body] TauCeti.RealComplexification.realPartOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:509)
          TauCeti.RealComplexification.realPartOperator.{u_1, u_2} {E : Type u_1} {F : Type u_2}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
            (T : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification F) : E →L[ℝ] F
          hash: expr=3255006892 text=5b4b316d076d7dac
        [type] TauCeti.RealComplexification  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:66)
            TauCeti.RealComplexification.{u_1} (E : Type u_1) : Type u_1
            hash: expr=1219222929 text=b115962a62bfdf78
        [body] TauCeti.RealComplexification.re  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:110)
            TauCeti.RealComplexification.re.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
            hash: expr=2897469443 text=1ee09de9c3b20d00
          [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.RealComplexification.ofReal  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:263)
            TauCeti.RealComplexification.ofReal.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] : E →ₗᵢ[ℝ] TauCeti.RealComplexification E
            hash: expr=2088652411 text=71b15fd88eac82fd
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.mk  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:105)
              TauCeti.RealComplexification.mk.{u_1} {E : Type u_1} (x y : E) : TauCeti.RealComplexification E
              hash: expr=2390836649 text=76af0c3ed38ec24a
            [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.DavisKahan.selfAdjointSpectralProjection  (def, DavisKahan/SpectralTheory/SpectralRestriction.lean:56)
          TauCeti.DavisKahan.selfAdjointSpectralProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (B : Set ℝ)
            (hB : MeasurableSet B) : H →L[ℂ] H
          hash: expr=1748688050 text=e4656068c7b20c48
        [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
            TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
              (hB : MeasurableSet B) : H →L[ℂ] H
            hash: expr=1748688050 text=b7b417789e21c33b
          [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
              TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
              hash: expr=1025771960 text=03d8a0e1bace7dda
            [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
                TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] : Type u_2
                field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
                field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
                field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
                field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
                field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
                hash: expr=2326492630 text=8a7f2f92f7e6cb25
            [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
                TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
                hash: expr=3192152571 text=38dbb03b36baa07e
              [type] TauCeti.ProjValMeasure  (above)
              [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
                  TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                    [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                    (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
                  hash: expr=6169287 text=22cb14432afff4f4
                [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                    TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                    hash: expr=2377768205 text=1636dc1e3618d340
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                      TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                      field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                      field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                      hash: expr=2489458960 text=438ae027281cfbf3
                  [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                      TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                      hash: expr=3802524166 text=6359a60df1615396
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                    [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                        TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                          {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                        hash: expr=1909853194 text=b5d0ecb89e77cc8a
                      [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                      [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                          TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                            [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                          hash: expr=3546105377 text=12fa953afc9438d3
                        [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                            TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                              MeasureTheory.Measure ↑(spectrum ℂ a)
                            hash: expr=2083923581 text=098301ad89533cf1
                          [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                              TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                                CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                              hash: expr=1299686186 text=681fa6315915ecf0
                            [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                                TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                                hash: expr=1488155521 text=8b20cf9e9db8beeb
                      [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                          TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                            (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                          hash: expr=2675746042 text=64520af0639dba43
                        [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
                  [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                      TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                        ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                      hash: expr=1978111998 text=fb2d00c2b9b8b360
              [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
                  TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                    [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                    MeasureTheory.Measure ℝ
                  hash: expr=1112489121 text=ea1d4ee13b3b4c3a
                [body] TauCeti.BorelCalculus.diagMeasure  (above)
              [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
                  TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                    MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
                  hash: expr=4257216657 text=b6885b32b095cce4
              [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
                  TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                    inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                      ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
                  hash: expr=3553813407 text=cfd94b77fa277777
              [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
                  TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                    TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                  hash: expr=4063104685 text=e7abf70c80874ae5
              [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
                  TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                    (hB₂ : MeasurableSet B₂) :
                    TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                      TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
                  hash: expr=2593835776 text=4cbdd3a7ba3e5991
            [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
                TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
                  [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
                hash: expr=2980745689 text=d062a67869324a13
              [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
                  TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
                  hash: expr=2710346752 text=3040545541bf06a5
                [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                    TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                      [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                    hash: expr=4073139655 text=faa87465022c9f97
                  [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                      TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                        {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                        (R : E →L[𝕜] E) : Prop
                      field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                      field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                      field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                      hash: expr=3549903545 text=cba9f82aae5d40ca
                [body] TauCeti.LinearPMap.IsResolventAt  (above)
            [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
                TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
                  (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
                hash: expr=4155508021 text=b37a61963eed50ac
              [type] TauCeti.LinearPMap.cayley  (above)
            [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
                TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
                  Measurable (TauCeti.LinearPMap.cayleyInv hA)
                hash: expr=321618348 text=e943baa16723572d
      [body] TauCeti.RealComplexification  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:202)
          TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify.{v} {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
            TauCeti.RealComplexification E →ₗ.[ℂ] TauCeti.RealComplexification E
          hash: expr=319180028 text=b37652d39791961e
        [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:71)
            TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain.{v} {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
              Submodule ℂ (TauCeti.RealComplexification E)
            hash: expr=2420177506 text=e087bd3004ce1b40
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (def, DavisKahan/SpectralTheory/Complexification/Subspace.lean:45)
              TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule.{u_1} {E : Type u_1}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Submodule ℝ E) :
                Submodule ℂ (TauCeti.RealComplexification E)
              hash: expr=3786915484 text=ce5d0cdd7318abdd
            [type] TauCeti.RealComplexification  (above)
            [body] TauCeti.RealComplexification.re  (above)
            [body] TauCeti.RealComplexification.im  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:115)
                TauCeti.RealComplexification.im.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
                hash: expr=2897469443 text=1ee09de9c3b20d00
              [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:96)
            TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.linearMap.{v} {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) :
              ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A) →ₗ[ℂ]
                TauCeti.RealComplexification E
            hash: expr=3577002504 text=5dca1e23683a16f5
          [type] TauCeti.RealComplexification  (above)
          [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
          [body] TauCeti.RealComplexification.mk  (above)
          [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:84)
              TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainRe.{v} {E : Type v}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
                (z : ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A)) : ↥A.domain
              hash: expr=2785441133 text=410c166af5d8ede6
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
            [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm  (def, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:90)
              TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domainIm.{v} {E : Type v}
                [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E)
                (z : ↥(TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain A)) : ↥A.domain
              hash: expr=2785441133 text=410c166af5d8ede6
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.domain  (above)
            [body] TauCeti.RealComplexification.im  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify  (theorem, DavisKahan/SpectralTheory/PartialMap/Complexification.lean:607)
          TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify.{v}
            {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E}
            (hA : IsSelfAdjoint A) :
            IsSelfAdjoint (TauCeti.DavisKahan.ExactSinTheta.PartialMapComplexification.complexify A)
          hash: expr=148782383 text=1cf221fc6bb0b7cb
  [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction  (def, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:650)
      TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction.{v} {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
        (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
        ↥(TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS) →ₗ.[ℝ]
          ↥(TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS)
      hash: expr=3557671409 text=a68faeaf65be9200
    [type] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace  (above)
    [body] TauCeti.LinearPMap.reducingRestriction  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:236)
        TauCeti.LinearPMap.reducingRestriction.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
          [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) : ↥U →ₗ.[𝕜] ↥U
        hash: expr=919990832 text=6294b55e071b60e3
      [type] TauCeti.LinearPMap.ReducesSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:98)
          TauCeti.LinearPMap.ReducesSubspace.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
            [U.HasOrthogonalProjection] : Prop
          hash: expr=2182083140 text=ca42901128d27dd3
        [body] TauCeti.LinearPMap.InvariantSubspace  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:92)
            TauCeti.LinearPMap.InvariantSubspace.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) : Prop
            hash: expr=687545939 text=e719e4c9ef5bb4bd
      [body] TauCeti.LinearPMap.reducingRestrictionDomain  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:159)
          TauCeti.LinearPMap.reducingRestrictionDomain.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) :
            Submodule 𝕜 ↥U
          hash: expr=1322056522 text=cded76d807ce10df
      [body] TauCeti.LinearPMap.reducingRestrictionLinearMap  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:188)
          TauCeti.LinearPMap.reducingRestrictionLinearMap.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
            [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
            [U.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace A U) :
            ↥(TauCeti.LinearPMap.reducingRestrictionDomain A U) →ₗ[𝕜] ↥U
          hash: expr=3070761079 text=783c5bf7467bcae2
        [type] TauCeti.LinearPMap.ReducesSubspace  (above)
        [type] TauCeti.LinearPMap.reducingRestrictionDomain  (above)
        [body] TauCeti.LinearPMap.reducingRestrictionDomainToAmbient  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:175)
            TauCeti.LinearPMap.reducingRestrictionDomainToAmbient.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
              (x : ↥(TauCeti.LinearPMap.reducingRestrictionDomain A U)) : ↥A.domain
            hash: expr=124560700 text=29ce882e442a8596
          [type] TauCeti.LinearPMap.reducingRestrictionDomain  (above)
    [body] TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing  (theorem, DavisKahan/SpectralTheory/Real/SpectralRestriction.lean:596)
        TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing.{v} {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →ₗ.[ℝ] E)
          (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
          TauCeti.LinearPMap.ReducesSubspace A
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA S hS)
        hash: expr=2538579909 text=bc3b439bb5002b58
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.sinTwoAngleOperatorR  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculusReal.lean:121)
      TauCeti.DavisKahanExt.sinTwoAngleOperatorR.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℝ E] [CompleteSpace E] (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℝ] E
      hash: expr=2215108693 text=ca05c2be87f84df1
    [body] TauCeti.RealComplexification.realPartOperator  (above)
    [body] TauCeti.DavisKahanExt.sinTwoAngleOperatorC  (def, DavisKahan/Geometry/Angle/DoubleAngleFunctionalCalculus.lean:60)
        TauCeti.DavisKahanExt.sinTwoAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.angleOperatorC  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean:84)
          TauCeti.DavisKahanExt.angleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] TauCeti.DavisKahanExt.sinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:38)
            TauCeti.DavisKahanExt.sinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
              [V.HasOrthogonalProjection] : E →L[ℂ] E
            hash: expr=187490045 text=178745a4708f5513
          [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
              ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
                [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
                [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
              hash: expr=299460441 text=f21cf18f7b7963ad
    [body] TauCeti.RealComplexification  (above)
    [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (above)
  [type] TauCeti.LinearPMap.addBounded  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:872)
      TauCeti.LinearPMap.addBounded.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E
      hash: expr=66748006 text=2a4b564ad9f00a78
  [type] TauCeti.DavisKahan.addBounded_isSelfAdjoint  (theorem, DavisKahan/SinTheta/BoundedPerturbation.lean:60)
      TauCeti.DavisKahan.addBounded_isSelfAdjoint.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H →ₗ.[𝕜] H)
        (hA : IsSelfAdjoint A) (V : H →L[𝕜] H) (hV : TauCeti.DavisKahan.IsSelfAdjointOperator V) :
        IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
      hash: expr=611105799 text=2114ceedd875afc0
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

68 project constant(s) unfolded, 9 project leaf/leaves, 102 boundary constant(s), 347 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, LinearPMap, RingHom.id, IsSelfAdjoint, ContinuousLinearMap, Set, MeasurableSet, Subtype, Submodule, MeasurableSet.compl, And, Nat, Complex, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, LinearMap.IsSymmetric, LinearMap.range, Ne, Submodule.HasOrthogonalProjection, LinearMap, LinearMap.domRestrict, ENNReal.toReal, FiniteDimensional, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, Or, Set.Icc, Set.ofPred, AddMonoidHom, LinearPMap.toFun', iSup, ENNReal.ofReal, LinearIsometry, LinearMap.mkContinuous, cfc, Real.sin, WithLp, Prod, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, Submodule.starProjection, Submodule.orthogonal, AddCommGroup, Module, Module.ofMinimalAxioms, NormedSpace, Real.arcsin, Exists, SMul, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.comp, ContinuousLinearMap.adjoint, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, NontriviallyNormedField, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, Set.indicator, Set.preimage, MeasureTheory.Measure.map, Exists.choose, RealRMK.rieszMeasure, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

### Supporting scope declarations

- `TauCeti.DavisKahan1970.sinTwoTheta_directed_boundedResidual_blockRepresentative_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_symmetricNorming_rclike` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_real` — elaborated; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction`

The literal source unitary-invariant norm. The new directed headline theorem evaluates it over generic RCLike scalars.

#### `TauCeti.DavisKahan.FiniteDimensional.sinTwoThetaEmbedding`

The rectangular directed sin(2 Theta0) representative used by the scalar-generic headline theorem.

#### `TauCeti.DavisKahan.residual`

The literal residual A X - X M appearing on the right-hand side of the directed theorem.

#### `TauCeti.DavisKahanExt.sinTwoAngleOperatorC`

The complex whole-space sin(2 Theta) operator used by the ambient perturbation scope companion.

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜] and uses SymmetricNormingFunction directly. | claimed_exact |
| Interval/exterior spectral separation by delta. | hCompressionSpectrum places M in [beta,alpha] and hUnwantedSpectrum literally places the unwanted A-spectrum outside (beta-delta,alpha+delta); no local gap structure is visible in the headline type. | claimed_exact |
| delta \|\|sin(2 Theta0)\|\| <= 2 \|\|R\|\|. | sinTwoTheta_directed_finiteDimensional_symmetricNorming_rclike concludes the factor-two SymmetricNormingFunction estimate for sinTwoThetaEmbedding U X against residual A X M. | claimed_exact |
| delta \|\|sin(2 Theta)\|\| <= 2 \|\|H\|\|. | sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex and its real sibling supply the ambient endpoint at the result's own unbounded scope: unbounded self-adjoint LinearPMap ambient operator, bounded self-adjoint perturbation, genuine spectral subspaces, the whole FormBoundedSylvesterGap, an arbitrary SymmetricNormingFunction and the exact factor two.  The bounded ambient theorems are their specialization. | claimed_exact |
| Infinite-dimensional and unbounded directed-residual scope. | Both printed conclusions are now witnessed at unbounded infinite-dimensional scope over each field.  The scalar-generic facade is finite-dimensional and is supporting evidence only; it is not this result's witness. | claimed_exact |

**Review note.** The directed residual conclusion now has a scalar-generic SymmetricNormingFunction facade with the interval/exterior hypotheses and residual written directly in its type. The ambient whole-space endpoint remains field-specific internally, so the complex source-shaped theorem stays as the second canonical declaration and its real sibling is a supporting scalar companion. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

2026-08-31: the canonical declaration list here is now the counted result's `canonical_evidence` in `dev/davis-kahan-1970-formalization-result-inventory.json`, and the checker enforces that. Demoted to supporting: TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_symmetricNorming_rclike -- a finite-dimensional or capability-class facade cannot be the canonical witness for a result certified at unbounded infinite-dimensional scope.

2026-08-31 (later the same day): the AMBIENT clause is no longer a scope companion.  `sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex` and its real sibling prove it at the row's own unbounded scope, by identifying the ambient double angle between U and V with an ambient SINGLE angle between U and its mirror image through V and applying the common-domain Proposition 6.1.  The bounded ambient endpoints are demoted to supporting evidence as their own specialization.

**Next action.** No hostile-review hole is currently recorded for this source passage. Preserve exact source scope and re-audit if the distributable source specification changes.

## C. Davis and W. M. Kahan, The Rotation of Eigenvectors by a Perturbation. III, SIAM J. Numer. Anal. 7(1), 1970, 1–46.: Davis--Kahan double-angle tan 2 theta theorem

The Section 2 tan(2 theta) theorem: an ordered gap and a fully off-diagonal perturbation give the directed residual and ambient perturbation bounds with factor two, without a separately assumed tangent-pole exclusion.

### Normalized source statement

**Setup**
- A0 and A1 are the two diagonal blocks of A, H0 and H1 are the diagonal perturbation blocks, R is the residual, H is the perturbation, and Theta0/Theta are directed/ambient angles.

**Hypotheses**
- spec(A0) is contained in [beta,alpha], spec(A1) is contained in [alpha+delta,infinity), and delta>0.
- H0=H1=0 (the perturbation is fully off diagonal).
- No independent hypothesis excluding poles of tan(2 Theta), and no separate spectral placement of the perturbed Lambda blocks, is part of the printed theorem.

**Conclusions**
- delta * ||tan(2 Theta0)|| <= 2 ||R||.
- delta * ||tan(2 Theta)|| <= 2 ||H||.

**Scope**
- Arbitrary source unitary-invariant norm, with real/complex and unbounded ambient companions.

### Canonical Lean declarations

#### `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExact.lean:77`

~~~~lean
variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]
theorem tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
    (hA : IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : G), hZdom x⟩ + B (Z (x : G)) = Z (A x) + Z (B (x : G)))
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b)
    (hRmem : N.Mem (blockCompression
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)) :
    IsUnit
        ((TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge (blockCompression
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex.{u}
  {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G}
  {a b c : ℝ} (hA : IsSelfAdjoint A)
  (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B) (hZsa : IsSelfAdjoint Z)
  (hZ2 : Z * Z = 1) (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x))
  (hUa :
    ∀ (x : ↥A.domain),
      ↑x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯ →
        RCLike.re (inner ℂ (↑A x) ↑x) ≤ a * ‖↑x‖ ^ 2)
  (hUb :
    ∀ (x : ↥A.domain),
      ↑x ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ →
        b * ‖↑x‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A x) ↑x))
  (hab : a < b)
  (hRmem :
    N.Mem
      (TauCeti.DavisKahan.ExactSinTheta.blockCompression
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)) :
  IsUnit
      ((TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯).diagonalPart Z *
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯).diagonalPart Z) ∧
    N.Mem
        (TauCeti.DavisKahan1970.reflectionTangentCorner
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) Z) ∧
      (b - a) *
          N.gauge
            (TauCeti.DavisKahan1970.reflectionTangentCorner
              (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) Z) ≤
        2 *
          N.gauge
            (TauCeti.DavisKahan.ExactSinTheta.blockCompression
              (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ
              (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)
~~~~

Structural type hash `2946508179`, printed-type hash `2f3a4e1c99e9c08f`.

Statement closure: 41 project constant(s) unfolded, 8 project leaf/leaves, 87 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.IsOddFor`, `TauCeti.LinearPMap.specRange`, `TauCeti.LinearPMap.MapsDomainTo`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan.ExactSinTheta.blockCompression`, `Submodule.diagonalPart`, `TauCeti.DavisKahan1970.reflectionTangentCorner`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.LinearPMap.specProjection`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.DavisKahan1970.unboundedReflectionTangent`, `TauCeti.diagOp`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `Submodule.offDiagonalPart`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedExact`, `TauCeti.DavisKahan.ExactSinTheta.instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.FiniteDimensional.absDoubleAngleTangent`, `TauCeti.DavisKahan1970.doubleSecant`, `TauCeti.DavisKahan1970.projectorDifference`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `Real`, `IsSelfAdjoint`, `Set.Iic`, `measurableSet_Iic`, `Eq`, `Subtype`, `Submodule`, `LinearPMap.toFun'`, `AddMonoidHom`, `Nat`, `Submodule.orthogonal`, `And`, `IsUnit`, `EuclideanSpace`, `Fin`, `ENNReal`, `EuclideanSpace.basisFun`, `RCLike`, `Set`, `MeasurableSet`, `LinearMap.range`, `Ne`, `Submodule.HasOrthogonalProjection`, `ContinuousLinearMap.comp`, `LinearIsometryEquiv`, `starRingEnd`, `ContinuousLinearMap.adjoint`, `Submodule.subtypeL`, `Submodule.starProjection`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `iSup`, `ENNReal.ofReal`, `Ring.inverse`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `InnerProductSpace.rankOne`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `NormedSpace`, `Exists.choose`, `LinearMap.mkContinuous`, `RealRMK.rieszMeasure`, `Set.ofPred`, `Exists`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExact.lean:60)
    TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex.{u}
      {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G}
      {a b c : ℝ} (hA : IsSelfAdjoint A)
      (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B) (hZsa : IsSelfAdjoint Z)
      (hZ2 : Z * Z = 1) (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
      (hZcomm : ∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x))
      (hUa :
        ∀ (x : ↥A.domain),
          ↑x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯ →
            RCLike.re (inner ℂ (↑A x) ↑x) ≤ a * ‖↑x‖ ^ 2)
      (hUb :
        ∀ (x : ↥A.domain),
          ↑x ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ →
            b * ‖↑x‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A x) ↑x))
      (hab : a < b)
      (hRmem :
        N.Mem
          (TauCeti.DavisKahan.ExactSinTheta.blockCompression
            (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ
            (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)) :
      IsUnit
          ((TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯).diagonalPart Z *
            (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯).diagonalPart Z) ∧
        N.Mem
            (TauCeti.DavisKahan1970.reflectionTangentCorner
              (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) Z) ∧
          (b - a) *
              N.gauge
                (TauCeti.DavisKahan1970.reflectionTangentCorner
                  (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) Z) ≤
            2 *
              N.gauge
                (TauCeti.DavisKahan.ExactSinTheta.blockCompression
                  (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ
                  (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)
    hash: expr=2946508179 text=2f3a4e1c99e9c08f
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.IsOddFor  (def, ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedReflection.lean:76)
      TauCeti.IsOddFor.{u_1, u_2} {𝕜 : Type u_1} {H : Type u_2} [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] (U : Submodule 𝕜 H) (B : H →L[𝕜] H) : Prop
      hash: expr=4245281075 text=f6fb5c101acd31be
  [type] TauCeti.LinearPMap.specRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:584)
      TauCeti.LinearPMap.specRange.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
        Submodule ℂ H
      hash: expr=3996704367 text=044a08326e510c21
    [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
        TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
          [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
          (hB : MeasurableSet B) : H →L[ℂ] H
        hash: expr=1748688050 text=b7b417789e21c33b
      [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
          TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
          hash: expr=1025771960 text=03d8a0e1bace7dda
        [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
            TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] : Type u_2
            field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
            field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
            field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
            field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
            field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
            field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
            hash: expr=2326492630 text=8a7f2f92f7e6cb25
        [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
            TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
            hash: expr=3192152571 text=38dbb03b36baa07e
          [type] TauCeti.ProjValMeasure  (above)
          [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
              TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
              hash: expr=6169287 text=22cb14432afff4f4
            [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                hash: expr=2377768205 text=1636dc1e3618d340
              [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                  TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                  field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                  field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                  hash: expr=2489458960 text=438ae027281cfbf3
              [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                  TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                  hash: expr=3802524166 text=6359a60df1615396
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                    TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                    hash: expr=1909853194 text=b5d0ecb89e77cc8a
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                      TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                        [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                      hash: expr=3546105377 text=12fa953afc9438d3
                    [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                        TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                          MeasureTheory.Measure ↑(spectrum ℂ a)
                        hash: expr=2083923581 text=098301ad89533cf1
                      [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                          TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                            CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                          hash: expr=1299686186 text=681fa6315915ecf0
                        [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                            TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                            hash: expr=1488155521 text=8b20cf9e9db8beeb
                  [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                      TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                        (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                      hash: expr=2675746042 text=64520af0639dba43
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
              [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
              [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                  TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                    ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                  hash: expr=1978111998 text=fb2d00c2b9b8b360
          [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
              TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                MeasureTheory.Measure ℝ
              hash: expr=1112489121 text=ea1d4ee13b3b4c3a
            [body] TauCeti.BorelCalculus.diagMeasure  (above)
          [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
              TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
              hash: expr=4257216657 text=b6885b32b095cce4
          [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
              TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                  ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
              hash: expr=3553813407 text=cfd94b77fa277777
          [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
              TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
              hash: expr=4063104685 text=e7abf70c80874ae5
          [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
              TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                (hB₂ : MeasurableSet B₂) :
                TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                  TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
              hash: expr=2593835776 text=4cbdd3a7ba3e5991
        [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
            TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
              [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
            hash: expr=2980745689 text=d062a67869324a13
          [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
              TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
              hash: expr=2710346752 text=3040545541bf06a5
            [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                hash: expr=4073139655 text=faa87465022c9f97
              [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                  TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                    {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                    (R : E →L[𝕜] E) : Prop
                  field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                  field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                  field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                  hash: expr=3549903545 text=cba9f82aae5d40ca
            [body] TauCeti.LinearPMap.IsResolventAt  (above)
        [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
            TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
              (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
            hash: expr=4155508021 text=b37a61963eed50ac
          [type] TauCeti.LinearPMap.cayley  (above)
        [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
            TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
              Measurable (TauCeti.LinearPMap.cayleyInv hA)
            hash: expr=321618348 text=e943baa16723572d
  [type] TauCeti.LinearPMap.MapsDomainTo  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:65)
      TauCeti.LinearPMap.MapsDomainTo.{u, v, w} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (X : F →L[𝕜] E) : Prop
      hash: expr=3340400931 text=044bcad4674dfaf8
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedExact  (theorem, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExact.lean:42)
      TauCeti.DavisKahan1970.instCompleteSpaceCoeOfHasOrthogonalProjectionUnboundedExact.{u} {G : Type u}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (W : Submodule ℂ G)
        [W.HasOrthogonalProjection] : CompleteSpace ↥W
      hash: expr=1317722915 text=adcae78b8367566c
  [type] TauCeti.DavisKahan.ExactSinTheta.blockCompression  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean:54)
      TauCeti.DavisKahan.ExactSinTheta.blockCompression.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (Ω Γ : Submodule 𝕜 E)
        [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection] (K : E →L[𝕜] E) : ↥Γ →L[𝕜] ↥Ω
      hash: expr=244603371 text=33c1f17fcf589162
    [body] TauCeti.DavisKahan.ExactSinTheta.instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61  (theorem, DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean:39)
        TauCeti.DavisKahan.ExactSinTheta.instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61.{u, v}
          {𝕜 : Type u} [RCLike 𝕜] {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
          [CompleteSpace G] (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace ↥U
        hash: expr=2771355356 text=cdbf1442689c5de1
  [type] Submodule.diagonalPart  (def, ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean:66)
      Submodule.diagonalPart.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
        E →L[𝕜] E
      hash: expr=3532409979 text=8ec1b7535939660f
  [type] TauCeti.DavisKahan1970.reflectionTangentCorner  (def, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramBridge.lean:270)
      TauCeti.DavisKahan1970.reflectionTangentCorner.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {G : Type u}
        [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G] (U : Submodule 𝕜 G)
        [U.HasOrthogonalProjection] (Z : G →L[𝕜] G) : ↥U →L[𝕜] ↥Uᗮ
      hash: expr=3938377629 text=e31c685a2b1630c9
    [body] TauCeti.DavisKahan.ExactSinTheta.blockCompression  (above)
    [body] TauCeti.DavisKahan1970.unboundedReflectionTangent  (def, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedKyFan.lean:2041)
        TauCeti.DavisKahan1970.unboundedReflectionTangent.{u_2, u_3} {𝕜 : Type u_2} [RCLike 𝕜]
          {G : Type u_3} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (U : Submodule 𝕜 G)
          [U.HasOrthogonalProjection] (Z : G →L[𝕜] G) : G →L[𝕜] G
        hash: expr=4055288565 text=32814c31f13a5e2e
      [body] Submodule.offDiagonalPart  (def, ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean:72)
          Submodule.offDiagonalPart.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
            E →L[𝕜] E
          hash: expr=3532409979 text=8ec1b7535939660f
        [body] Submodule.diagonalPart  (above)
      [body] Submodule.diagonalPart  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

41 project constant(s) unfolded, 8 project leaf/leaves, 87 boundary constant(s), 283 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, ContinuousLinearMap, Real, IsSelfAdjoint, Set.Iic, measurableSet_Iic, Eq, Subtype, Submodule, LinearPMap.toFun', AddMonoidHom, Nat, Submodule.orthogonal, And, IsUnit, EuclideanSpace, Fin, ENNReal, EuclideanSpace.basisFun, RCLike, Set, MeasurableSet, LinearMap.range, Ne, Submodule.HasOrthogonalProjection, ContinuousLinearMap.comp, LinearIsometryEquiv, starRingEnd, ContinuousLinearMap.adjoint, Submodule.subtypeL, Submodule.starProjection, ENNReal.toReal, FiniteDimensional, LinearMap, LinearMap.comp, OrthonormalBasis, Fin.lastCases, iSup, ENNReal.ofReal, Ring.inverse, Finset.sum, Finset.univ, RCLike.ofReal, InnerProductSpace.rankOne, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, NormedSpace, Exists.choose, LinearMap.mkContinuous, RealRMK.rieszMeasure, Set.ofPred, Exists, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:198`

~~~~lean
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
theorem tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E} {a b c : ℝ}
    (hA : _root_.IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic →
      ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b)
    (hRmem : N.Mem (reflectionResidualCorner
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)) :
    IsUnit
        ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge (reflectionResidualCorner
          (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real.{u}
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E}
  {a b c : ℝ} (hA : IsSelfAdjoint A)
  (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)
  (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x))
  (hUa :
    ∀ (x : ↥A.domain),
      ↑x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯ → inner ℝ (↑A x) ↑x ≤ a * ‖↑x‖ ^ 2)
  (hUb :
    ∀ (x : ↥A.domain),
      ↑x ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯)ᗮ → b * ‖↑x‖ ^ 2 ≤ inner ℝ (↑A x) ↑x)
  (hab : a < b)
  (hRmem :
    N.Mem
      (TauCeti.DavisKahan1970.reflectionResidualCorner
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)) :
  IsUnit
      ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯).diagonalPart Z *
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯).diagonalPart Z) ∧
    N.Mem
        (TauCeti.DavisKahan1970.reflectionTangentCorner
          (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) Z) ∧
      (b - a) *
          N.gauge
            (TauCeti.DavisKahan1970.reflectionTangentCorner
              (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) Z) ≤
        2 *
          N.gauge
            (TauCeti.DavisKahan1970.reflectionResidualCorner
              (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)
~~~~

Structural type hash `3512068222`, printed-type hash `20562477f7339ac9`.

Statement closure: 54 project constant(s) unfolded, 8 project leaf/leaves, 93 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.IsOddFor`, `TauCeti.LinearPMap.realSpecRange`, `TauCeti.LinearPMap.MapsDomainTo`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahan1970.reflectionResidualCorner`, `Submodule.diagonalPart`, `TauCeti.DavisKahan1970.reflectionTangentCorner`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.LinearPMap.realSpecProjection`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.DavisKahan.ExactSinTheta.blockCompression`, `TauCeti.DavisKahan1970.unboundedReflectionTangent`, `TauCeti.diagOp`, `TauCeti.RealComplexification.realPartOperator`, `TauCeti.LinearPMap.specProjection`, `TauCeti.RealComplexification`, `TauCeti.LinearPMap.complexifyReal`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `Submodule.offDiagonalPart`, `TauCeti.RealComplexification.re`, `TauCeti.RealComplexification.ofReal`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.RealComplexification.im`, `TauCeti.LinearPMap.complexificationDomain`, `TauCeti.LinearPMap.complexificationLinearMap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.RealComplexification.mk`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.LinearPMap.complexificationDomainRe`, `TauCeti.LinearPMap.complexificationDomainIm`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.LinearPMap.isSelfAdjoint_complexifyReal`, `TauCeti.DavisKahan.ExactSinTheta.instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.FiniteDimensional.absDoubleAngleTangent`, `TauCeti.DavisKahan1970.doubleSecant`, `TauCeti.DavisKahan1970.projectorDifference`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `IsSelfAdjoint`, `Set.Iic`, `measurableSet_Iic`, `Eq`, `Subtype`, `Submodule`, `LinearPMap.toFun'`, `Nat`, `Submodule.orthogonal`, `And`, `IsUnit`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `EuclideanSpace.basisFun`, `RCLike`, `Set`, `MeasurableSet`, `LinearMap.range`, `Ne`, `Submodule.HasOrthogonalProjection`, `ContinuousLinearMap.comp`, `Submodule.starProjection`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `iSup`, `ENNReal.ofReal`, `starRingEnd`, `ContinuousLinearMap.adjoint`, `Submodule.subtypeL`, `Ring.inverse`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `InnerProductSpace.rankOne`, `LinearIsometry`, `LinearMap.mkContinuous`, `WithLp`, `Prod`, `AddCommGroup`, `Module`, `Module.ofMinimalAxioms`, `NormedSpace`, `Set.ofPred`, `SMul`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `Exists.choose`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `RealRMK.rieszMeasure`, `Exists`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:193)
    TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real.{u}
      {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E}
      {a b c : ℝ} (hA : IsSelfAdjoint A)
      (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)
      (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
      (hZcomm : ∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x))
      (hUa :
        ∀ (x : ↥A.domain),
          ↑x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯ → inner ℝ (↑A x) ↑x ≤ a * ‖↑x‖ ^ 2)
      (hUb :
        ∀ (x : ↥A.domain),
          ↑x ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯)ᗮ → b * ‖↑x‖ ^ 2 ≤ inner ℝ (↑A x) ↑x)
      (hab : a < b)
      (hRmem :
        N.Mem
          (TauCeti.DavisKahan1970.reflectionResidualCorner
            (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)) :
      IsUnit
          ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯).diagonalPart Z *
            (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯).diagonalPart Z) ∧
        N.Mem
            (TauCeti.DavisKahan1970.reflectionTangentCorner
              (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) Z) ∧
          (b - a) *
              N.gauge
                (TauCeti.DavisKahan1970.reflectionTangentCorner
                  (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) Z) ≤
            2 *
              N.gauge
                (TauCeti.DavisKahan1970.reflectionResidualCorner
                  (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)
    hash: expr=3512068222 text=20562477f7339ac9
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.IsOddFor  (def, ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedReflection.lean:76)
      TauCeti.IsOddFor.{u_1, u_2} {𝕜 : Type u_1} {H : Type u_2} [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] (U : Submodule 𝕜 H) (B : H →L[𝕜] H) : Prop
      hash: expr=4245281075 text=f6fb5c101acd31be
  [type] TauCeti.LinearPMap.realSpecRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification/SpectralDescent.lean:338)
      TauCeti.LinearPMap.realSpecRange.{v} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
        Submodule ℝ E
      hash: expr=4005423199 text=f64f5562d5a2e705
    [body] TauCeti.LinearPMap.realSpecProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification/SpectralDescent.lean:278)
        TauCeti.LinearPMap.realSpecProjection.{v} {E : Type v} [NormedAddCommGroup E]
          [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A) (S : Set ℝ)
          (hS : MeasurableSet S) : E →L[ℝ] E
        hash: expr=3802734145 text=f26be7d693b8db3d
      [body] TauCeti.RealComplexification.realPartOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:509)
          TauCeti.RealComplexification.realPartOperator.{u_1, u_2} {E : Type u_1} {F : Type u_2}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
            (T : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification F) : E →L[ℝ] F
          hash: expr=3255006892 text=5b4b316d076d7dac
        [type] TauCeti.RealComplexification  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:66)
            TauCeti.RealComplexification.{u_1} (E : Type u_1) : Type u_1
            hash: expr=1219222929 text=b115962a62bfdf78
        [body] TauCeti.RealComplexification.re  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:110)
            TauCeti.RealComplexification.re.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
            hash: expr=2897469443 text=1ee09de9c3b20d00
          [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.RealComplexification.ofReal  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:263)
            TauCeti.RealComplexification.ofReal.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] : E →ₗᵢ[ℝ] TauCeti.RealComplexification E
            hash: expr=2088652411 text=71b15fd88eac82fd
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.mk  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:105)
              TauCeti.RealComplexification.mk.{u_1} {E : Type u_1} (x y : E) : TauCeti.RealComplexification E
              hash: expr=2390836649 text=76af0c3ed38ec24a
            [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
          TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
            (hB : MeasurableSet B) : H →L[ℂ] H
          hash: expr=1748688050 text=b7b417789e21c33b
        [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
            TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
            hash: expr=1025771960 text=03d8a0e1bace7dda
          [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
              TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] : Type u_2
              field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
              field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
              field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
              field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
              field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
              field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
              hash: expr=2326492630 text=8a7f2f92f7e6cb25
          [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
              TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
              hash: expr=3192152571 text=38dbb03b36baa07e
            [type] TauCeti.ProjValMeasure  (above)
            [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
                TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                  (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
                hash: expr=6169287 text=22cb14432afff4f4
              [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                  TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                  hash: expr=2377768205 text=1636dc1e3618d340
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                    TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                    field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                    field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                    hash: expr=2489458960 text=438ae027281cfbf3
                [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                    TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                    hash: expr=3802524166 text=6359a60df1615396
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                      TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                      hash: expr=1909853194 text=b5d0ecb89e77cc8a
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                    [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                        TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                          [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                        hash: expr=3546105377 text=12fa953afc9438d3
                      [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                          TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                            MeasureTheory.Measure ↑(spectrum ℂ a)
                          hash: expr=2083923581 text=098301ad89533cf1
                        [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                            TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                              CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                            hash: expr=1299686186 text=681fa6315915ecf0
                          [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                              TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                              hash: expr=1488155521 text=8b20cf9e9db8beeb
                    [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                        TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                          (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                        hash: expr=2675746042 text=64520af0639dba43
                      [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
                [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                    TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                      ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                    hash: expr=1978111998 text=fb2d00c2b9b8b360
            [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
                TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                  MeasureTheory.Measure ℝ
                hash: expr=1112489121 text=ea1d4ee13b3b4c3a
              [body] TauCeti.BorelCalculus.diagMeasure  (above)
            [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
                TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                  MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
                hash: expr=4257216657 text=b6885b32b095cce4
            [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
                TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                  inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                    ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
                hash: expr=3553813407 text=cfd94b77fa277777
            [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
                TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                  TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                hash: expr=4063104685 text=e7abf70c80874ae5
            [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
                TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                  (hB₂ : MeasurableSet B₂) :
                  TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                    TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
                hash: expr=2593835776 text=4cbdd3a7ba3e5991
          [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
              TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
                [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
              hash: expr=2980745689 text=d062a67869324a13
            [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
                TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
                hash: expr=2710346752 text=3040545541bf06a5
              [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                  TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                  hash: expr=4073139655 text=faa87465022c9f97
                [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                    TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                      {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                      (R : E →L[𝕜] E) : Prop
                    field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                    field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                    field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                    hash: expr=3549903545 text=cba9f82aae5d40ca
              [body] TauCeti.LinearPMap.IsResolventAt  (above)
          [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
              TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
                (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
              hash: expr=4155508021 text=b37a61963eed50ac
            [type] TauCeti.LinearPMap.cayley  (above)
          [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
              TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
                Measurable (TauCeti.LinearPMap.cayleyInv hA)
              hash: expr=321618348 text=e943baa16723572d
      [body] TauCeti.RealComplexification  (above)
      [body] TauCeti.LinearPMap.complexifyReal  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:152)
          TauCeti.LinearPMap.complexifyReal.{v, w} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
            {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (A : E →ₗ.[ℝ] F) :
            TauCeti.RealComplexification E →ₗ.[ℂ] TauCeti.RealComplexification F
          hash: expr=3708712926 text=43f07700adc6de1d
        [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.LinearPMap.complexificationDomain  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:88)
            TauCeti.LinearPMap.complexificationDomain.{v, w} {E : Type v} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
              (A : E →ₗ.[ℝ] F) : Submodule ℂ (TauCeti.RealComplexification E)
            hash: expr=1064317096 text=e6f15ad22a023759
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.RealComplexification.im  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:115)
              TauCeti.RealComplexification.im.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
              hash: expr=2897469443 text=1ee09de9c3b20d00
            [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.LinearPMap.complexificationLinearMap  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:122)
            TauCeti.LinearPMap.complexificationLinearMap.{v, w} {E : Type v} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
              (A : E →ₗ.[ℝ] F) :
              ↥(TauCeti.LinearPMap.complexificationDomain A) →ₗ[ℂ] TauCeti.RealComplexification F
            hash: expr=4119099890 text=ae2b112c5c1d8979
          [type] TauCeti.RealComplexification  (above)
          [type] TauCeti.LinearPMap.complexificationDomain  (above)
          [body] TauCeti.RealComplexification.mk  (above)
          [body] TauCeti.LinearPMap.complexificationDomainRe  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:112)
              TauCeti.LinearPMap.complexificationDomainRe.{v, w} {E : Type v} [NormedAddCommGroup E]
                [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
                (A : E →ₗ.[ℝ] F) (z : ↥(TauCeti.LinearPMap.complexificationDomain A)) : ↥A.domain
              hash: expr=3454732267 text=822b4affe842ca54
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.LinearPMap.complexificationDomain  (above)
            [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.LinearPMap.complexificationDomainIm  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:117)
              TauCeti.LinearPMap.complexificationDomainIm.{v, w} {E : Type v} [NormedAddCommGroup E]
                [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
                (A : E →ₗ.[ℝ] F) (z : ↥(TauCeti.LinearPMap.complexificationDomain A)) : ↥A.domain
              hash: expr=3454732267 text=822b4affe842ca54
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.LinearPMap.complexificationDomain  (above)
            [body] TauCeti.RealComplexification.im  (above)
      [body] TauCeti.LinearPMap.isSelfAdjoint_complexifyReal  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:503)
          TauCeti.LinearPMap.isSelfAdjoint_complexifyReal.{v} {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A) :
            IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A)
          hash: expr=1704724094 text=54470d3f97383c71
  [type] TauCeti.LinearPMap.MapsDomainTo  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:65)
      TauCeti.LinearPMap.MapsDomainTo.{u, v, w} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F]
        [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (X : F →L[𝕜] E) : Prop
      hash: expr=3340400931 text=044bcad4674dfaf8
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahan1970.reflectionResidualCorner  (def, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramMiddle.lean:414)
      TauCeti.DavisKahan1970.reflectionResidualCorner.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {G : Type u}
        [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G] (U : Submodule 𝕜 G)
        [U.HasOrthogonalProjection] (B : G →L[𝕜] G) : ↥U →L[𝕜] ↥Uᗮ
      hash: expr=3938377629 text=e31c685a2b1630c9
    [body] TauCeti.DavisKahan.ExactSinTheta.blockCompression  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean:54)
        TauCeti.DavisKahan.ExactSinTheta.blockCompression.{u, v} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] (Ω Γ : Submodule 𝕜 E)
          [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection] (K : E →L[𝕜] E) : ↥Γ →L[𝕜] ↥Ω
        hash: expr=244603371 text=33c1f17fcf589162
      [body] TauCeti.DavisKahan.ExactSinTheta.instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61  (theorem, DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean:39)
          TauCeti.DavisKahan.ExactSinTheta.instCompleteSpaceCoeOfHasOrthogonalProjectionLemma61.{u, v}
            {𝕜 : Type u} [RCLike 𝕜] {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
            [CompleteSpace G] (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace ↥U
          hash: expr=2771355356 text=cdbf1442689c5de1
  [type] Submodule.diagonalPart  (def, ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean:66)
      Submodule.diagonalPart.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
        [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
        E →L[𝕜] E
      hash: expr=3532409979 text=8ec1b7535939660f
  [type] TauCeti.DavisKahan1970.reflectionTangentCorner  (def, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramBridge.lean:270)
      TauCeti.DavisKahan1970.reflectionTangentCorner.{u, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {G : Type u}
        [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G] (U : Submodule 𝕜 G)
        [U.HasOrthogonalProjection] (Z : G →L[𝕜] G) : ↥U →L[𝕜] ↥Uᗮ
      hash: expr=3938377629 text=e31c685a2b1630c9
    [body] TauCeti.DavisKahan.ExactSinTheta.blockCompression  (above)
    [body] TauCeti.DavisKahan1970.unboundedReflectionTangent  (def, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedKyFan.lean:2041)
        TauCeti.DavisKahan1970.unboundedReflectionTangent.{u_2, u_3} {𝕜 : Type u_2} [RCLike 𝕜]
          {G : Type u_3} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (U : Submodule 𝕜 G)
          [U.HasOrthogonalProjection] (Z : G →L[𝕜] G) : G →L[𝕜] G
        hash: expr=4055288565 text=32814c31f13a5e2e
      [body] Submodule.offDiagonalPart  (def, ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean:72)
          Submodule.offDiagonalPart.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
            E →L[𝕜] E
          hash: expr=3532409979 text=8ec1b7535939660f
        [body] Submodule.diagonalPart  (above)
      [body] Submodule.diagonalPart  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

54 project constant(s) unfolded, 8 project leaf/leaves, 93 boundary constant(s), 328 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, LinearPMap, RingHom.id, ContinuousLinearMap, IsSelfAdjoint, Set.Iic, measurableSet_Iic, Eq, Subtype, Submodule, LinearPMap.toFun', Nat, Submodule.orthogonal, And, IsUnit, Complex, EuclideanSpace, Fin, ENNReal, EuclideanSpace.basisFun, RCLike, Set, MeasurableSet, LinearMap.range, Ne, Submodule.HasOrthogonalProjection, ContinuousLinearMap.comp, Submodule.starProjection, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, iSup, ENNReal.ofReal, starRingEnd, ContinuousLinearMap.adjoint, Submodule.subtypeL, Ring.inverse, Finset.sum, Finset.univ, RCLike.ofReal, InnerProductSpace.rankOne, LinearIsometry, LinearMap.mkContinuous, WithLp, Prod, AddCommGroup, Module, Module.ofMinimalAxioms, NormedSpace, Set.ofPred, SMul, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, Exists.choose, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, RealRMK.rieszMeasure, Exists, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedAmbientExact.lean:630`

~~~~lean
variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]
theorem tanTwoTheta_ambient_unbounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G} {a b c : ℝ}
    (V : Submodule ℂ G) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain,
      (x : G) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : G)⟫_ℂ ≤ a * ‖(x : G)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : G) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : G)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : G)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    N.Mem (TauCeti.DavisKahanExt.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahanExt.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_complex.{u} {G : Type u}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G}
  {a b c : ℝ} (V : Submodule ℂ G) [V.HasOrthogonalProjection] (hA : IsSelfAdjoint A)
  (hBsa : IsSelfAdjoint B) (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)
  (hV : TauCeti.DavisKahan.ReflectionIntertwines A B V)
  (hUa :
    ∀ (x : ↥A.domain),
      ↑x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯ →
        RCLike.re (inner ℂ (↑A x) ↑x) ≤ a * ‖↑x‖ ^ 2)
  (hUb :
    ∀ (x : ↥A.domain),
      ↑x ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ →
        b * ‖↑x‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A x) ↑x))
  (hab : a < b) (hBmem : N.Mem B) :
  N.Mem
      (TauCeti.DavisKahanExt.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) V) ∧
    (b - a) *
        N.gauge
          (TauCeti.DavisKahanExt.absTanTwoAngleOperatorC
            (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) V) ≤
      2 * N.gauge B
~~~~

Structural type hash `1374896681`, printed-type hash `19ff5f0e26acf116`.

Statement closure: 42 project constant(s) unfolded, 6 project leaf/leaves, 96 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.IsOddFor`, `TauCeti.LinearPMap.specRange`, `TauCeti.DavisKahan.ReflectionIntertwines`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahanExt.absTanTwoAngleOperatorC`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.LinearPMap.specProjection`, `TauCeti.LinearPMap.MapsDomainTo`, `Submodule.reflectionOperator`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.DavisKahanExt.angleOperatorC`, `TauCeti.diagOp`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.DavisKahanExt.sinAngleOperatorC`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `ContinuousLinearMap.modulus`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.FiniteDimensional.absDoubleAngleTangent`, `TauCeti.DavisKahan1970.doubleSecant`, `TauCeti.DavisKahan1970.projectorDifference`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Complex`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `Real`, `Submodule`, `Submodule.HasOrthogonalProjection`, `IsSelfAdjoint`, `Set.Iic`, `measurableSet_Iic`, `Subtype`, `AddMonoidHom`, `LinearPMap.toFun'`, `Nat`, `Submodule.orthogonal`, `And`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `Set`, `MeasurableSet`, `LinearMap.range`, `Ne`, `cfc`, `abs`, `Real.tan`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `LinearIsometry.toContinuousLinearMap`, `LinearIsometryEquiv.toLinearIsometry`, `Submodule.reflection`, `iSup`, `ENNReal.ofReal`, `Real.arcsin`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `Submodule.starProjection`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.comp`, `ContinuousLinearMap.adjoint`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `NormedSpace`, `Exists.choose`, `LinearMap.mkContinuous`, `RealRMK.rieszMeasure`, `Set.ofPred`, `Exists`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_complex  (theorem, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedAmbientExact.lean:612)
    TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_complex.{u} {G : Type u}
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : G →ₗ.[ℂ] G} {B : G →L[ℂ] G}
      {a b c : ℝ} (V : Submodule ℂ G) [V.HasOrthogonalProjection] (hA : IsSelfAdjoint A)
      (hBsa : IsSelfAdjoint B) (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)
      (hV : TauCeti.DavisKahan.ReflectionIntertwines A B V)
      (hUa :
        ∀ (x : ↥A.domain),
          ↑x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯ →
            RCLike.re (inner ℂ (↑A x) ↑x) ≤ a * ‖↑x‖ ^ 2)
      (hUb :
        ∀ (x : ↥A.domain),
          ↑x ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ →
            b * ‖↑x‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A x) ↑x))
      (hab : a < b) (hBmem : N.Mem B) :
      N.Mem
          (TauCeti.DavisKahanExt.absTanTwoAngleOperatorC
            (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) V) ∧
        (b - a) *
            N.gauge
              (TauCeti.DavisKahanExt.absTanTwoAngleOperatorC
                (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) V) ≤
          2 * N.gauge B
    hash: expr=1374896681 text=19ff5f0e26acf116
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.IsOddFor  (def, ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedReflection.lean:76)
      TauCeti.IsOddFor.{u_1, u_2} {𝕜 : Type u_1} {H : Type u_2} [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] (U : Submodule 𝕜 H) (B : H →L[𝕜] H) : Prop
      hash: expr=4245281075 text=f6fb5c101acd31be
  [type] TauCeti.LinearPMap.specRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:584)
      TauCeti.LinearPMap.specRange.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B) :
        Submodule ℂ H
      hash: expr=3996704367 text=044a08326e510c21
    [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
        TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
          [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
          (hB : MeasurableSet B) : H →L[ℂ] H
        hash: expr=1748688050 text=b7b417789e21c33b
      [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
          TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
            [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
          hash: expr=1025771960 text=03d8a0e1bace7dda
        [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
            TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] : Type u_2
            field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
            field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
            field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
            field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
            field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
            field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
            hash: expr=2326492630 text=8a7f2f92f7e6cb25
        [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
            TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
              {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
            hash: expr=3192152571 text=38dbb03b36baa07e
          [type] TauCeti.ProjValMeasure  (above)
          [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
              TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
              hash: expr=6169287 text=22cb14432afff4f4
            [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                hash: expr=2377768205 text=1636dc1e3618d340
              [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                  TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                  field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                  field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                  hash: expr=2489458960 text=438ae027281cfbf3
              [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                  TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                  hash: expr=3802524166 text=6359a60df1615396
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                    TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                    hash: expr=1909853194 text=b5d0ecb89e77cc8a
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                      TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                        [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                      hash: expr=3546105377 text=12fa953afc9438d3
                    [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                        TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                          MeasureTheory.Measure ↑(spectrum ℂ a)
                        hash: expr=2083923581 text=098301ad89533cf1
                      [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                          TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                            CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                          hash: expr=1299686186 text=681fa6315915ecf0
                        [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                            TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                            hash: expr=1488155521 text=8b20cf9e9db8beeb
                  [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                      TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                        (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                      hash: expr=2675746042 text=64520af0639dba43
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
              [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
              [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                  TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                    ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                  hash: expr=1978111998 text=fb2d00c2b9b8b360
          [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
              TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                MeasureTheory.Measure ℝ
              hash: expr=1112489121 text=ea1d4ee13b3b4c3a
            [body] TauCeti.BorelCalculus.diagMeasure  (above)
          [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
              TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
              hash: expr=4257216657 text=b6885b32b095cce4
          [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
              TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                  ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
              hash: expr=3553813407 text=cfd94b77fa277777
          [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
              TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
              hash: expr=4063104685 text=e7abf70c80874ae5
          [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
              TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                (hB₂ : MeasurableSet B₂) :
                TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                  TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
              hash: expr=2593835776 text=4cbdd3a7ba3e5991
        [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
            TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
              [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
            hash: expr=2980745689 text=d062a67869324a13
          [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
              TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
              hash: expr=2710346752 text=3040545541bf06a5
            [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                hash: expr=4073139655 text=faa87465022c9f97
              [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                  TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                    {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                    (R : E →L[𝕜] E) : Prop
                  field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                  field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                  field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                  hash: expr=3549903545 text=cba9f82aae5d40ca
            [body] TauCeti.LinearPMap.IsResolventAt  (above)
        [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
            TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
              (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
            hash: expr=4155508021 text=b37a61963eed50ac
          [type] TauCeti.LinearPMap.cayley  (above)
        [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
            TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
              [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
              Measurable (TauCeti.LinearPMap.cayleyInv hA)
            hash: expr=321618348 text=e943baa16723572d
  [type] TauCeti.DavisKahan.ReflectionIntertwines  (structure, DavisKahan/TanTheta/RitzPair.lean:245)
      TauCeti.DavisKahan.ReflectionIntertwines.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
        (V : Submodule 𝕜 H) [V.HasOrthogonalProjection] : Prop
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection], TauCeti.DavisKahan.ReflectionIntertwines A B V → TauCeti.LinearPMap.MapsDomainTo A A V.reflectionOperator
      field commutes : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection] (self : TauCeti.DavisKahan.ReflectionIntertwines A B V) (x : ↥A.domain), ↑A ⟨V.reflectionOperator ↑x, ⋯⟩ + B (V.reflectionOperator ↑x) = V.reflectionOperator (↑A x) + V.reflectionOperator (B ↑x)
      hash: expr=906379057 text=a8a6a47981ad2500
    [body] TauCeti.LinearPMap.MapsDomainTo  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:65)
        TauCeti.LinearPMap.MapsDomainTo.{u, v, w} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (X : F →L[𝕜] E) : Prop
        hash: expr=3340400931 text=044bcad4674dfaf8
    [body] Submodule.reflectionOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean:61)
        Submodule.reflectionOperator.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
          E →L[𝕜] E
        hash: expr=3177136020 text=e88d9a7941fbe63e
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.absTanTwoAngleOperatorC  (def, DavisKahan/Geometry/Angle/TanAngleFunctionalCalculus.lean:179)
      TauCeti.DavisKahanExt.absTanTwoAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℂ] E
      hash: expr=187490045 text=178745a4708f5513
    [body] TauCeti.DavisKahanExt.angleOperatorC  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean:84)
        TauCeti.DavisKahanExt.angleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.sinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:38)
          TauCeti.DavisKahanExt.sinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
            ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
              [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
              [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
              [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
            hash: expr=299460441 text=f21cf18f7b7963ad
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

42 project constant(s) unfolded, 6 project leaf/leaves, 96 boundary constant(s), 293 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Complex, CompleteSpace, LinearPMap, RingHom.id, ContinuousLinearMap, Real, Submodule, Submodule.HasOrthogonalProjection, IsSelfAdjoint, Set.Iic, measurableSet_Iic, Subtype, AddMonoidHom, LinearPMap.toFun', Nat, Submodule.orthogonal, And, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, Set, MeasurableSet, LinearMap.range, Ne, cfc, abs, Real.tan, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, LinearIsometry.toContinuousLinearMap, LinearIsometryEquiv.toLinearIsometry, Submodule.reflection, iSup, ENNReal.ofReal, Real.arcsin, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, Submodule.starProjection, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.comp, ContinuousLinearMap.adjoint, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, NormedSpace, Exists.choose, LinearMap.mkContinuous, RealRMK.rieszMeasure, Set.ofPred, Exists, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

#### `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:527`

~~~~lean
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
theorem tanTwoTheta_ambient_unbounded_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E} {B : E →L[ℝ] E} {a b c : ℝ}
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (hA : _root_.IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
    (hV : DavisKahan.ReflectionIntertwines A B V)
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic →
      ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) (hBmem : N.Mem B) :
    N.Mem (TauCeti.DavisKahanExt.absTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahanExt.absTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B
~~~~

**Elaborated signature** (statement pin: current)

~~~~lean
TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_real.{u} {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B : E →L[ℝ] E}
  {a b c : ℝ} (V : Submodule ℝ E) [V.HasOrthogonalProjection] (hA : IsSelfAdjoint A)
  (hBsa : IsSelfAdjoint B)
  (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)
  (hV : TauCeti.DavisKahan.ReflectionIntertwines A B V)
  (hUa :
    ∀ (x : ↥A.domain),
      ↑x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯ → inner ℝ (↑A x) ↑x ≤ a * ‖↑x‖ ^ 2)
  (hUb :
    ∀ (x : ↥A.domain),
      ↑x ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯)ᗮ → b * ‖↑x‖ ^ 2 ≤ inner ℝ (↑A x) ↑x)
  (hab : a < b) (hBmem : N.Mem B) :
  N.Mem
      (TauCeti.DavisKahanExt.absTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) V) ∧
    (b - a) *
        N.gauge
          (TauCeti.DavisKahanExt.absTanTwoAngleOperatorR
            (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) V) ≤
      2 * N.gauge B
~~~~

Structural type hash `2282470164`, printed-type hash `81828007b92d34da`.

Statement closure: 56 project constant(s) unfolded, 7 project leaf/leaves, 102 boundary constant(s).
**Project constants in the statement closure that the local semantic dictionary does not disclose:** `TauCeti.IsOddFor`, `TauCeti.LinearPMap.realSpecRange`, `TauCeti.DavisKahan.ReflectionIntertwines`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem`, `TauCeti.DavisKahanExt.absTanTwoAngleOperatorR`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge`, `TauCeti.UnitarilyInvariantSeminorm`, `TauCeti.UnitarilyInvariantSeminorm.gauge`, `TauCeti.DavisKahan.ExactSinTheta.zeroPad`, `TauCeti.LinearPMap.realSpecProjection`, `TauCeti.LinearPMap.MapsDomainTo`, `Submodule.reflectionOperator`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge`, `TauCeti.RealComplexification.realPartOperator`, `TauCeti.DavisKahanExt.absTanTwoAngleOperatorC`, `TauCeti.RealComplexification`, `TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule`, `TauCeti.diagOp`, `TauCeti.LinearPMap.specProjection`, `TauCeti.LinearPMap.complexifyReal`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge`, `TauCeti.RealComplexification.re`, `TauCeti.RealComplexification.ofReal`, `TauCeti.DavisKahanExt.angleOperatorC`, `TauCeti.RealComplexification.im`, `TauCeti.LinearPMap.spectralPVM`, `TauCeti.LinearPMap.complexificationDomain`, `TauCeti.LinearPMap.complexificationLinearMap`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge`, `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix`, `TauCeti.RealComplexification.mk`, `TauCeti.DavisKahanExt.sinAngleOperatorC`, `TauCeti.ProjValMeasure`, `TauCeti.BorelCalculus.toProjValMeasure`, `TauCeti.LinearPMap.cayley`, `TauCeti.LinearPMap.cayleyInv`, `TauCeti.LinearPMap.complexificationDomainRe`, `TauCeti.LinearPMap.complexificationDomainIm`, `ContinuousLinearMap.modulus`, `TauCeti.BorelCalculus.specProj`, `TauCeti.BorelCalculus.specDiag`, `TauCeti.LinearPMap.resolvent`, `ContinuousLinearMap.approximationNumber`, `TauCeti.BorelCalculus.borelCalculus`, `TauCeti.BorelCalculus.diagMeasure`, `TauCeti.LinearPMap.resolventSet`, `TauCeti.LinearPMap.IsResolventAt`, `TauCeti.BorelCalculus.IsBddMeasurable`, `TauCeti.BorelCalculus.borelVector`, `TauCeti.BorelCalculus.IsBddMeasurable.chooseBound`, `TauCeti.BorelCalculus.diagFunctional`, `TauCeti.BorelCalculus.pairFunctional`, `TauCeti.BorelCalculus.ofRealLM`, `TauCeti.BorelCalculus.pair`, `TauCeti.LinearPMap.isSelfAdjoint_complexifyReal`, `TauCeti.LinearPMap.measurable_cayleyInv`, `TauCeti.BorelCalculus.isFiniteMeasure_specDiag`, `TauCeti.BorelCalculus.inner_specProj_self`, `TauCeti.BorelCalculus.specProj_univ`, `TauCeti.BorelCalculus.specProj_inter`, `TauCeti.BorelCalculus.norm_borelVector_le`
Dictionary definitions this statement never reaches: `TauCeti.DavisKahan.FiniteDimensional.absDoubleAngleTangent`, `TauCeti.DavisKahan1970.doubleSecant`, `TauCeti.DavisKahan1970.projectorDifference`
Boundary vocabulary: `NormedAddCommGroup`, `InnerProductSpace`, `Real`, `CompleteSpace`, `LinearPMap`, `RingHom.id`, `ContinuousLinearMap`, `Submodule`, `Submodule.HasOrthogonalProjection`, `IsSelfAdjoint`, `Set.Iic`, `measurableSet_Iic`, `Subtype`, `LinearPMap.toFun'`, `Nat`, `Submodule.orthogonal`, `And`, `Complex`, `EuclideanSpace`, `Fin`, `ENNReal`, `Eq`, `EuclideanSpace.basisFun`, `RCLike`, `Set`, `MeasurableSet`, `LinearMap.range`, `Ne`, `ENNReal.toReal`, `FiniteDimensional`, `LinearMap`, `LinearIsometryEquiv`, `LinearMap.comp`, `OrthonormalBasis`, `Fin.lastCases`, `LinearIsometry.toContinuousLinearMap`, `LinearIsometryEquiv.toLinearIsometry`, `Submodule.reflection`, `iSup`, `ENNReal.ofReal`, `LinearIsometry`, `LinearMap.mkContinuous`, `cfc`, `abs`, `Real.tan`, `WithLp`, `Prod`, `Set.ofPred`, `Finset.sum`, `Finset.univ`, `RCLike.ofReal`, `starRingEnd`, `InnerProductSpace.rankOne`, `AddCommGroup`, `Module`, `Module.ofMinimalAxioms`, `NormedSpace`, `Real.arcsin`, `SMul`, `Submodule.starProjection`, `MeasureTheory.Measure`, `MeasureTheory.IsFiniteMeasure`, `Complex.ofReal`, `Set.univ`, `MeasurableSet.univ`, `ContinuousLinearMap.id`, `MeasurableSet.inter`, `IsStarNormal`, `Set.Elem`, `spectrum`, `Measurable`, `Complex.I`, `Algebra`, `IsScalarTower`, `ContinuousFunctionalCalculus`, `CFC.sqrt`, `ContinuousLinearMap.instStarOrderedRingRCLike`, `ContinuousLinearMap.comp`, `ContinuousLinearMap.adjoint`, `Set.indicator`, `Set.preimage`, `MeasureTheory.Measure.map`, `NontriviallyNormedField`, `Exists.choose`, `SeminormedAddCommGroup`, `iInf`, `Cardinal`, `LinearMap.rank`, `Nat.cast`, `RealRMK.rieszMeasure`, `Exists`, `StrongDual`, `LinearIsometryEquiv.symm`, `InnerProductSpace.toDual`, `PositiveLinearMap`, `CompactlySupportedContinuousMap`, `StarAlgHom`, `ContinuousMap`, `cfcHom`, `RingHom`, `TopologicalSpace`, `MeasureTheory.integral`

<details><summary>Statement closure tree</summary>

~~~~text
TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_real  (theorem, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:515)
    TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_symmetricNorming_real.{u} {E : Type u}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B : E →L[ℝ] E}
      {a b c : ℝ} (V : Submodule ℝ E) [V.HasOrthogonalProjection] (hA : IsSelfAdjoint A)
      (hBsa : IsSelfAdjoint B)
      (hB : TauCeti.IsOddFor (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B)
      (hV : TauCeti.DavisKahan.ReflectionIntertwines A B V)
      (hUa :
        ∀ (x : ↥A.domain),
          ↑x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯ → inner ℝ (↑A x) ↑x ≤ a * ‖↑x‖ ^ 2)
      (hUb :
        ∀ (x : ↥A.domain),
          ↑x ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯)ᗮ → b * ‖↑x‖ ^ 2 ≤ inner ℝ (↑A x) ↑x)
      (hab : a < b) (hBmem : N.Mem B) :
      N.Mem
          (TauCeti.DavisKahanExt.absTanTwoAngleOperatorR
            (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) V) ∧
        (b - a) *
            N.gauge
              (TauCeti.DavisKahanExt.absTanTwoAngleOperatorR
                (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) V) ≤
          2 * N.gauge B
    hash: expr=2282470164 text=81828007b92d34da
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (structure, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:47)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction : Type
      field finiteNorm : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction → (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      field normalized : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction), ((self.finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1
      field zero_pad : ∀ (self : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) {n : ℕ} (x : Fin n → ℝ), (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ) (TauCeti.DavisKahan.ExactSinTheta.zeroPad x) = (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
      hash: expr=3931117990 text=baaddf70fb5d432b
    [body] TauCeti.UnitarilyInvariantSeminorm  (structure, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:251)
        TauCeti.UnitarilyInvariantSeminorm.{u_3, u_4} (𝕜 : Type u_3) (E : Type u_4) [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] : Type u_4
        field toFun : {𝕜 : Type u_3} → {E : Type u_4} → [inst : RCLike 𝕜] → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → [inst_3 : FiniteDimensional 𝕜 E] → TauCeti.UnitarilyInvariantSeminorm 𝕜 E → (E →ₗ[𝕜] E) → ℝ
        field add_le' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (A B : E →ₗ[𝕜] E), self.toFun (A + B) ≤ self.toFun A + self.toFun B
        field smul' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (a : 𝕜) (A : E →ₗ[𝕜] E), self.toFun (a • A) = ‖a‖ * self.toFun A
        field invariant' : ∀ {𝕜 : Type u_3} {E : Type u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] (self : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (U V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E), self.toFun (↑U.toLinearEquiv ∘ₗ A ∘ₗ ↑V.toLinearEquiv) = self.toFun A
        hash: expr=2499593303 text=2e9a12d567f1324f
    [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:327)
        TauCeti.UnitarilyInvariantSeminorm.gauge.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
          (N : TauCeti.UnitarilyInvariantSeminorm 𝕜 E) (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) :
          ℝ
        hash: expr=394691753 text=abe65b3be11f4c41
      [type] TauCeti.UnitarilyInvariantSeminorm  (above)
      [body] TauCeti.diagOp  (def, ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm.lean:88)
          TauCeti.diagOp.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜] [NormedAddCommGroup E]
            [InnerProductSpace 𝕜 E] {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (x : Fin n → ℝ) : E →ₗ[𝕜] E
          hash: expr=4166364711 text=47942ef11e9bbfe7
    [body] TauCeti.DavisKahan.ExactSinTheta.zeroPad  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:43)
        TauCeti.DavisKahan.ExactSinTheta.zeroPad {n : ℕ} (x : Fin n → ℝ) : Fin (n + 1) → ℝ
        hash: expr=135628739 text=485d6568d5290806
  [type] TauCeti.IsOddFor  (def, ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedReflection.lean:76)
      TauCeti.IsOddFor.{u_1, u_2} {𝕜 : Type u_1} {H : Type u_2} [RCLike 𝕜] [NormedAddCommGroup H]
        [InnerProductSpace 𝕜 H] (U : Submodule 𝕜 H) (B : H →L[𝕜] H) : Prop
      hash: expr=4245281075 text=f6fb5c101acd31be
  [type] TauCeti.LinearPMap.realSpecRange  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification/SpectralDescent.lean:338)
      TauCeti.LinearPMap.realSpecRange.{v} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A) (S : Set ℝ) (hS : MeasurableSet S) :
        Submodule ℝ E
      hash: expr=4005423199 text=f64f5562d5a2e705
    [body] TauCeti.LinearPMap.realSpecProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification/SpectralDescent.lean:278)
        TauCeti.LinearPMap.realSpecProjection.{v} {E : Type v} [NormedAddCommGroup E]
          [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A) (S : Set ℝ)
          (hS : MeasurableSet S) : E →L[ℝ] E
        hash: expr=3802734145 text=f26be7d693b8db3d
      [body] TauCeti.RealComplexification.realPartOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:509)
          TauCeti.RealComplexification.realPartOperator.{u_1, u_2} {E : Type u_1} {F : Type u_2}
            [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
            (T : TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification F) : E →L[ℝ] F
          hash: expr=3255006892 text=5b4b316d076d7dac
        [type] TauCeti.RealComplexification  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:66)
            TauCeti.RealComplexification.{u_1} (E : Type u_1) : Type u_1
            hash: expr=1219222929 text=b115962a62bfdf78
        [body] TauCeti.RealComplexification.re  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:110)
            TauCeti.RealComplexification.re.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
            hash: expr=2897469443 text=1ee09de9c3b20d00
          [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.RealComplexification.ofReal  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:263)
            TauCeti.RealComplexification.ofReal.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] : E →ₗᵢ[ℝ] TauCeti.RealComplexification E
            hash: expr=2088652411 text=71b15fd88eac82fd
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.mk  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:105)
              TauCeti.RealComplexification.mk.{u_1} {E : Type u_1} (x y : E) : TauCeti.RealComplexification E
              hash: expr=2390836649 text=76af0c3ed38ec24a
            [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.LinearPMap.specProjection  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:452)
          TauCeti.LinearPMap.specProjection.{u_1} {H : Type u_1} [NormedAddCommGroup H]
            [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
            (hB : MeasurableSet B) : H →L[ℂ] H
          hash: expr=1748688050 text=b7b417789e21c33b
        [body] TauCeti.LinearPMap.spectralPVM  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:148)
            TauCeti.LinearPMap.spectralPVM.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
              [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure H
            hash: expr=1025771960 text=03d8a0e1bace7dda
          [type] TauCeti.ProjValMeasure  (structure, ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean:87)
              TauCeti.ProjValMeasure.{u_2} (H : Type u_2) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] : Type u_2
              field proj : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H
              field diag : {H : Type u_2} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → [inst_2 : CompleteSpace H] → TauCeti.ProjValMeasure H → H → MeasureTheory.Measure ℝ
              field diag_finite : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (ξ : H), MeasureTheory.IsFiniteMeasure (self.diag ξ)
              field inner_proj : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H), inner ℂ ξ ((self.proj B hB) ξ) = ↑((self.diag ξ) B).toReal
              field proj_univ : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H), self.proj Set.univ ⋯ = ContinuousLinearMap.id ℂ H
              field proj_inter : ∀ {H : Type u_2} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] (self : TauCeti.ProjValMeasure H) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂), self.proj B₁ hB₁ * self.proj B₂ hB₂ = self.proj (B₁ ∩ B₂) ⋯
              hash: expr=2326492630 text=8a7f2f92f7e6cb25
          [body] TauCeti.BorelCalculus.toProjValMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:140)
              TauCeti.BorelCalculus.toProjValMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) : TauCeti.ProjValMeasure H
              hash: expr=3192152571 text=38dbb03b36baa07e
            [type] TauCeti.ProjValMeasure  (above)
            [body] TauCeti.BorelCalculus.specProj  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:63)
                TauCeti.BorelCalculus.specProj.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) {κ : ↑(spectrum ℂ a) → ℝ}
                  (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H
                hash: expr=6169287 text=22cb14432afff4f4
              [body] TauCeti.BorelCalculus.borelCalculus  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:371)
                  TauCeti.BorelCalculus.borelCalculus.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                    [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                    {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : H →L[ℂ] H
                  hash: expr=2377768205 text=1636dc1e3618d340
                [type] TauCeti.BorelCalculus.IsBddMeasurable  (structure, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:44)
                    TauCeti.BorelCalculus.IsBddMeasurable.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] {a : H →L[ℂ] H} (f : ↑(spectrum ℂ a) → ℂ) : Prop
                    field measurable : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → Measurable f
                    field exists_bound : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}, TauCeti.BorelCalculus.IsBddMeasurable f → ∃ M, 0 ≤ M ∧ ∀ (x : ↑(spectrum ℂ a)), ‖f x‖ ≤ M
                    hash: expr=2489458960 text=438ae027281cfbf3
                [body] TauCeti.BorelCalculus.borelVector  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:354)
                    TauCeti.BorelCalculus.borelVector.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H
                    hash: expr=3802524166 text=6359a60df1615396
                  [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                  [body] TauCeti.BorelCalculus.pairFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:328)
                      TauCeti.BorelCalculus.pairFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                        [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                        {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ
                      hash: expr=1909853194 text=b5d0ecb89e77cc8a
                    [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                    [body] TauCeti.BorelCalculus.pair  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean:98)
                        TauCeti.BorelCalculus.pair.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                          [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (f : ↑(spectrum ℂ a) → ℂ) (ψ ξ : H) : ℂ
                        hash: expr=3546105377 text=12fa953afc9438d3
                      [body] TauCeti.BorelCalculus.diagMeasure  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:162)
                          TauCeti.BorelCalculus.diagMeasure.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                            [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                            MeasureTheory.Measure ↑(spectrum ℂ a)
                          hash: expr=2083923581 text=098301ad89533cf1
                        [body] TauCeti.BorelCalculus.diagFunctional  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:136)
                            TauCeti.BorelCalculus.diagFunctional.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                              [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (ξ : H) :
                              CompactlySupportedContinuousMap ↑(spectrum ℂ a) ℝ →ₚ[ℝ] ℝ
                            hash: expr=1299686186 text=681fa6315915ecf0
                          [body] TauCeti.BorelCalculus.ofRealLM  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean:66)
                              TauCeti.BorelCalculus.ofRealLM.{u_1} {X : Type u_1} [TopologicalSpace X] : C(X, ℝ) →ₗ[ℝ] C(X, ℂ)
                              hash: expr=1488155521 text=8b20cf9e9db8beeb
                    [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:51)
                        TauCeti.BorelCalculus.IsBddMeasurable.chooseBound.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                          [InnerProductSpace ℂ H] {a : H →L[ℂ] H} {f : ↑(spectrum ℂ a) → ℂ}
                          (hf : TauCeti.BorelCalculus.IsBddMeasurable f) : ℝ
                        hash: expr=2675746042 text=64520af0639dba43
                      [type] TauCeti.BorelCalculus.IsBddMeasurable  (above)
                [body] TauCeti.BorelCalculus.IsBddMeasurable.chooseBound  (above)
                [body] TauCeti.BorelCalculus.norm_borelVector_le  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:365)
                    TauCeti.BorelCalculus.norm_borelVector_le.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                      [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                      {f : ↑(spectrum ℂ a) → ℂ} (hf : TauCeti.BorelCalculus.IsBddMeasurable f) (ξ : H) :
                      ‖TauCeti.BorelCalculus.borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖
                    hash: expr=1978111998 text=fb2d00c2b9b8b360
            [body] TauCeti.BorelCalculus.specDiag  (def, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:82)
                TauCeti.BorelCalculus.specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                  [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a) (κ' : ↑(spectrum ℂ a) → ℝ) (ξ : H) :
                  MeasureTheory.Measure ℝ
                hash: expr=1112489121 text=ea1d4ee13b3b4c3a
              [body] TauCeti.BorelCalculus.diagMeasure  (above)
            [body] TauCeti.BorelCalculus.isFiniteMeasure_specDiag  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:93)
                TauCeti.BorelCalculus.isFiniteMeasure_specDiag.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (ξ : H) :
                  MeasureTheory.IsFiniteMeasure (TauCeti.BorelCalculus.specDiag ha κ ξ)
                hash: expr=4257216657 text=b6885b32b095cce4
            [body] TauCeti.BorelCalculus.inner_specProj_self  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:99)
                TauCeti.BorelCalculus.inner_specProj_self.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
                  inner ℂ ξ ((TauCeti.BorelCalculus.specProj ha hκ B hB) ξ) =
                    ↑((TauCeti.BorelCalculus.specDiag ha κ ξ) B).toReal
                hash: expr=3553813407 text=cfd94b77fa277777
            [body] TauCeti.BorelCalculus.specProj_univ  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:107)
                TauCeti.BorelCalculus.specProj_univ.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) :
                  TauCeti.BorelCalculus.specProj ha hκ Set.univ ⋯ = ContinuousLinearMap.id ℂ H
                hash: expr=4063104685 text=e7abf70c80874ae5
            [body] TauCeti.BorelCalculus.specProj_inter  (theorem, ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean:121)
                TauCeti.BorelCalculus.specProj_inter.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                  [InnerProductSpace ℂ H] [CompleteSpace H] {a : H →L[ℂ] H} (ha : IsStarNormal a)
                  {κ : ↑(spectrum ℂ a) → ℝ} (hκ : Measurable κ) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁)
                  (hB₂ : MeasurableSet B₂) :
                  TauCeti.BorelCalculus.specProj ha hκ B₁ hB₁ * TauCeti.BorelCalculus.specProj ha hκ B₂ hB₂ =
                    TauCeti.BorelCalculus.specProj ha hκ (B₁ ∩ B₂) ⋯
                hash: expr=2593835776 text=4cbdd3a7ba3e5991
          [body] TauCeti.LinearPMap.cayley  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean:484)
              TauCeti.LinearPMap.cayley.{u_1} {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
                [CompleteSpace E] {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E
              hash: expr=2980745689 text=d062a67869324a13
            [body] TauCeti.LinearPMap.resolvent  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:198)
                TauCeti.LinearPMap.resolvent.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜) : E →L[𝕜] E
                hash: expr=2710346752 text=3040545541bf06a5
              [body] TauCeti.LinearPMap.resolventSet  (def, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:173)
                  TauCeti.LinearPMap.resolventSet.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
                    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) : Set 𝕜
                  hash: expr=4073139655 text=faa87465022c9f97
                [body] TauCeti.LinearPMap.IsResolventAt  (structure, ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean:128)
                    TauCeti.LinearPMap.IsResolventAt.{u_1, u_2} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
                      {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : E →ₗ.[𝕜] E) (lambda : 𝕜)
                      (R : E →L[𝕜] E) : Prop
                    field mem_domain : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (y : E), R y ∈ A.domain
                    field smul_sub_apply : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E} (self : TauCeti.LinearPMap.IsResolventAt A lambda R) (y : E), lambda • R y - ↑A ⟨R y, ⋯⟩ = y
                    field apply_smul_sub : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {lambda : 𝕜} {R : E →L[𝕜] E}, TauCeti.LinearPMap.IsResolventAt A lambda R → ∀ (x : ↥A.domain), R (lambda • ↑x - ↑A x) = ↑x
                    hash: expr=3549903545 text=cba9f82aae5d40ca
              [body] TauCeti.LinearPMap.IsResolventAt  (above)
          [body] TauCeti.LinearPMap.cayleyInv  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:125)
              TauCeti.LinearPMap.cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
                [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
                (w : ↑(spectrum ℂ (TauCeti.LinearPMap.cayley hA))) : ℝ
              hash: expr=4155508021 text=b37a61963eed50ac
            [type] TauCeti.LinearPMap.cayley  (above)
          [body] TauCeti.LinearPMap.measurable_cayleyInv  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean:142)
              TauCeti.LinearPMap.measurable_cayleyInv.{u_1} {H : Type u_1} [NormedAddCommGroup H]
                [InnerProductSpace ℂ H] [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
                Measurable (TauCeti.LinearPMap.cayleyInv hA)
              hash: expr=321618348 text=e943baa16723572d
      [body] TauCeti.RealComplexification  (above)
      [body] TauCeti.LinearPMap.complexifyReal  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:152)
          TauCeti.LinearPMap.complexifyReal.{v, w} {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
            {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (A : E →ₗ.[ℝ] F) :
            TauCeti.RealComplexification E →ₗ.[ℂ] TauCeti.RealComplexification F
          hash: expr=3708712926 text=43f07700adc6de1d
        [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.LinearPMap.complexificationDomain  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:88)
            TauCeti.LinearPMap.complexificationDomain.{v, w} {E : Type v} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
              (A : E →ₗ.[ℝ] F) : Submodule ℂ (TauCeti.RealComplexification E)
            hash: expr=1064317096 text=e6f15ad22a023759
          [type] TauCeti.RealComplexification  (above)
          [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.RealComplexification.im  (def, ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean:115)
              TauCeti.RealComplexification.im.{u_1} {E : Type u_1} (z : TauCeti.RealComplexification E) : E
              hash: expr=2897469443 text=1ee09de9c3b20d00
            [type] TauCeti.RealComplexification  (above)
        [body] TauCeti.LinearPMap.complexificationLinearMap  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:122)
            TauCeti.LinearPMap.complexificationLinearMap.{v, w} {E : Type v} [NormedAddCommGroup E]
              [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
              (A : E →ₗ.[ℝ] F) :
              ↥(TauCeti.LinearPMap.complexificationDomain A) →ₗ[ℂ] TauCeti.RealComplexification F
            hash: expr=4119099890 text=ae2b112c5c1d8979
          [type] TauCeti.RealComplexification  (above)
          [type] TauCeti.LinearPMap.complexificationDomain  (above)
          [body] TauCeti.RealComplexification.mk  (above)
          [body] TauCeti.LinearPMap.complexificationDomainRe  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:112)
              TauCeti.LinearPMap.complexificationDomainRe.{v, w} {E : Type v} [NormedAddCommGroup E]
                [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
                (A : E →ₗ.[ℝ] F) (z : ↥(TauCeti.LinearPMap.complexificationDomain A)) : ↥A.domain
              hash: expr=3454732267 text=822b4affe842ca54
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.LinearPMap.complexificationDomain  (above)
            [body] TauCeti.RealComplexification.re  (above)
          [body] TauCeti.LinearPMap.complexificationDomainIm  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:117)
              TauCeti.LinearPMap.complexificationDomainIm.{v, w} {E : Type v} [NormedAddCommGroup E]
                [InnerProductSpace ℝ E] {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
                (A : E →ₗ.[ℝ] F) (z : ↥(TauCeti.LinearPMap.complexificationDomain A)) : ↥A.domain
              hash: expr=3454732267 text=822b4affe842ca54
            [type] TauCeti.RealComplexification  (above)
            [type] TauCeti.LinearPMap.complexificationDomain  (above)
            [body] TauCeti.RealComplexification.im  (above)
      [body] TauCeti.LinearPMap.isSelfAdjoint_complexifyReal  (theorem, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean:503)
          TauCeti.LinearPMap.isSelfAdjoint_complexifyReal.{v} {E : Type v} [NormedAddCommGroup E]
            [InnerProductSpace ℝ E] [CompleteSpace E] {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A) :
            IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A)
          hash: expr=1704724094 text=54470d3f97383c71
  [type] TauCeti.DavisKahan.ReflectionIntertwines  (structure, DavisKahan/TanTheta/RitzPair.lean:245)
      TauCeti.DavisKahan.ReflectionIntertwines.{u, v} {𝕜 : Type u} [RCLike 𝕜] {H : Type v}
        [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
        (V : Submodule 𝕜 H) [V.HasOrthogonalProjection] : Prop
      field mapsDomain : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection], TauCeti.DavisKahan.ReflectionIntertwines A B V → TauCeti.LinearPMap.MapsDomainTo A A V.reflectionOperator
      field commutes : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {H : Type v} [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H} {V : Submodule 𝕜 H} [inst_3 : V.HasOrthogonalProjection] (self : TauCeti.DavisKahan.ReflectionIntertwines A B V) (x : ↥A.domain), ↑A ⟨V.reflectionOperator ↑x, ⋯⟩ + B (V.reflectionOperator ↑x) = V.reflectionOperator (↑A x) + V.reflectionOperator (B ↑x)
      hash: expr=906379057 text=a8a6a47981ad2500
    [body] TauCeti.LinearPMap.MapsDomainTo  (def, ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:65)
        TauCeti.LinearPMap.MapsDomainTo.{u, v, w} {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F]
          [InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (X : F →L[𝕜] E) : Prop
        hash: expr=3340400931 text=044bcad4674dfaf8
    [body] Submodule.reflectionOperator  (def, ForTauCeti/Analysis/InnerProductSpace/Projection/Blocks.lean:61)
        Submodule.reflectionOperator.{u_1, u_2} {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
          [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
          E →L[𝕜] E
        hash: expr=3177136020 text=e88d9a7941fbe63e
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:102)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.Mem.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : Prop
      hash: expr=1327221734 text=dc252aae0969961d
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:92)
        TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge.{u, v} {𝕜 : Type u}
          [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
          [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
          (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ENNReal
        hash: expr=3870263571 text=019df4fe0eed0f53
      [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
      [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:83)
          TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.prefixGauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
            {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
            [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
            (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (A : E →L[𝕜] F) : ℝ
          hash: expr=3234483192 text=78b88ec54f5dc4a2
        [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:68)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.finiteGauge
              (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (n : ℕ) (x : Fin n → ℝ) : ℝ
            hash: expr=1989020631 text=8bff7666e96d3c25
          [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
          [body] TauCeti.UnitarilyInvariantSeminorm.gauge  (above)
        [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:73)
            TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.approximationPrefix.{u, v} {𝕜 : Type u}
              [RCLike 𝕜] {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
              [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (n : ℕ) (A : E →L[𝕜] F) :
              Fin n → ℝ
            hash: expr=3116985227 text=6f425b5ba0cf5e43
          [body] TauCeti.ApproximationNumber.approximationSingularValue  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:65)
              TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} {𝕜 : Type u} [RCLike 𝕜]
                {E : Type v} {F : Type vF} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] (n : ℕ) (K : E →L[𝕜] F) : ℝ
              hash: expr=4158989512 text=be2938934bb498aa
            [body] ContinuousLinearMap.approximationNumber  (def, ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:136)
                ContinuousLinearMap.approximationNumber.{u, v, w} {𝕜 : Type u} [NontriviallyNormedField 𝕜]
                  {E : Type v} {F : Type w} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
                  [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (n : ℕ) : ℝ
                hash: expr=2527437639 text=7dc5679d2ff68267
  [type] TauCeti.DavisKahanExt.absTanTwoAngleOperatorR  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculusReal.lean:136)
      TauCeti.DavisKahanExt.absTanTwoAngleOperatorR.{u_1} {E : Type u_1} [NormedAddCommGroup E]
        [InnerProductSpace ℝ E] [CompleteSpace E] (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
        [V.HasOrthogonalProjection] : E →L[ℝ] E
      hash: expr=2215108693 text=ca05c2be87f84df1
    [body] TauCeti.RealComplexification.realPartOperator  (above)
    [body] TauCeti.DavisKahanExt.absTanTwoAngleOperatorC  (def, DavisKahan/Geometry/Angle/TanAngleFunctionalCalculus.lean:179)
        TauCeti.DavisKahanExt.absTanTwoAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
          [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
          [V.HasOrthogonalProjection] : E →L[ℂ] E
        hash: expr=187490045 text=178745a4708f5513
      [body] TauCeti.DavisKahanExt.angleOperatorC  (def, DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean:84)
          TauCeti.DavisKahanExt.angleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
            [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
            [V.HasOrthogonalProjection] : E →L[ℂ] E
          hash: expr=187490045 text=178745a4708f5513
        [body] TauCeti.DavisKahanExt.sinAngleOperatorC  (def, DavisKahan/Geometry/Angle/OperatorAngleComplex.lean:38)
            TauCeti.DavisKahanExt.sinAngleOperatorC.{u_1} {E : Type u_1} [NormedAddCommGroup E]
              [InnerProductSpace ℂ E] [CompleteSpace E] (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
              [V.HasOrthogonalProjection] : E →L[ℂ] E
            hash: expr=187490045 text=178745a4708f5513
          [body] ContinuousLinearMap.modulus  (def, ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean:139)
              ContinuousLinearMap.modulus.{u, v, u_1} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u} {F : Type v}
                [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F]
                [InnerProductSpace 𝕜 F] [CompleteSpace F] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
                [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] (T : E →L[𝕜] F) : E →L[𝕜] E
              hash: expr=299460441 text=f21cf18f7b7963ad
    [body] TauCeti.RealComplexification  (above)
    [body] TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule  (def, DavisKahan/SpectralTheory/Complexification/Subspace.lean:45)
        TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule.{u_1} {E : Type u_1}
          [NormedAddCommGroup E] [InnerProductSpace ℝ E] (U : Submodule ℝ E) :
          Submodule ℂ (TauCeti.RealComplexification E)
        hash: expr=3786915484 text=ce5d0cdd7318abdd
      [type] TauCeti.RealComplexification  (above)
      [body] TauCeti.RealComplexification.re  (above)
      [body] TauCeti.RealComplexification.im  (above)
  [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge  (def, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:112)
      TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.gauge.{u, v} {𝕜 : Type u} [RCLike 𝕜]
        {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction) (A : E →L[𝕜] F) : ℝ
      hash: expr=1680327561 text=57303bb0d50c9d09
    [type] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction  (above)
    [body] TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction.extendedGauge  (above)

56 project constant(s) unfolded, 7 project leaf/leaves, 102 boundary constant(s), 340 instance/projection constant(s)
boundary: NormedAddCommGroup, InnerProductSpace, Real, CompleteSpace, LinearPMap, RingHom.id, ContinuousLinearMap, Submodule, Submodule.HasOrthogonalProjection, IsSelfAdjoint, Set.Iic, measurableSet_Iic, Subtype, LinearPMap.toFun', Nat, Submodule.orthogonal, And, Complex, EuclideanSpace, Fin, ENNReal, Eq, EuclideanSpace.basisFun, RCLike, Set, MeasurableSet, LinearMap.range, Ne, ENNReal.toReal, FiniteDimensional, LinearMap, LinearIsometryEquiv, LinearMap.comp, OrthonormalBasis, Fin.lastCases, LinearIsometry.toContinuousLinearMap, LinearIsometryEquiv.toLinearIsometry, Submodule.reflection, iSup, ENNReal.ofReal, LinearIsometry, LinearMap.mkContinuous, cfc, abs, Real.tan, WithLp, Prod, Set.ofPred, Finset.sum, Finset.univ, RCLike.ofReal, starRingEnd, InnerProductSpace.rankOne, AddCommGroup, Module, Module.ofMinimalAxioms, NormedSpace, Real.arcsin, SMul, Submodule.starProjection, MeasureTheory.Measure, MeasureTheory.IsFiniteMeasure, Complex.ofReal, Set.univ, MeasurableSet.univ, ContinuousLinearMap.id, MeasurableSet.inter, IsStarNormal, Set.Elem, spectrum, Measurable, Complex.I, Algebra, IsScalarTower, ContinuousFunctionalCalculus, CFC.sqrt, ContinuousLinearMap.instStarOrderedRingRCLike, ContinuousLinearMap.comp, ContinuousLinearMap.adjoint, Set.indicator, Set.preimage, MeasureTheory.Measure.map, NontriviallyNormedField, Exists.choose, SeminormedAddCommGroup, iInf, Cardinal, LinearMap.rank, Nat.cast, RealRMK.rieszMeasure, Exists, StrongDual, LinearIsometryEquiv.symm, InnerProductSpace.toDual, PositiveLinearMap, CompactlySupportedContinuousMap, StarAlgHom, ContinuousMap, cfcHom, RingHom, TopologicalSpace, MeasureTheory.integral
~~~~

</details>

### Supporting scope declarations

- `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_complex` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_symmetricNorming_real` — elaborated; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike` — elaborated; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction`

The literal source unitary-invariant norm; tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike is already generic over RCLike 𝕜 at this norm scope.

#### `TauCeti.DavisKahan.FiniteDimensional.absDoubleAngleTangent`

The branch-free scalar function 2 t / |1-t^2| applied to graph-coordinate singular values; this is the generic theorem’s representation of |tan(2 Theta)|.

#### `TauCeti.ApproximationNumber.approximationSingularValue`

The approximation-number singular-value sequence used to express the branch-free tangent representative in arbitrary Hilbert space.

#### `TauCeti.DavisKahan1970.doubleSecant`

The source-shaped U,V directed-corner implementation used by the second canonical theorem; its invertibility is derived internally rather than assumed.

#### `TauCeti.DavisKahan1970.projectorDifference`

The projector-difference factor used to build the source-shaped directed tan(2 Theta0) representative.

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike is an alias of the already proved branch-free theorem quantified over 𝕜 with [RCLike 𝕜] and the literal SymmetricNormingFunction. | claimed_exact |
| A has an ordered block gap and H is fully off diagonal. | The generic theorem writes the form bounds hUb/hUa and the two literal off-diagonal mapping hypotheses hHU/hHUperp directly; no named gap or oddness predicate hides them. | claimed_exact |
| The perturbed invariant subspace is arbitrary and no independent tan(2 Theta) pole hypothesis is assumed. | The generic theorem describes the invariant perturbed graph by hTmem, hTzero and hinv and uses the branch-free absDoubleAngleTangent singular values; it has no T<1, IsQuarterAcute, or cos(2 theta) premise. | claimed_exact |
| delta \|\|tan(2 Theta)\|\| <= 2 \|\|H\|\|. | With delta = b-a, tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike concludes (b-a) * N.gauge tanTwoTheta <= 2 * N.gauge H for every source norm. | claimed_exact |
| delta \|\|tan(2 Theta0)\|\| <= 2 \|\|R\|\| in the source-shaped U,V corner notation. | The second canonical declaration gives the literal compression-spectrum/off-diagonal directed-corner theorem with no caller-supplied pole certificate. | claimed_exact |
| Infinite-dimensional/unbounded scope. | The generic branch-free canonical theorem removes ambient finite-dimensionality but still assumes a finite-dimensional graph base U; the full arbitrary-dimensional and unbounded real/complex endpoints remain compiler-checked supporting declarations. | scope_companion |

**Review note.** Unlike tan Theta and sin 2Theta, the branch-free tan 2Theta paper-norm theorem was already scalar-generic. The review now promotes it to the canonical headline name. Its generic proof is necessarily graph-coordinate shaped, so the source-shaped U,V directed-corner theorem remains canonical alongside it and the report prints absDoubleAngleTangent/approximationSingularValue context explicitly. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

2026-08-31: the canonical declaration list here is now the counted result's `canonical_evidence` in `dev/davis-kahan-1970-formalization-result-inventory.json`, and the checker enforces that. Demoted to supporting: TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike -- a finite-dimensional or capability-class facade cannot be the canonical witness for a result certified at unbounded infinite-dimensional scope.

**Next action.** No hostile-review hole is currently recorded for this source passage. Preserve exact source scope and re-audit if the distributable source specification changes.
