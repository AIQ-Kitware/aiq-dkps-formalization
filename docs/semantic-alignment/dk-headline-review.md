# Semantic alignment review packet

This packet is generated from curated semantic-review fields in the source censuses. Human-written Lean headers are structural source evidence. Compiler output, when present, is elaborator-backed evidence about the Lean surface. The source-to-Lean correspondence remains the census author's explicit review claim.

**Compiler imports:** `DavisKahan.All`, `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry`, `ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz`, `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core`

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

#### `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:253`

~~~~lean
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
theorem sinTheta_unbounded_formGap_paperUINorm_rclike
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    [TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.{u, v} 𝕜]
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R
~~~~

**Compiler-resolved type**

~~~~lean
@DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E F G H : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E]
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : CompleteSpace F]
  [inst_7 : NormedAddCommGroup G] [inst_8 : InnerProductSpace 𝕜 G] [inst_9 : CompleteSpace G]
  [inst_10 : NormedAddCommGroup H] [inst_11 : InnerProductSpace 𝕜 H] [inst_12 : CompleteSpace H]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] [TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan 𝕜]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
  (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E),
  IsSelfAdjoint A →
    IsSelfAdjoint A₀ →
      IsSelfAdjoint Λ₁ →
        DavisKahan1970.IsTrialResidual A A₀ E₀ R →
          DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ →
            ∀ {δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap A₀ Λ₁ δ →
                  N.Mem R →
                    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ∧
                      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ≤
                        N.gauge R
~~~~

### Supporting scope declarations

- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex` — resolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real` — resolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex_ofRCLike` — resolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real_ofRCLike` — resolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_ofComponents_rclike` — resolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_rclike` — resolved; source located
- `DavisKahan1970.sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` — resolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_idealFamily_rclike` — resolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_spectralSubspace_complex` — resolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_spectralSubspace_real` — resolved; source located
- `TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace_complex` — resolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex_ofRCLike_conforms` — resolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real_ofRCLike_conforms` — resolved; source located

### Local semantic dictionary

#### `DavisKahan1970.isTrialResidual_iff`

Expands the compact trial-residual hypothesis into the trial isometry, domain transport, and exact residual identity R = A E0 - E0 A0.

~~~~lean
theorem DavisKahan1970.isTrialResidual_iff.{u, v} : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E F : Type v}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCommGroup F]
  [inst_4 : InnerProductSpace 𝕜 F] (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (E₀ R : F →L[𝕜] E),
  DavisKahan1970.IsTrialResidual A A₀ E₀ R ↔
    TauCeti.DavisKahan.IsometricEmbedding E₀ ∧
      ∃ (hdom : ∀ (x : ↥A₀.domain), E₀ ↑x ∈ A.domain), ∀ (x : ↥A₀.domain), ↑A ⟨E₀ ↑x, ⋯⟩ - E₀ (↑A₀ x) = R ↑x :=
fun {𝕜} [RCLike 𝕜] {E F} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] A
    A₀ E₀ R =>
  { mp := fun h => ⟨h.isometry, Exists.intro h.mapsDomain h.residualEquation⟩,
    mpr := fun a =>
      And.casesOn a fun hE₀ right =>
        Exists.casesOn right fun hdom heq => { isometry := hE₀, mapsDomain := hdom, residualEquation := heq } }
~~~~

#### `DavisKahan1970.isExactSpectralDecomposition_iff`

Expands the compact exact-space hypothesis into isometric F0/F1 coordinates, orthogonality, completeness, domain transport, and A F1 = F1 Lambda1.

~~~~lean
theorem DavisKahan1970.isExactSpectralDecomposition_iff.{u, v} : ∀ {𝕜 : Type u} [inst : RCLike 𝕜] {E G H : Type v}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E]
  [inst_4 : NormedAddCommGroup G] [inst_5 : InnerProductSpace 𝕜 G] [inst_6 : CompleteSpace G]
  [inst_7 : NormedAddCommGroup H] [inst_8 : InnerProductSpace 𝕜 H] [inst_9 : CompleteSpace H] (A : E →ₗ.[𝕜] E)
  (Λ₁ : G →ₗ.[𝕜] G) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E),
  DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁ ↔
    TauCeti.DavisKahan.IsometricEmbedding F₀ ∧
      TauCeti.DavisKahan.IsometricEmbedding F₁ ∧
        ContinuousLinearMap.adjoint F₀ ∘SL F₁ = 0 ∧
          F₀ ∘SL ContinuousLinearMap.adjoint F₀ + F₁ ∘SL ContinuousLinearMap.adjoint F₁ = ContinuousLinearMap.id 𝕜 E ∧
            ∃ (hdom : ∀ (y : ↥Λ₁.domain), F₁ ↑y ∈ A.domain), ∀ (y : ↥Λ₁.domain), ↑A ⟨F₁ ↑y, ⋯⟩ = F₁ (↑Λ₁ y) :=
fun {𝕜} [RCLike 𝕜] {E G H} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] A Λ₁ F₀
    F₁ =>
  {
    mp := fun h =>
      ⟨h.desiredIsometry,
        ⟨h.complementIsometry, ⟨h.orthogonal, ⟨h.complete, Exists.intro h.mapsDomain h.intertwines⟩⟩⟩⟩,
    mpr := fun a =>
      And.casesOn a fun hF₀ right =>
        And.casesOn right fun hF₁ right =>
          And.casesOn right fun horth right =>
            And.casesOn right fun hcomplete right =>
              Exists.casesOn right fun hdom hintertwines =>
                { desiredIsometry := hF₀, complementIsometry := hF₁, orthogonal := horth, complete := hcomplete,
                  mapsDomain := hdom, intertwines := hintertwines } }
~~~~

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

Implementation structure behind the public theorem spelling UnitaryInvariantNorm: the dimension-coherent normalized unitary-invariant norm quantified over by Davis--Kahan.

~~~~lean
structure TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm : Type
number of parameters: 0
fields:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.finiteNorm : (n : ℕ) →
      TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.normalized : ((self.finiteNorm 1).gauge
        (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) =
      1
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.zero_pad : ∀ {n : ℕ} (x : Fin n → ℝ),
      (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
          (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
        (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
constructor:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.mk
    (finiteNorm : (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)))
    (normalized : ((finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1)
    (zero_pad :
      ∀ {n : ℕ} (x : Fin n → ℝ),
        (finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
            (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
          (finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x) :
    TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm
~~~~

#### `TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan`

Scalar-field proof capability used to keep one theorem generic over RCLike. The repository provides instances for both source scalar fields, R and C; this is implementation evidence rather than an additional paper hypothesis.

~~~~lean
class TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.{u, v} (𝕜 : Type u) [RCLike 𝕜] : Prop
number of parameters: 2
fields:
  TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.out : ∀ {E F : Type v} [inst : NormedAddCommGroup E]
      [inst_1 : InnerProductSpace 𝕜 E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup F]
      [inst_4 : InnerProductSpace 𝕜 F] [inst_5 : CompleteSpace F] {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F},
      IsSelfAdjoint A →
        IsSelfAdjoint B →
          ∀ {X C : F →L[𝕜] E} {δ : ℝ},
            0 < δ →
              TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap A B δ →
                TauCeti.LinearPMap.SylvesterEquation A B X C →
                  ∀ (k : ℕ),
                    δ * TauCeti.ApproximationNumber.kyFanApproximationGauge k X ≤
                      TauCeti.ApproximationNumber.kyFanApproximationGauge k C
constructor:
  TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.mk.{u, v} {𝕜 : Type u} [RCLike 𝕜]
    (out :
      ∀ {E F : Type v} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace 𝕜 E] [inst_2 : CompleteSpace E]
        [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] [inst_5 : CompleteSpace F] {A : E →ₗ.[𝕜] E}
        {B : F →ₗ.[𝕜] F},
        IsSelfAdjoint A →
          IsSelfAdjoint B →
            ∀ {X C : F →L[𝕜] E} {δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap A B δ →
                  TauCeti.LinearPMap.SylvesterEquation A B X C →
                    ∀ (k : ℕ),
                      δ * TauCeti.ApproximationNumber.kyFanApproximationGauge k X ≤
                        TauCeti.ApproximationNumber.kyFanApproximationGauge k C) :
    TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan 𝕜
~~~~

#### `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`

Approximation-number min--max capability needed by the universal norm machinery. It has proved R and C instances and is not an extra source restriction.

~~~~lean
class ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} (𝕜 : Type u) [RCLike 𝕜] : Prop
number of parameters: 2
fields:
  ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.out : ∀ {E F : Type v} [inst : NormedAddCommGroup E]
      [inst_1 : InnerProductSpace 𝕜 E] [CompleteSpace E] [inst_3 : NormedAddCommGroup F]
      [inst_4 : InnerProductSpace 𝕜 F] [CompleteSpace F], ContinuousLinearMap.HasMinMaxLowerBound 𝕜 E F
constructor:
  ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.mk.{u, v} {𝕜 : Type u} [RCLike 𝕜]
    (out :
      ∀ {E F : Type v} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace 𝕜 E] [CompleteSpace E]
        [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] [CompleteSpace F],
        ContinuousLinearMap.HasMinMaxLowerBound 𝕜 E F) :
    ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜
~~~~

#### `LinearPMap`

Mathlib's partial linear map: the repository representation of the paper's possibly unbounded self-adjoint operators. Dense domain, closed graph and self-adjointness are hypotheses of the theorems that need them, not fields of the carrier; the bundled DKPS record that once played this role was deleted on 2026-08-28.

~~~~lean
structure LinearPMap.{u_1, u_2, u_3, u_4} {R : Type u_1} {S : Type u_2} [Ring R] [Ring S] (σ : R →+* S) (E : Type u_3)
  [AddCommGroup E] [Module R E] (F : Type u_4) [AddCommGroup F] [Module S F] : Type (max u_3 u_4)
number of parameters: 11
fields:
  LinearPMap.domain : Submodule R E
  LinearPMap.toFun : ↥self.domain →ₛₗ[σ] F
constructor:
  LinearPMap.mk.{u_1, u_2, u_3, u_4} {R : Type u_1} {S : Type u_2} [Ring R] [Ring S] {σ : R →+* S} {E : Type u_3}
    [AddCommGroup E] [Module R E] {F : Type u_4} [AddCommGroup F] [Module S F] (domain : Submodule R E)
    (toFun : ↥domain →ₛₗ[σ] F) : E →ₛₗ.[σ] F
~~~~

#### `TauCeti.LinearPMap.realSpectrum`

Real spectrum of a self-adjoint partial/closed operator; the interval/exterior alternative itself remains literal in the canonical theorem.

~~~~lean
def TauCeti.LinearPMap.realSpectrum.{u, v} : {𝕜 : Type u} →
  [inst : RCLike 𝕜] →
    {E : Type v} → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → (E →ₗ.[𝕜] E) → Set ℝ :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] A => (TauCeti.LinearPMap.realResolventSet A)ᶜ
~~~~

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical theorem is generic over 𝕜 with [RCLike 𝕜]. Its two scalar capability binders have proved instances for both source scalar fields ℝ and ℂ. | claimed_exact |
| A, A0, and Lambda1 are self-adjoint; E0 is the trial coordinate map and F0,F1 are orthogonal exact-space coordinates. | A, A₀, Λ₁, E₀, F₀, and F₁ are explicit arguments. Self-adjointness is literal; IsTrialResidual and IsExactSpectralDecomposition are expanded immediately in the local semantic dictionary. | claimed_exact |
| R = A E0 - E0 A0 on the operator domain, while F1 intertwines Lambda1 with A. | These clauses are exactly the residualEquation and intertwines components exposed by isTrialResidual_iff and isExactSpectralDecomposition_iff, together with their domain-transport hypotheses. | claimed_exact |
| sin Theta0 is the directed sine block from the trial subspace to the exact subspace. | sinTheta₀ is an explicit theorem parameter and hSinTheta₀ literally states sinTheta₀ = (I - F₀ F₀†) E₀. No named definition hides this identification. | claimed_exact |
| For beta <= alpha and delta > 0, one spectrum lies in [beta,alpha] and the other avoids (beta-delta,alpha+delta), with the roles interchangeable. | hβα and hδ are explicit, and hspectral is literally the disjunction of the two real-spectrum inclusions. | claimed_exact |
| The norm is an arbitrary source unitary-invariant norm and R has finite norm. | N : UnitaryInvariantNorm and hR : N.Mem R appear directly. UnitaryInvariantNorm is the existing public source-facing name for the audited PaperUnitaryInvariantNorm implementation structure. | claimed_exact |
| delta \|\|sin Theta0\|\| <= \|\|R\|\|. | The text after the theorem colon is exactly δ * N.gauge sinTheta₀ <= N.gauge R. The supporting sinTheta_unbounded_intervalExterior_paperUINorm_rclike theorem additionally certifies N.Mem sinTheta₀ after rewriting by hSinTheta₀. | claimed_exact |
| Infinite-dimensional and unbounded self-adjoint scope. | There is no FiniteDimensional hypothesis; A, A₀, and Λ₁ are `LinearPMap` values and the two expanded setup predicates carry the required domain conditions. | claimed_exact |

**Review note.** The canonical review declaration is also the intended paper-display declaration. It names sinTheta₀ as a theorem parameter but gives its concrete projection-block formula by a literal equality hypothesis in the same signature, so the claim after the colon is a one-to-one rendering of the printed inequality without an opaque angle definition. Only the domain-heavy trial and exact-coordinate setup is bundled, and both bundles are fully expanded by characteristic theorems in the local semantic dictionary. The stronger generic theorem remains supporting evidence for norm-ideal membership and the implementation proof bridge. CANONICAL WITNESS CORRECTED 2026-08-31. The row named `sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` as the exact source match. That was wrong on two counts: it carries only the bounded interval/exterior branch of the gap, while the source permits half-infinite separating intervals, and it drops the ideal-membership half of the conclusion. The canonical witness is now `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike`, added the same day: scalar-generic over `RCLike`, unbounded `LinearPMap` ambient operator, arbitrary Hilbert dimension, the whole `FormBoundedSylvesterGap` (interval/exterior plus both ordered semibounded configurations), an arbitrary `PaperUnitaryInvariantNorm`, and both conclusions. It is proved by taking the gap directly into the Ky-Fan-to-paper-norm promotion the interval/exterior theorem already ran, so it is a repackaging rather than a new argument, and the interval/exterior form is now a one-line consequence of it. `..._complex_ofRCLike` and `..._real_ofRCLike` are the compiled conformance checks: each restates the corresponding fixed-field endpoint's type verbatim and discharges it by the generic theorem with no adapter. The fixed-field endpoints remain as corroborating full-source witnesses and the interval/exterior theorem as a presentation specialization. The two `RCLike` capability classes in the generic signature are proof capabilities with instances for both source fields, not printed source hypotheses. CONFORMANCE TIED BY NAME 2026-08-31. The `_ofRCLike` wrappers restate a type, and a restatement cannot notice if the declaration it mirrors changes. `..._ofRCLike_conforms` closes that: an equation between two constants elaborates only when both sides have the same type, so it asserts exactly that the restatement is the fixed-field endpoint's type, and `rfl` discharges it by proof irrelevance. It is a type-level check by design and says nothing about the two proofs.

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

**Compiler-resolved type**

~~~~lean
@Submodule.opNorm_starProjection_sub_le_of_coercive : ∀ {𝕜 : Type u_1} {H : Type u_2} [inst : RCLike 𝕜]
  [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProductSpace 𝕜 H] [CompleteSpace H] {A B : H →L[𝕜] H},
  (↑A).IsSymmetric →
    (↑B).IsSymmetric →
      ∀ {U W : Submodule 𝕜 H} [inst_4 : U.HasOrthogonalProjection] [inst_5 : W.HasOrthogonalProjection],
        A.Reduces U →
          B.Reduces W →
            ∀ {c g : ℝ},
              0 < g →
                (∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)) →
                  (∀ x ∈ Uᗮ, RCLike.re (inner 𝕜 (A x) x) ≤ c * ‖x‖ ^ 2) →
                    (∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B x) x)) →
                      (∀ x ∈ Wᗮ, RCLike.re (inner 𝕜 (B x) x) ≤ c * ‖x‖ ^ 2) →
                        ‖U.starProjection - W.starProjection‖ ≤ ‖B - A‖ / g
~~~~

### Supporting scope declarations

- `TauCeti.opNorm_spectralSubspace_sub_le` — resolved; source located

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
- Every source unitary-invariant norm; finite/infinite dimensional and real/complex scope, with the appendix unbounded extension when the residual/perturbation is bounded.

### Canonical Lean declarations

#### `TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_paperUINorm_rclike`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/ScalarGenericFinite.lean:73`

~~~~lean
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
theorem tanTheta_directed_finiteDimensional_paperUINorm_rclike
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E)
    (_hrank : Module.finrank 𝕜 F = Module.finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hCompressionSpectrum :
      SpectrumIn (compression A X) ⊤ (Set.Icc β α))
    (hUnwantedSpectrum : SpectrumIn A Uᗮ (Set.Ici (α + δ)))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U)
    (hR : N.Mem (ritzResidual A X).toContinuousLinearMap) :
    N.Mem tanTheta0.toContinuousLinearMap ∧
      δ * N.gauge tanTheta0.toContinuousLinearMap ≤
        N.gauge (ritzResidual A X).toContinuousLinearMap
~~~~

**Compiler-resolved type**

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_paperUINorm_rclike : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜]
  {E F : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E]
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : E →ₗ[𝕜] E},
  A.IsSymmetric →
    ∀ {U : Submodule 𝕜 E} [inst_7 : U.HasOrthogonalProjection],
      TauCeti.IsInvariant A U →
        ∀ (X : F →ₗᵢ[𝕜] E),
          Module.finrank 𝕜 F = Module.finrank 𝕜 ↥U →
            ∀ {β α δ : ℝ},
              β ≤ α →
                0 < δ →
                  TauCeti.SpectrumIn (TauCeti.compression A X) ⊤ (Set.Icc β α) →
                    TauCeti.SpectrumIn A Uᗮ (Set.Ici (α + δ)) →
                      ∀ (tanTheta0 : F →ₗ[𝕜] E),
                        tanTheta0.singularValues = TauCeti.principalTangents (TauCeti.approximateSubspace X) U →
                          N.Mem (LinearMap.toContinuousLinearMap (TauCeti.ritzResidual A X)) →
                            N.Mem (LinearMap.toContinuousLinearMap tanTheta0) ∧
                              δ * N.gauge (LinearMap.toContinuousLinearMap tanTheta0) ≤
                                N.gauge (LinearMap.toContinuousLinearMap (TauCeti.ritzResidual A X))
~~~~

### Supporting scope declarations

- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm` — resolved; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_paperUINorm_real` — resolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_complex_of_crossedDefects` — resolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_real_of_crossedDefects` — resolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_paperUINorm_real` — resolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_raw_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_raw_paperUINorm_real` — resolved; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

The literal dimension-coherent source unitary-invariant norm. The new generic directed headline theorem uses it directly over arbitrary RCLike scalars.

~~~~lean
structure TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm : Type
number of parameters: 0
fields:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.finiteNorm : (n : ℕ) →
      TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.normalized : ((self.finiteNorm 1).gauge
        (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) =
      1
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.zero_pad : ∀ {n : ℕ} (x : Fin n → ℝ),
      (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
          (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
        (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
constructor:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.mk
    (finiteNorm : (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)))
    (normalized : ((finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1)
    (zero_pad :
      ∀ {n : ℕ} (x : Fin n → ℝ),
        (finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
            (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
          (finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x) :
    TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm
~~~~

#### `TauCeti.principalTangents`

The directed principal-tangent singular-value sequence used in the paper definition of tan Theta0.

~~~~lean
def TauCeti.principalTangents.{u_1, u_2} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            (U V : Submodule 𝕜 E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → ℕ →₀ ℝ :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] U V
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  Finsupp.mapRange Real.tan Real.tan_zero (TauCeti.principalAngles U V)
~~~~

#### `TauCeti.ritzResidual`

The Rayleigh--Ritz residual. In the generic headline theorem it appears directly on the right-hand side rather than through a bundled problem record.

~~~~lean
def TauCeti.ritzResidual.{u_1, u_2, u_3} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {F : Type u_3} →
              [inst_4 : NormedAddCommGroup F] →
                [inst_5 : InnerProductSpace 𝕜 F] → [FiniteDimensional 𝕜 F] → (E →ₗ[𝕜] E) → (F →ₗᵢ[𝕜] E) → F →ₗ[𝕜] E :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {F} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] A X =>
  TauCeti.residual A X (TauCeti.compression A X)
~~~~

#### `TauCeti.DavisKahan.CrossedDefectsEquivalent`

The paper-wide nonacute direct-rotation existence condition (3.5), needed only for the ambient whole-space tangent semantics in the general infinite-dimensional case.

~~~~lean
def TauCeti.DavisKahan.CrossedDefectsEquivalent.{u, u_1} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {H : Type u} →
      [inst_1 : NormedAddCommGroup H] →
        [inst_2 : InnerProductSpace 𝕜 H] →
          (U V : Submodule 𝕜 H) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → Prop :=
fun {𝕜} [RCLike 𝕜] {H} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] U V [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] =>
  Nonempty (↥(TauCeti.DavisKahan.halmosSourceDefect U V) ≃ₗᵢ[𝕜] ↥(TauCeti.DavisKahan.halmosTargetDefect U V))
~~~~

#### `TauCeti.DavisKahanExt.paperTanAngleOperatorC`

The canonical complex ambient tan(Theta) operator used by the unbounded whole-space scope companion.

~~~~lean
def TauCeti.DavisKahanExt.paperTanAngleOperatorC.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      [CompleteSpace E] →
        (U V : Submodule ℂ E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → E →L[ℂ] E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] U V [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] =>
  cfc Real.tan (TauCeti.DavisKahanExt.paperAngleOperatorC U V)
~~~~

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜]; no ℂ specialization appears in that headline type. Field-specific unbounded ambient declarations remain scope companions. | claimed_exact |
| spec(A0) subset [beta,alpha] and unwanted exact spectrum subset [alpha+delta,infinity). | hCompressionSpectrum and hUnwantedSpectrum are literal SpectrumIn hypotheses in tanTheta_directed_finiteDimensional_paperUINorm_rclike; TanThetaIntervalGap is constructed only inside the proof and is not part of the public signature. | claimed_exact |
| H0=0 / Rayleigh--Ritz choice. | The public conclusion is written directly in terms of ritzResidual A X, where X is the trial isometry and the coordinate compression is the Rayleigh--Ritz compression. | claimed_exact |
| delta \|\|tan Theta0\|\| <= \|\|R\|\|. | tanTheta_directed_finiteDimensional_paperUINorm_rclike concludes δ * N.gauge tanTheta0.toContinuousLinearMap <= N.gauge (ritzResidual A X).toContinuousLinearMap, with tanTheta0 constrained to have the principal-tangent singular values. | claimed_exact |
| delta \|\|tan Theta\|\| <= \|\|H\|\|. | The unbounded ambient source companion concludes the factor-one estimate for paperTanAngleOperatorC; its real sibling is compiler-checked as supporting scalar scope. | scope_companion |
| No separately assumed tangent-pole exclusion in the printed theorem. | The scalar-generic directed theorem assumes only the spectral placement and derives transversality in its engine. The ambient source companion uses the accepted nonlocal (3.5) semantics rather than a numerical pole hypothesis. | claimed_exact |

**Review note.** The directed residual half now has a scalar-generic, PaperUnitaryInvariantNorm, source-shaped canonical theorem whose public signature exposes the Ritz spectral placement instead of TanThetaIntervalGap. The harder ambient/unbounded half remains represented by the accepted source-shaped complex theorem plus its real companion because the current whole-space angle-operator implementation is field-specific. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

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

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/ScalarGenericFinite.lean:111`

~~~~lean
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
theorem sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike
    (N : PaperUnitaryInvariantNorm)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {β α δ : ℝ} (_hβα : β ≤ α) (hδ : 0 < δ)
    (hCompressionSpectrum : SpectrumIn M ⊤ (Set.Icc β α))
    (hUnwantedSpectrum :
      SpectrumIn A Uᗮ {lam : ℝ | lam ≤ β - δ ∨ α + δ ≤ lam})
    (hR : N.Mem (residual A X M).toContinuousLinearMap) :
    N.Mem (sinTwoThetaEmbedding U X).toContinuousLinearMap ∧
      δ * N.gauge (sinTwoThetaEmbedding U X).toContinuousLinearMap ≤
        2 * N.gauge (residual A X M).toContinuousLinearMap
~~~~

**Compiler-resolved type**

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜]
  {E F : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E]
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : E →ₗ[𝕜] E},
  A.IsSymmetric →
    ∀ {U : Submodule 𝕜 E} [inst_7 : U.HasOrthogonalProjection],
      TauCeti.IsInvariant A U →
        ∀ (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F},
          M.IsSymmetric →
            ∀ {β α δ : ℝ},
              β ≤ α →
                0 < δ →
                  TauCeti.SpectrumIn M ⊤ (Set.Icc β α) →
                    TauCeti.SpectrumIn A Uᗮ {lam | lam ≤ β - δ ∨ α + δ ≤ lam} →
                      N.Mem (LinearMap.toContinuousLinearMap (TauCeti.residual A X M)) →
                        N.Mem (LinearMap.toContinuousLinearMap (TauCeti.DavisKahanTheory.sinTwoThetaEmbedding U X)) ∧
                          δ *
                              N.gauge
                                (LinearMap.toContinuousLinearMap (TauCeti.DavisKahanTheory.sinTwoThetaEmbedding U X)) ≤
                            2 * N.gauge (LinearMap.toContinuousLinearMap (TauCeti.residual A X M))
~~~~

### Supporting scope declarations

- `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_directed_boundedResidual_blockRepresentative_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_paperUINorm_real` — resolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real` — resolved; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

The literal source unitary-invariant norm. The new directed headline theorem evaluates it over generic RCLike scalars.

~~~~lean
structure TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm : Type
number of parameters: 0
fields:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.finiteNorm : (n : ℕ) →
      TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.normalized : ((self.finiteNorm 1).gauge
        (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) =
      1
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.zero_pad : ∀ {n : ℕ} (x : Fin n → ℝ),
      (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
          (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
        (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
constructor:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.mk
    (finiteNorm : (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)))
    (normalized : ((finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1)
    (zero_pad :
      ∀ {n : ℕ} (x : Fin n → ℝ),
        (finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
            (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
          (finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x) :
    TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm
~~~~

#### `TauCeti.DavisKahanTheory.sinTwoThetaEmbedding`

The rectangular directed sin(2 Theta0) representative used by the scalar-generic headline theorem.

~~~~lean
def TauCeti.DavisKahanTheory.sinTwoThetaEmbedding.{u_1, u_2, u_3} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {F : Type u_3} →
              [inst_4 : NormedAddCommGroup F] →
                [inst_5 : InnerProductSpace 𝕜 F] →
                  [FiniteDimensional 𝕜 F] →
                    (U : Submodule 𝕜 E) → [U.HasOrthogonalProjection] → (F →ₗᵢ[𝕜] E) → F →ₗ[𝕜] E :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {F} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] U [U.HasOrthogonalProjection] X =>
  2 • TauCeti.sinThetaEmbedding U X ∘ₗ TauCeti.cosThetaMagnitude U X
~~~~

#### `TauCeti.DavisKahan.residual`

The literal residual A X - X M appearing on the right-hand side of the directed theorem.

~~~~lean
def TauCeti.DavisKahan.residual.{u_1, u_2, u_3} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          {F : Type u_3} →
            [inst_3 : NormedAddCommGroup F] →
              [inst_4 : InnerProductSpace 𝕜 F] → (E →L[𝕜] E) → (F →L[𝕜] E) → (F →L[𝕜] F) → F →L[𝕜] E :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    A X M =>
  A ∘SL X - X ∘SL M
~~~~

#### `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC`

The complex whole-space sin(2 Theta) operator used by the ambient perturbation scope companion.

~~~~lean
def TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      [CompleteSpace E] →
        (U V : Submodule ℂ E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → E →L[ℂ] E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] U V [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] =>
  cfc (fun t => Real.sin (2 * t)) (TauCeti.DavisKahanExt.paperAngleOperatorC U V)
~~~~

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜] and uses PaperUnitaryInvariantNorm directly. | claimed_exact |
| Interval/exterior spectral separation by delta. | hCompressionSpectrum places M in [beta,alpha] and hUnwantedSpectrum literally places the unwanted A-spectrum outside (beta-delta,alpha+delta); no local gap structure is visible in the headline type. | claimed_exact |
| delta \|\|sin(2 Theta0)\|\| <= 2 \|\|R\|\|. | sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike concludes the factor-two PaperUnitaryInvariantNorm estimate for sinTwoThetaEmbedding U X against residual A X M. | claimed_exact |
| delta \|\|sin(2 Theta)\|\| <= 2 \|\|H\|\|. | sinTwoTheta_ambient_bounded_paperUINorm_complex supplies the ambient source endpoint, with the real whole-space theorem compiler-checked as a scalar companion. | scope_companion |
| Infinite-dimensional and unbounded directed-residual scope. | The generic headline facade is finite-dimensional; the real and complex unbounded directed-residual theorems remain explicit supporting declarations and carry the full source scope. | scope_companion |

**Review note.** The directed residual conclusion now has a scalar-generic PaperUnitaryInvariantNorm facade with the interval/exterior hypotheses and residual written directly in its type. The ambient whole-space endpoint remains field-specific internally, so the complex source-shaped theorem stays as the second canonical declaration and its real sibling is a supporting scalar companion. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

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

#### `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:86`

~~~~lean
theorem tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike
    {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (N : PaperUnitaryInvariantNorm)
    {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[𝕜] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      DavisKahanTheory.absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H
~~~~

**Compiler-resolved type**

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike : ∀ {𝕜 : Type u_1}
  [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
  [inst_3 : CompleteSpace E] (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A H T : E →L[𝕜] E}
  {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 ↥U] {a b : ℝ},
  IsSelfAdjoint A →
    IsSelfAdjoint H →
      (∀ x ∈ U, A x ∈ U) →
        (∀ x ∈ U, H x ∈ Uᗮ) →
          (∀ x ∈ Uᗮ, H x ∈ U) →
            (∀ (x : E), T x ∈ Uᗮ) →
              (∀ x ∈ Uᗮ, T x = 0) →
                a < b →
                  (∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)) →
                    (∀ x ∈ Uᗮ, RCLike.re (inner 𝕜 (A x) x) ≤ a * ‖x‖ ^ 2) →
                      (∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y) →
                        ∀ (tanTwoTheta : E →L[𝕜] E) (π : ℕ ≃ ℕ),
                          (∀ (n : ℕ),
                              TauCeti.ApproximationNumber.approximationSingularValue (π n) tanTwoTheta =
                                TauCeti.DavisKahanTheory.absDoubleAngleTangent
                                  (TauCeti.ApproximationNumber.approximationSingularValue n T)) →
                            N.Mem H → N.Mem tanTwoTheta ∧ (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H
~~~~

### Supporting scope declarations

- `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_paperUINorm_real` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_paperUINorm_real` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_paperUINorm_complex` — resolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_paperUINorm_real` — resolved; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

The literal source unitary-invariant norm; tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike is already generic over RCLike 𝕜 at this norm scope.

~~~~lean
structure TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm : Type
number of parameters: 0
fields:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.finiteNorm : (n : ℕ) →
      TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.normalized : ((self.finiteNorm 1).gauge
        (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) =
      1
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.zero_pad : ∀ {n : ℕ} (x : Fin n → ℝ),
      (self.finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
          (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
        (self.finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x
constructor:
  TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.mk
    (finiteNorm : (n : ℕ) → TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)))
    (normalized : ((finiteNorm 1).gauge (EuclideanSpace.basisFun (Fin 1) ℂ) fun x => 1) = 1)
    (zero_pad :
      ∀ {n : ℕ} (x : Fin n → ℝ),
        (finiteNorm (n + 1)).gauge (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)
            (TauCeti.DavisKahan.ExactSinTheta.paperZeroPad x) =
          (finiteNorm n).gauge (EuclideanSpace.basisFun (Fin n) ℂ) x) :
    TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm
~~~~

#### `TauCeti.DavisKahanTheory.absDoubleAngleTangent`

The branch-free scalar function 2 t / |1-t^2| applied to graph-coordinate singular values; this is the generic theorem’s representation of |tan(2 Theta)|.

~~~~lean
def TauCeti.DavisKahanTheory.absDoubleAngleTangent : ℝ → ℝ :=
fun t => 2 * t / |1 - t ^ 2|
~~~~

#### `TauCeti.ApproximationNumber.approximationSingularValue`

The approximation-number singular-value sequence used to express the branch-free tangent representative in arbitrary Hilbert space.

~~~~lean
def TauCeti.ApproximationNumber.approximationSingularValue.{u, v, vF} : {𝕜 : Type u} →
  [inst : RCLike 𝕜] →
    {E : Type v} →
      {F : Type vF} →
        [inst_1 : NormedAddCommGroup E] →
          [inst_2 : InnerProductSpace 𝕜 E] →
            [inst_3 : NormedAddCommGroup F] → [inst_4 : InnerProductSpace 𝕜 F] → ℕ → (E →L[𝕜] F) → ℝ :=
fun {𝕜} [RCLike 𝕜] {E} {F} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    n K =>
  K.approximationNumber n
~~~~

#### `TauCeti.DavisKahan1970.paperDoubleSecant`

The source-shaped U,V directed-corner implementation used by the second canonical theorem; its invertibility is derived internally rather than assumed.

~~~~lean
def TauCeti.DavisKahan1970.paperDoubleSecant.{v} : {E : Type v} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      (U V : Submodule ℂ E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → E →L[ℂ] E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℂ E] U V [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  Ring.inverse
    (1 -
      2 * (TauCeti.DavisKahan1970.paperProjectorDifference U V * TauCeti.DavisKahan1970.paperProjectorDifference U V))
~~~~

#### `TauCeti.DavisKahan1970.paperProjectorDifference`

The projector-difference factor used to build the source-shaped directed tan(2 Theta0) representative.

~~~~lean
def TauCeti.DavisKahan1970.paperProjectorDifference.{v} : {E : Type v} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      (U V : Submodule ℂ E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → E →L[ℂ] E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℂ E] U V [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  V.starProjection - U.starProjection
~~~~

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike is an alias of the already proved branch-free theorem quantified over 𝕜 with [RCLike 𝕜] and the literal PaperUnitaryInvariantNorm. | claimed_exact |
| A has an ordered block gap and H is fully off diagonal. | The generic theorem writes the form bounds hUb/hUa and the two literal off-diagonal mapping hypotheses hHU/hHUperp directly; no named gap or oddness predicate hides them. | claimed_exact |
| The perturbed invariant subspace is arbitrary and no independent tan(2 Theta) pole hypothesis is assumed. | The generic theorem describes the invariant perturbed graph by hTmem, hTzero and hinv and uses the branch-free absDoubleAngleTangent singular values; it has no T<1, IsQuarterAcute, or cos(2 theta) premise. | claimed_exact |
| delta \|\|tan(2 Theta)\|\| <= 2 \|\|H\|\|. | With delta = b-a, tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike concludes (b-a) * N.gauge tanTwoTheta <= 2 * N.gauge H for every source norm. | claimed_exact |
| delta \|\|tan(2 Theta0)\|\| <= 2 \|\|R\|\| in the source-shaped U,V corner notation. | The second canonical declaration gives the literal compression-spectrum/off-diagonal directed-corner theorem with no caller-supplied pole certificate. | claimed_exact |
| Infinite-dimensional/unbounded scope. | The generic branch-free canonical theorem removes ambient finite-dimensionality but still assumes a finite-dimensional graph base U; the full arbitrary-dimensional and unbounded real/complex endpoints remain compiler-checked supporting declarations. | scope_companion |

**Review note.** Unlike tan Theta and sin 2Theta, the branch-free tan 2Theta paper-norm theorem was already scalar-generic. The review now promotes it to the canonical headline name. Its generic proof is necessarily graph-coordinate shaped, so the source-shaped U,V directed-corner theorem remains canonical alongside it and the report prints absDoubleAngleTangent/approximationSingularValue context explicitly. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

**Next action.** No hostile-review hole is currently recorded for this source passage. Preserve exact source scope and re-audit if the distributable source specification changes.
