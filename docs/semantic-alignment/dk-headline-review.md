# Semantic alignment review packet

This packet is generated from curated semantic-review fields in the source censuses. Human-written Lean headers are structural source evidence. Compiler output, when present, is elaborator-backed evidence about the Lean surface. The source-to-Lean correspondence remains the census author's explicit review claim.

**Compiler imports:** `DavisKahan.Sources.DavisKahan1970.SineTheta.PaperSurface`, `DavisKahan.Sources.DavisKahan1970.SineTheta.ScalarGeneric`, `DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions`, `DavisKahan.Sources.DavisKahan1970.GeneralSinTheta`, `DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm`, `DavisKahan.Sylvester.ScalarGeneric`, `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction`, `ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed`, `DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient`, `DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbientReal`, `DavisKahan.Sources.DavisKahan1970.TanThetaDirectedUnbounded`, `DavisKahan.Sources.DavisKahan1970.DirectedReal`, `Challenge.DavisKahan1970.Conformance`, `DavisKahan.Sources.DavisKahan1970.TanThetaAmbient`, `DavisKahan.Sources.DavisKahan1970.ScalarGenericFinite`, `DavisKahan.Sources.DavisKahan1970.Section2TanThetaPerturbation`, `DavisKahan.Sources.DavisKahan1970.PartIII`, `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry`, `ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz`, `DavisKahan.Geometry.Halmos.GenericRotationPredicates`, `DavisKahan.Geometry.Angle.PaperTanAngle`, `DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidual`, `DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidualReal`, `DavisKahan.Sources.DavisKahan1970.SinTwoTheta`, `DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded`, `DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbient`, `DavisKahan.Sources.DavisKahan1970.AmbientReal`, `DavisKahan.FiniteDimensional.Residual.AngleEmbeddings`, `DavisKahan.BoundedOperator.Compat`, `DavisKahan.Geometry.Angle.PaperDoubleAngle`, `DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExact`, `DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExactReal`, `DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact`, `DavisKahan.Sources.DavisKahan1970.TanTwoThetaReflectionAmbient`, `DavisKahan.Sources.DavisKahan1970.TanTwoThetaBranchFree`, `DavisKahan.DoubleAngle.TanTwoThetaBranchFree`, `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core`, `DavisKahan.Sources.DavisKahan1970.AmbientBlockVocabulary`, `ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector`, `ForTauCeti.Analysis.InnerProductSpace.SinTheta.DirectedBounds`

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

#### `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:343`

~~~~lean
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem sinTheta_unbounded_formGap_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
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

**Compiler probe failed to resolve this declaration.**

#### `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:457`

~~~~lean
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem sinTheta_unbounded_formGap_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
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

**Compiler probe failed to resolve this declaration.**

### Supporting scope declarations

- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex_ofRCLike` — unresolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real_ofRCLike` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_ofComponents_rclike` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_intervalExterior_paperUINorm_rclike` — unresolved; source located
- `DavisKahan1970.sinTheta_unbounded_intervalExterior_characterizedWitness_rclike` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_idealFamily_rclike` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_spectralSubspace_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTheta_unbounded_spectralSubspace_real` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace_complex` — unresolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex_ofRCLike_conforms` — unresolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real_ofRCLike_conforms` — unresolved; source located
- `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike` — unresolved; source located

### Local semantic dictionary

#### `DavisKahan1970.isTrialResidual_iff`

Expands the compact trial-residual hypothesis into the trial isometry, domain transport, and exact residual identity R = A E0 - E0 A0.

**Compiler probe failed to print this declaration.**

#### `DavisKahan1970.isExactSpectralDecomposition_iff`

Expands the compact exact-space hypothesis into isometric F0/F1 coordinates, orthogonality, completeness, domain transport, and A F1 = F1 Lambda1.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

Implementation structure behind the public theorem spelling UnitaryInvariantNorm: the dimension-coherent normalized unitary-invariant norm quantified over by Davis--Kahan.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan`

Scalar-field proof capability used to keep one theorem generic over RCLike. The repository provides instances for both source scalar fields, R and C; this is implementation evidence rather than an additional paper hypothesis.

**Compiler probe failed to print this declaration.**

#### `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`

Approximation-number min--max capability needed by the universal norm machinery. It has proved R and C instances and is not an extra source restriction.

**Compiler probe failed to print this declaration.**

#### `LinearPMap`

Mathlib's partial linear map: the repository representation of the paper's possibly unbounded self-adjoint operators. Dense domain, closed graph and self-adjointness are hypotheses of the theorems that need them, not fields of the carrier; the bundled DKPS record that once played this role was deleted on 2026-08-28.

**Compiler probe failed to print this declaration.**

#### `TauCeti.LinearPMap.realSpectrum`

Real spectrum of a self-adjoint partial/closed operator; the interval/exterior alternative itself remains literal in the canonical theorem.

**Compiler probe failed to print this declaration.**

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

2026-08-31 (second pass): canonical declarations follow the result inventory's `canonical_evidence`. Demoted to supporting: DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike -- the scalar-generic form carries proof-capability instance binders that the printed statement does not, and the two fixed-field endpoints state the result at the paper's two fields with no such binder.

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

**Compiler probe failed to resolve this declaration.**

### Supporting scope declarations

- `TauCeti.opNorm_spectralSubspace_sub_le` — unresolved; source located

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

#### `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:511`

~~~~lean
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem tanTheta_ambient_unboundedRitz_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
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
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean:392`

~~~~lean
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
theorem tanTheta_ambient_unboundedRitz_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
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
    N.Mem (paperTanAngleOperatorR U V) ∧
      delta * N.gauge (paperTanAngleOperatorR U V) ≤ N.gauge H
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:92`

~~~~lean
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem tanTheta_directed_unboundedTrial_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : TanTheta.UnboundedTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z
      (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean:135`

~~~~lean
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem tanTheta_directed_unboundedTrial_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    {Z : Submodule ℝ E} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : TanTheta.UnboundedTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSelfAdjointSpectralProjection A hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z
      (realSelfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual
~~~~

**Compiler probe failed to resolve this declaration.**

### Supporting scope declarations

- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_bounded_spectralGap_paperUINorm_real` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_complex_of_crossedDefects` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_bounded_paperUINorm_real_of_crossedDefects` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedOperator_boundedRitz_paperUINorm_real` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_raw_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_raw_paperUINorm_real` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_paperUINorm_rclike` — unresolved; source located
- `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial` — unresolved; source located
- `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm` — unresolved; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

The literal dimension-coherent source unitary-invariant norm. The new generic directed headline theorem uses it directly over arbitrary RCLike scalars.

**Compiler probe failed to print this declaration.**

#### `TauCeti.principalTangents`

The directed principal-tangent singular-value sequence used in the paper definition of tan Theta0.

**Compiler probe failed to print this declaration.**

#### `TauCeti.ritzResidual`

The Rayleigh--Ritz residual. In the generic headline theorem it appears directly on the right-hand side rather than through a bundled problem record.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahan.CrossedDefectsEquivalent`

The paper-wide nonacute direct-rotation existence condition (3.5), needed only for the ambient whole-space tangent semantics in the general infinite-dimensional case.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahanExt.paperTanAngleOperatorC`

The canonical complex ambient tan(Theta) operator used by the unbounded whole-space scope companion.

**Compiler probe failed to print this declaration.**

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

2026-08-31: the canonical declaration list here is now the counted result's `canonical_evidence` in `dev/davis-kahan-1970-formalization-result-inventory.json`, and the checker enforces that. Demoted to supporting: TauCeti.DavisKahan1970.tanTheta_directed_finiteDimensional_paperUINorm_rclike -- a finite-dimensional or capability-class facade cannot be the canonical witness for a result certified at unbounded infinite-dimensional scope.

2026-08-31 (coherent-clause audit): demoted to supporting because the compiler-printed type does not carry the scope the declaration was credited with: TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial, TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm.

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

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidual.lean:370`

~~~~lean
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Submodule ℂ H} [V.HasOrthogonalProjection]
  {M : V →L[ℂ] V} {R : V →L[ℂ] H}
  {A : H →ₗ.[ℂ] H}
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
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

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidualReal.lean:201`

~~~~lean
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {V : Submodule ℝ E} [V.HasOrthogonalProjection]
  {M : V →L[ℝ] V} {R : V →L[ℝ] E}
  {A : E →ₗ.[ℝ] E}
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
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

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:872`

~~~~lean
variable {Hc : Type v}
  [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
theorem sinTwoTheta_directed_unbounded_addBounded_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
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

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.sinTwoTheta_directed_unbounded_addBounded_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:576`

~~~~lean
variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
theorem sinTwoTheta_directed_unbounded_addBounded_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (A : Er →ₗ.[ℝ] Er)
    (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.Real.sinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.Real.sinTwoAngleOperatorRC
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean:286`

~~~~lean
variable {Hc : Type v}
  [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
theorem sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
    (A : Hc →ₗ.[ℂ] Hc) (hA : IsSelfAdjoint A)
    (Eop : Hc →L[ℂ] Hc) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean:421`

~~~~lean
variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
theorem sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (A : Er →ₗ.[ℝ] Er) (hA : IsSelfAdjoint A)
    (Eop : Er →L[ℝ] Er) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorR
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop
~~~~

**Compiler probe failed to resolve this declaration.**

### Supporting scope declarations

- `TauCeti.DavisKahan1970.sinTwoTheta_directed_boundedResidual_blockRepresentative_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_paperUINorm_real` — unresolved; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

The literal source unitary-invariant norm. The new directed headline theorem evaluates it over generic RCLike scalars.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahanTheory.sinTwoThetaEmbedding`

The rectangular directed sin(2 Theta0) representative used by the scalar-generic headline theorem.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahan.residual`

The literal residual A X - X M appearing on the right-hand side of the directed theorem.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC`

The complex whole-space sin(2 Theta) operator used by the ambient perturbation scope companion.

**Compiler probe failed to print this declaration.**

### Clause correspondence

| source clause | Lean realization | status |
| --- | --- | --- |
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜] and uses PaperUnitaryInvariantNorm directly. | claimed_exact |
| Interval/exterior spectral separation by delta. | hCompressionSpectrum places M in [beta,alpha] and hUnwantedSpectrum literally places the unwanted A-spectrum outside (beta-delta,alpha+delta); no local gap structure is visible in the headline type. | claimed_exact |
| delta \|\|sin(2 Theta0)\|\| <= 2 \|\|R\|\|. | sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike concludes the factor-two PaperUnitaryInvariantNorm estimate for sinTwoThetaEmbedding U X against residual A X M. | claimed_exact |
| delta \|\|sin(2 Theta)\|\| <= 2 \|\|H\|\|. | sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex and its real sibling supply the ambient endpoint at the result's own unbounded scope: unbounded self-adjoint LinearPMap ambient operator, bounded self-adjoint perturbation, genuine spectral subspaces, the whole FormBoundedSylvesterGap, an arbitrary PaperUnitaryInvariantNorm and the exact factor two.  The bounded ambient theorems are their specialization. | claimed_exact |
| Infinite-dimensional and unbounded directed-residual scope. | Both printed conclusions are now witnessed at unbounded infinite-dimensional scope over each field.  The scalar-generic facade is finite-dimensional and is supporting evidence only; it is not this result's witness. | claimed_exact |

**Review note.** The directed residual conclusion now has a scalar-generic PaperUnitaryInvariantNorm facade with the interval/exterior hypotheses and residual written directly in its type. The ambient whole-space endpoint remains field-specific internally, so the complex source-shaped theorem stays as the second canonical declaration and its real sibling is a supporting scalar companion. The packet presents one source-shaped declaration as the primary alignment object; field-, ambient-, unbounded-, and implementation-specific companions are retained under supporting scope.

2026-08-31: the canonical declaration list here is now the counted result's `canonical_evidence` in `dev/davis-kahan-1970-formalization-result-inventory.json`, and the checker enforces that. Demoted to supporting: TauCeti.DavisKahan1970.sinTwoTheta_directed_finiteDimensional_paperUINorm_rclike -- a finite-dimensional or capability-class facade cannot be the canonical witness for a result certified at unbounded infinite-dimensional scope.

2026-08-31 (later the same day): the AMBIENT clause is no longer a scope companion.  `sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` and its real sibling prove it at the row's own unbounded scope, by identifying the ambient double angle between U and V with an ambient SINGLE angle between U and its mirror image through V and applying the common-domain Proposition 6.1.  The bounded ambient endpoints are demoted to supporting evidence as their own specialization.

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

#### `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExact.lean:77`

~~~~lean
variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]
theorem tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
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
    (hRmem : N.Mem (paperBlockCompression
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)) :
    IsUnit
        ((TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z *
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z) ∧
      N.Mem (reflectionTangentCorner
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ∧
      (b - a) * N.gauge (reflectionTangentCorner
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) ≤
        2 * N.gauge (paperBlockCompression
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ
          (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:196`

~~~~lean
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
theorem tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
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

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_paperUINorm_complex`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedAmbientExact.lean:466`

~~~~lean
variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]
theorem tanTwoTheta_ambient_unbounded_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
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
    N.Mem (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B
~~~~

**Compiler probe failed to resolve this declaration.**

#### `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_paperUINorm_real`

**Human-written Lean statement**

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:525`

~~~~lean
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
theorem tanTwoTheta_ambient_unbounded_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
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
    N.Mem (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B
~~~~

**Compiler probe failed to resolve this declaration.**

### Supporting scope declarations

- `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_paperUINorm_real` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_bounded_spectralGap_paperUINorm_real` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_paperUINorm_complex` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_blockRepresentative_paperUINorm_real` — unresolved; source located
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike` — unresolved; source located

### Local semantic dictionary

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

The literal source unitary-invariant norm; tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike is already generic over RCLike 𝕜 at this norm scope.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahanTheory.absDoubleAngleTangent`

The branch-free scalar function 2 t / |1-t^2| applied to graph-coordinate singular values; this is the generic theorem’s representation of |tan(2 Theta)|.

**Compiler probe failed to print this declaration.**

#### `TauCeti.ApproximationNumber.approximationSingularValue`

The approximation-number singular-value sequence used to express the branch-free tangent representative in arbitrary Hilbert space.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahan1970.paperDoubleSecant`

The source-shaped U,V directed-corner implementation used by the second canonical theorem; its invertibility is derived internally rather than assumed.

**Compiler probe failed to print this declaration.**

#### `TauCeti.DavisKahan1970.paperProjectorDifference`

The projector-difference factor used to build the source-shaped directed tan(2 Theta0) representative.

**Compiler probe failed to print this declaration.**

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

2026-08-31: the canonical declaration list here is now the counted result's `canonical_evidence` in `dev/davis-kahan-1970-formalization-result-inventory.json`, and the checker enforces that. Demoted to supporting: TauCeti.DavisKahan1970.tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike -- a finite-dimensional or capability-class facade cannot be the canonical witness for a result certified at unbounded infinite-dimensional scope.

**Next action.** No hostile-review hole is currently recorded for this source passage. Preserve exact source scope and re-audit if the distributable source specification changes.
