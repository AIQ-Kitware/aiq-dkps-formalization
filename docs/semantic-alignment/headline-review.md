# Semantic alignment review: headline mathematical statements

Generated: `2026-08-13T17:35:49+00:00`
Repository commit: `26271eb95ccfc971d491b48e43547f3802c05c3a`
Working tree clean: `no`
Importance threshold: `headline`
Papers: Davis--Kahan 1970, Yu--Wang--Samworth 2015
Compiler semantic probe run: `yes`
Compiler probe exit code: `1`

## Review purpose

This is a deliberately small semantic-review surface, not a full-paper census. For each selected headline claim it contains enough of both sides of the translation to let a mathematically knowledgeable reviewer decide whether the Lean theorem states the same claim under the same hypotheses and scope.

The **normalized source statement and correspondence table are maintained claims of this project**. The Lean theorem types and local-definition bodies are obtained from the compiler on this commit. The reviewer's job is to challenge the correspondence between them.

Project-local definitions are expanded only when they hide mathematically relevant content in a headline theorem type. The packet does not recursively dump implementation dependencies.

## Davis--Kahan 1970

### Davis--Kahan single-angle sin theta theorem

Review priority: `headline`

**Source anchor:** Section 2, sin theta theorem

The Section 2 sin-theta theorem: interval/exterior spectral separation controls the directed sine of the subspace angle by the residual, with sharp factor one.

**Normalized source statement**

*Setup:*

- A0 is the trial/compressed self-adjoint operator, Lambda1 is the complementary exact self-adjoint block, R is the residual, and Theta0 is the directed angle from the trial subspace to the exact subspace.

*Hypotheses:*

- There are beta <= alpha and delta > 0 such that spec(A0) is contained in [beta, alpha] and spec(Lambda1) avoids (beta-delta, alpha+delta), or the same interval/exterior condition with A0 and Lambda1 interchanged.
- The norm is an arbitrary source unitary-invariant norm and the residual belongs to its norm ideal whenever that norm is finite.

*Conclusion:*

- delta * ||sin Theta0|| <= ||R||.

*Scope:*

- The paper states the result in finite and infinite dimension, over real or complex Hilbert spaces.
- The unbounded self-adjoint extension is included when the domain condition holds and the residual/norm expression is bounded and meaningful.

**Canonical compiler-resolved Lean statement(s)**

`TauCeti.DavisKahan1970.sinTheta_headline_generic`

~~~~lean
@TauCeti.DavisKahan1970.sinTheta_headline_generic : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E F G H : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E]
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : CompleteSpace F]
  [inst_7 : NormedAddCommGroup G] [inst_8 : InnerProductSpace 𝕜 G] [inst_9 : CompleteSpace G]
  [inst_10 : NormedAddCommGroup H] [inst_11 : InnerProductSpace 𝕜 H] [inst_12 : CompleteSpace H]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] [TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan 𝕜]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) (A : TauCeti.DavisKahanExt.ClosedOperator)
  (A₀ : TauCeti.DavisKahanExt.ClosedOperator) (Λ₁ : TauCeti.DavisKahanExt.ClosedOperator) (E₀ : F →L[𝕜] E)
  (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E),
  A.IsSelfAdjoint →
    A₀.IsSelfAdjoint →
      Λ₁.IsSelfAdjoint →
        TauCeti.DavisKahan.IsometricEmbedding E₀ →
          TauCeti.DavisKahan.IsometricEmbedding F₀ →
            TauCeti.DavisKahan.IsometricEmbedding F₁ →
              ContinuousLinearMap.adjoint F₀ ∘SL F₁ = 0 →
                F₀ ∘SL ContinuousLinearMap.adjoint F₀ + F₁ ∘SL ContinuousLinearMap.adjoint F₁ =
                    ContinuousLinearMap.id 𝕜 E →
                  ∀ (hE₀dom : ∀ (x : ↥A₀.domain), E₀ ↑x ∈ A.domain) (hF₁dom : ∀ (y : ↥Λ₁.domain), F₁ ↑y ∈ A.domain),
                    (∀ (x : ↥A₀.domain), A.toLinearMap ⟨E₀ ↑x, ⋯⟩ - E₀ (A₀.toLinearMap x) = R ↑x) →
                      (∀ (y : ↥Λ₁.domain), A.toLinearMap ⟨F₁ ↑y, ⋯⟩ = F₁ (Λ₁.toLinearMap y)) →
                        ∀ {β α δ : ℝ},
                          β ≤ α →
                            0 < δ →
                              TauCeti.LinearPMap.realSpectrum A₀.toLinearPMap ⊆ Set.Icc β α ∧
                                    TauCeti.LinearPMap.realSpectrum Λ₁.toLinearPMap ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x} ∨
                                  TauCeti.LinearPMap.realSpectrum Λ₁.toLinearPMap ⊆ Set.Icc β α ∧
                                    TauCeti.LinearPMap.realSpectrum A₀.toLinearPMap ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x} →
                                N.Mem R →
                                  N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL E₀) ∧
                                    δ *
                                        N.gauge
                                          ((ContinuousLinearMap.id 𝕜 E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL
                                            E₀) ≤
                                      N.gauge R
~~~~

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The literal dimension-coherent unitary-invariant norm quantified over by Davis--Kahan; the generic headline theorem uses this source definition directly.

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

`TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan` — A scalar-field capability used to state one theorem over generic RCLike 𝕜. The repository proves instances for both scalar fields in the paper, ℝ and ℂ; it is implementation evidence, not an additional paper hypothesis.

~~~~lean
class TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.{u, v} (𝕜 : Type u) [RCLike 𝕜] : Prop
number of parameters: 2
fields:
  TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.out : ∀ {E F : Type v} [inst : NormedAddCommGroup E]
      [inst_1 : InnerProductSpace 𝕜 E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup F]
      [inst_4 : InnerProductSpace 𝕜 F] [inst_5 : CompleteSpace F] {A : TauCeti.DavisKahanExt.ClosedOperator}
      {B : TauCeti.DavisKahanExt.ClosedOperator},
      A.IsSelfAdjoint →
        B.IsSelfAdjoint →
          ∀ {X C : F →L[𝕜] E} {δ : ℝ},
            0 < δ →
              TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap A B δ →
                TauCeti.DavisKahan.ExactSinTheta.HasClosedSylvesterEquation A B X C →
                  ∀ (k : ℕ),
                    δ * TauCeti.ApproximationNumber.kyFanApproximationGauge k X ≤
                      TauCeti.ApproximationNumber.kyFanApproximationGauge k C
constructor:
  TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan.mk.{u, v} {𝕜 : Type u} [RCLike 𝕜]
    (out :
      ∀ {E F : Type v} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace 𝕜 E] [inst_2 : CompleteSpace E]
        [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] [inst_5 : CompleteSpace F]
        {A : TauCeti.DavisKahanExt.ClosedOperator} {B : TauCeti.DavisKahanExt.ClosedOperator},
        A.IsSelfAdjoint →
          B.IsSelfAdjoint →
            ∀ {X C : F →L[𝕜] E} {δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap A B δ →
                  TauCeti.DavisKahan.ExactSinTheta.HasClosedSylvesterEquation A B X C →
                    ∀ (k : ℕ),
                      δ * TauCeti.ApproximationNumber.kyFanApproximationGauge k X ≤
                        TauCeti.ApproximationNumber.kyFanApproximationGauge k C) :
    TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan 𝕜
~~~~

`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere` — The approximation-number min--max capability needed by the universal norm machinery. It likewise has proved ℝ and ℂ instances and is not an extra mathematical restriction on the paper theorem.

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

`TauCeti.DavisKahanExt.ClosedOperator` — The repository representation of a densely defined closed operator used for the paper's possibly unbounded self-adjoint operators.

~~~~lean
structure TauCeti.DavisKahanExt.ClosedOperator.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] : Type u_2
number of parameters: 5
fields:
  TauCeti.DavisKahanExt.ClosedOperator.domain : Submodule 𝕜 E
  TauCeti.DavisKahanExt.ClosedOperator.toLinearMap : ↥self.domain →ₗ[𝕜] E
  TauCeti.DavisKahanExt.ClosedOperator.dense_domain : Dense ↑self.domain
  TauCeti.DavisKahanExt.ClosedOperator.closed_graph : IsClosed (Set.range fun x => (↑x, self.toLinearMap x))
constructor:
  TauCeti.DavisKahanExt.ClosedOperator.mk.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {E : Type u_2} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (domain : Submodule 𝕜 E) (toLinearMap : ↥domain →ₗ[𝕜] E) (dense_domain : Dense ↑domain)
    (closed_graph : IsClosed (Set.range fun x => (↑x, toLinearMap x))) : TauCeti.DavisKahanExt.ClosedOperator
~~~~

`TauCeti.LinearPMap.realSpectrum` — The real spectrum of a self-adjoint partial/closed operator. The interval/exterior alternative is written directly in the canonical theorem rather than hidden behind a local gap structure.

~~~~lean
def TauCeti.LinearPMap.realSpectrum.{u, v} : {𝕜 : Type u} →
  [inst : RCLike 𝕜] →
    {E : Type v} → [inst_1 : NormedAddCommGroup E] → [inst_2 : InnerProductSpace 𝕜 E] → (E →ₗ.[𝕜] E) → Set ℝ :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] A => (TauCeti.LinearPMap.realResolventSet A)ᶜ
~~~~

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The scalar field is real or complex. | The canonical theorem quantifies over 𝕜 with [RCLike 𝕜]. The only extra scalar capability binders are HasUnboundedSylvesterKyFan and HasMinMaxLowerBoundEverywhere, for which the repository has proved ℝ and ℂ instances. | `claimed_exact` |
| A, A0, and Lambda1 are self-adjoint, with E0 the trial isometry and F0,F1 orthogonal exact-space coordinates. | A, A₀, Λ₁, E₀, F₀, and F₁ are explicit arguments. Self-adjointness, isometry of all three coordinate maps, F₀†F₁=0, and F₀F₀†+F₁F₁†=I are explicit hypotheses rather than fields of a bundled problem structure. | `claimed_exact` |
| R = A E0 - E0 A0 on the operator domain, while F1 intertwines Lambda1 with A. | hE₀dom, hF₁dom, hresidual, and hintertwines state the domain compatibility, residual equation, and complementary intertwining pointwise in the theorem signature. | `claimed_exact` |
| For beta <= alpha and delta > 0, one of spec(A0), spec(Lambda1) lies in [beta,alpha] and the other avoids (beta-delta,alpha+delta), with the roles interchangeable. | hβα and hδ are explicit, and hspectral is literally the disjunction of the two real-spectrum inclusions; no named gap predicate hides the interval/exterior condition. | `claimed_exact` |
| The norm is an arbitrary source unitary-invariant norm and R has finite norm. | N : PaperUnitaryInvariantNorm and hR : N.Mem R appear directly. | `claimed_exact` |
| delta \|\|sin Theta0\|\| <= \|\|R\|\|. | The conclusion is δ * N.gauge ((I - F₀F₀†) E₀) <= N.gauge R, together with membership of that directed sine operator in the same source norm ideal. | `claimed_exact` |
| Infinite-dimensional and unbounded self-adjoint scope. | There is no FiniteDimensional hypothesis; A, A₀, and Λ₁ are ClosedOperator values and the residual/intertwining equations carry their domain hypotheses explicitly. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.DavisKahan1970.sinTheta_unbounded_exact_generic`

~~~~lean
@TauCeti.DavisKahan1970.sinTheta_unbounded_exact_generic : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E F G H : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E]
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : CompleteSpace F]
  [inst_7 : NormedAddCommGroup G] [inst_8 : InnerProductSpace 𝕜 G] [inst_9 : CompleteSpace G]
  [inst_10 : NormedAddCommGroup H] [inst_11 : InnerProductSpace 𝕜 H] [inst_12 : CompleteSpace H]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜] [TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan 𝕜]
  (N : TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily 𝕜)
  (D : TauCeti.DavisKahan.ExactSinTheta.UnboundedSinThetaData) (F₀ : H →L[𝕜] E),
  TauCeti.DavisKahanExt.ClosedOperator.IsSelfAdjoint D.A →
    TauCeti.DavisKahanExt.ClosedOperator.IsSelfAdjoint D.A₀ →
      TauCeti.DavisKahanExt.ClosedOperator.IsSelfAdjoint D.Λ₁ →
        TauCeti.DavisKahan.IsometricEmbedding D.X →
          TauCeti.DavisKahan.ExactSinTheta.OrthogonalExactDecomposition F₀ D.F₁ →
            ∀ {δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap D.A₀ D.Λ₁ δ →
                  N.Mem D.residual →
                    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL D.X) ∧
                      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘SL ContinuousLinearMap.adjoint F₀) ∘SL D.X) ≤
                        N.gauge D.residual
~~~~

`TauCeti.DavisKahan1970.sinTheta_spectralSubspace`

~~~~lean
@TauCeti.DavisKahan1970.sinTheta_spectralSubspace : ∀ {E F : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup F]
  [inst_4 : InnerProductSpace ℂ F] [inst_5 : CompleteSpace F]
  (N : TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily ℂ) (A : TauCeti.DavisKahanExt.ClosedOperator)
  (hA : A.IsSelfAdjoint) (S : Set ℝ) (hS : MeasurableSet S) (A0 : TauCeti.DavisKahanExt.ClosedOperator),
  A0.IsSelfAdjoint →
    ∀ (X Rop : F →L[ℂ] E),
      TauCeti.DavisKahan.IsometricEmbedding X →
        ∀ (hXdom : ∀ (x : ↥A0.domain), X ↑x ∈ A.domain),
          (∀ (x : ↥A0.domain), A.toLinearMap ⟨X ↑x, ⋯⟩ - X (A0.toLinearMap x) = Rop ↑x) →
            ∀ {δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap A0
                    (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Sᶜ ⋯) δ →
                  N.Mem Rop →
                    N.Mem
                        ((ContinuousLinearMap.id ℂ E -
                            TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion A hA S hS ∘SL
                              ContinuousLinearMap.adjoint
                                (TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion A hA S hS)) ∘SL
                          X) ∧
                      δ *
                          N.gauge
                            ((ContinuousLinearMap.id ℂ E -
                                TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion A hA S hS ∘SL
                                  ContinuousLinearMap.adjoint
                                    (TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion A hA S hS)) ∘SL
                              X) ≤
                        N.gauge Rop
~~~~

`TauCeti.DavisKahan1970.sinTheta_real_spectralSubspace`

~~~~lean
@TauCeti.DavisKahan1970.sinTheta_real_spectralSubspace : ∀ {E F : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup F]
  [inst_4 : InnerProductSpace ℝ F] [inst_5 : CompleteSpace F]
  (N : TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily ℝ) (A : TauCeti.DavisKahanExt.ClosedOperator)
  (hA : A.IsSelfAdjoint) (S : Set ℝ) (hS : MeasurableSet S) (A0 : TauCeti.DavisKahanExt.ClosedOperator),
  A0.IsSelfAdjoint →
    ∀ (X Rop : F →L[ℝ] E),
      TauCeti.DavisKahan.IsometricEmbedding X →
        ∀ (hXdom : ∀ (x : ↥A0.domain), X ↑x ∈ A.domain),
          (∀ (x : ↥A0.domain), A.toLinearMap ⟨X ↑x, ⋯⟩ - X (A0.toLinearMap x) = Rop ↑x) →
            ∀ {δ : ℝ},
              0 < δ →
                TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap A0
                    (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Sᶜ ⋯) δ →
                  N.Mem Rop →
                    N.Mem
                        ((ContinuousLinearMap.id ℝ E -
                            TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspaceInclusion A hA S
                                hS ∘SL
                              ContinuousLinearMap.adjoint
                                (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspaceInclusion A
                                  hA S hS)) ∘SL
                          X) ∧
                      δ *
                          N.gauge
                            ((ContinuousLinearMap.id ℝ E -
                                TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspaceInclusion A hA
                                    S hS ∘SL
                                  ContinuousLinearMap.adjoint
                                    (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspaceInclusion
                                      A hA S hS)) ∘SL
                              X) ≤
                        N.gauge Rop
~~~~

`TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace`

~~~~lean
@TauCeti.DavisKahan1970.sinTheta_bounded_spectralSubspace : ∀ {E F : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup F]
  [inst_4 : InnerProductSpace ℂ F] [inst_5 : CompleteSpace F]
  (N : TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily ℂ) (A : E →L[ℂ] E) (hA : (↑A).IsSymmetric) (S : Set ℝ)
  (hS : MeasurableSet S) (A0 : F →L[ℂ] F),
  (↑A0).IsSymmetric →
    ∀ (X : F →L[ℂ] E),
      TauCeti.DavisKahan.IsometricEmbedding X →
        ∀ {δ : ℝ},
          0 < δ →
            TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A0)
                (TauCeti.DavisKahan.selfAdjointSpectralRestriction (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A) ⋯
                  Sᶜ ⋯)
                δ →
              N.Mem (TauCeti.DavisKahan.ExactSinTheta.generalResidual A X A0) →
                N.Mem
                    ((ContinuousLinearMap.id ℂ E -
                        TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion
                            (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A) ⋯ S hS ∘SL
                          ContinuousLinearMap.adjoint
                            (TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion
                              (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A) ⋯ S hS)) ∘SL
                      X) ∧
                  δ *
                      N.gauge
                        ((ContinuousLinearMap.id ℂ E -
                            TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion
                                (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A) ⋯ S hS ∘SL
                              ContinuousLinearMap.adjoint
                                (TauCeti.DavisKahan.selfAdjointSpectralSubspaceInclusion
                                  (TauCeti.DavisKahanExt.ClosedOperator.ofBounded A) ⋯ S hS)) ∘SL
                          X) ≤
                    N.gauge (TauCeti.DavisKahan.ExactSinTheta.generalResidual A X A0)
~~~~

</details>

**Maintainer note:** The canonical review declaration is now scalar-generic and deliberately unbundled: its type exposes the paper operators, coordinate maps, domain equations, interval/exterior spectral alternative, source unitary-invariant norm, and conclusion directly. Field-specific and more abstract natural-input theorems remain supporting declarations rather than the primary semantic-review object.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

### Sharp Davis--Kahan projector-difference theorem

Review priority: `headline` (derived review target)

**Provenance:** Derived review target: this is the sharp projector formulation obtained from the Davis--Kahan sin-theta theorem together with the two-projection norm identity, not a fifth separately printed Section 2 theorem.

The canonical projector form of the factor-one sin-theta estimate: for two reducing high-side subspaces separated from their complements by the same gap g, ||P_U - P_W|| <= ||B-A||/g.

**Normalized source statement**

*Setup:*

- A and B are self-adjoint operators; U and W are reducing selected subspaces; P_U and P_W are their orthogonal projections.

*Hypotheses:*

- There is a cut c and g>0 such that U and W lie on the high side c+g while U^perp and W^perp lie on the low side c.

*Conclusion:*

- ||P_U - P_W|| <= ||B-A|| / g.

*Scope:*

- This packet asks the reviewer to validate the mathematical provenance from the source sin-theta theorem, not to treat this as a separately printed Davis--Kahan theorem.

**Canonical compiler-resolved Lean statement(s)**

`Submodule.opNorm_starProjection_sub_le_of_coercive`

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

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| A common two-sided gap g separates each selected subspace from its orthogonal complement. | The four quadratic-form inequalities around c and c+g are written literally in the canonical theorem. | `derived` |
| Projector distance is bounded with factor one. | The conclusion is \|\|U.starProjection - W.starProjection\|\| <= \|\|B-A\|\| / g. | `derived` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.opNorm_spectralSubspace_sub_le`

~~~~lean
@TauCeti.opNorm_spectralSubspace_sub_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E},
  A.IsSymmetric →
    B.IsSymmetric →
      ∀ {s t : Set ℝ} {c g ε : ℝ},
        0 < g →
          TauCeti.SpectrumIn A (TauCeti.spectralSubspace A s) (Set.Ici (c + g)) →
            TauCeti.SpectrumIn A (TauCeti.spectralSubspace A s)ᗮ (Set.Iic c) →
              TauCeti.SpectrumIn B (TauCeti.spectralSubspace B t) (Set.Ici (c + g)) →
                TauCeti.SpectrumIn B (TauCeti.spectralSubspace B t)ᗮ (Set.Iic c) →
                  0 ≤ ε →
                    (∀ (x : E), ‖(B - A) x‖ ≤ ε * ‖x‖) →
                      ‖(TauCeti.spectralSubspace A s).starProjection - (TauCeti.spectralSubspace B t).starProjection‖ ≤
                        ε / g
~~~~

</details>

**Independent reviewer verdict:** `PASS faithful derived form` / `FAIL` / `UNCERTAIN`

- Verdict: _fill in_
- Is the claimed derivation from the source theorem legitimate? _fill in_
- Any stronger hidden hypothesis in Lean? _fill in_

---

### Davis--Kahan single-angle tan theta theorem

Review priority: `headline`

**Source anchor:** Section 2, tan theta theorem

The Section 2 tan-theta theorem: an ordered one-sided gap plus the Rayleigh--Ritz/off-diagonal condition gives the directed residual and ambient perturbation tangent bounds with sharp factor one.

**Normalized source statement**

*Setup:*

- A0 is the Rayleigh--Ritz compression on the trial subspace, Lambda1 is the unwanted exact block, R is the Ritz residual, H is the full perturbation, and Theta0/Theta are directed/ambient angles.

*Hypotheses:*

- spec(A0) is contained in [beta,alpha], spec(Lambda1) is contained in [alpha+delta,infinity), and delta>0.
- H0=0, equivalently A0 is the Rayleigh--Ritz compression in the paper setup.
- For the ambient tangent statement, the standing Section 3 direct-rotation existence condition is required whenever the angle norm would otherwise be undefined.

*Conclusion:*

- delta * ||tan Theta0|| <= ||R||.
- delta * ||tan Theta|| <= ||H||.

*Scope:*

- Every source unitary-invariant norm; finite/infinite dimensional and real/complex scope, with the appendix unbounded extension when the residual/perturbation is bounded.

**Canonical compiler-resolved Lean statement(s)**

`TauCeti.DavisKahan1970.tanTheta_headline_generic_directed`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_headline_generic_directed : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E F : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E]
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

`TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) (A : TauCeti.DavisKahan.DKClosedOperator)
  {U V : Submodule ℂ E} [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (D : TauCeti.DavisKahan.TanTheta.UnboundedTrialBlock A U) (H : E →L[ℂ] E),
  IsSelfAdjoint H →
    ∀ {alpha delta : ℝ},
      0 < delta →
        ∀ (hVdom : ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain),
          (∀ (x : ↥A.domain), Vᗮ.starProjection (A.toLinearMap x) = A.toLinearMap ⟨Vᗮ.starProjection ↑x, ⋯⟩) →
            (∀ (z : ↥U), RCLike.re (inner ℂ (D.operator z) z) ≤ alpha * ‖z‖ ^ 2) →
              (∀ y ∈ Vᗮ,
                  ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (A.toLinearMap ⟨y, hy⟩) y)) →
                TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent U V →
                  D.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL →
                    N.Mem H →
                      N.Mem (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) ∧
                        delta * N.gauge (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) ≤ N.gauge H
~~~~

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The literal dimension-coherent source unitary-invariant norm. The new generic directed headline theorem uses it directly over arbitrary RCLike scalars.

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

`TauCeti.DavisKahanTheory.principalTangents` — The directed principal-tangent singular-value sequence used in the paper definition of tan Theta0.

> **UNRESOLVED DEFINITION:** build/semantic-review-qry9vrso.lean:83:7: error(lean.unknownIdentifier): Unknown constant `TauCeti.DavisKahanTheory.principalTangents`

`TauCeti.DavisKahanTheory.ritzResidual` — The Rayleigh--Ritz residual. In the generic headline theorem it appears directly on the right-hand side rather than through a bundled problem record.

> **UNRESOLVED DEFINITION:** build/semantic-review-qry9vrso.lean:87:7: error(lean.unknownIdentifier): Unknown constant `TauCeti.DavisKahanTheory.ritzResidual`

`TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent` — The paper-wide nonacute direct-rotation existence condition (3.5), needed only for the ambient whole-space tangent semantics in the general infinite-dimensional case.

~~~~lean
def TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent.{u, u_1} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {H : Type u} →
      [inst_1 : NormedAddCommGroup H] →
        [inst_2 : InnerProductSpace 𝕜 H] →
          (U V : Submodule 𝕜 H) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → Prop :=
fun {𝕜} [RCLike 𝕜] {H} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] U V [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] =>
  Nonempty (↥(TauCeti.DavisKahan.halmosSourceDefect U V) ≃ₗᵢ[𝕜] ↥(TauCeti.DavisKahan.halmosTargetDefect U V))
~~~~

`TauCeti.DavisKahanExt.paperTanAngleOperatorC` — The canonical complex ambient tan(Theta) operator used by the unbounded whole-space scope companion.

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

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜]; no ℂ specialization appears in that headline type. Field-specific unbounded ambient declarations remain scope companions. | `claimed_exact` |
| spec(A0) subset [beta,alpha] and unwanted exact spectrum subset [alpha+delta,infinity). | hCompressionSpectrum and hUnwantedSpectrum are literal SpectrumIn hypotheses in tanTheta_headline_generic_directed; TanThetaIntervalGap is constructed only inside the proof and is not part of the public signature. | `claimed_exact` |
| H0=0 / Rayleigh--Ritz choice. | The public conclusion is written directly in terms of ritzResidual A X, where X is the trial isometry and the coordinate compression is the Rayleigh--Ritz compression. | `claimed_exact` |
| delta \|\|tan Theta0\|\| <= \|\|R\|\|. | tanTheta_headline_generic_directed concludes δ * N.gauge tanTheta0.toContinuousLinearMap <= N.gauge (ritzResidual A X).toContinuousLinearMap, with tanTheta0 constrained to have the principal-tangent singular values. | `claimed_exact` |
| delta \|\|tan Theta\|\| <= \|\|H\|\|. | The unbounded ambient source companion concludes the factor-one estimate for paperTanAngleOperatorC; its real sibling is compiler-checked as supporting scalar scope. | `scope_companion` |
| No separately assumed tangent-pole exclusion in the printed theorem. | The scalar-generic directed theorem assumes only the spectral placement and derives transversality in its engine. The ambient source companion uses the accepted nonlocal (3.5) semantics rather than a numerical pole hypothesis. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`

~~~~lean
@TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {F : Type u_3}
  [inst_4 : NormedAddCommGroup F] [inst_5 : InnerProductSpace 𝕜 F] [inst_6 : FiniteDimensional 𝕜 F]
  (N : TauCeti.RectangularUnitarilyInvariantSeminorm 𝕜 F E) {A : E →ₗ[𝕜] E},
  A.IsSymmetric →
    ∀ {U : Submodule 𝕜 E} [inst_7 : U.HasOrthogonalProjection],
      TauCeti.IsInvariant A U →
        ∀ (X : F →ₗᵢ[𝕜] E),
          Module.finrank 𝕜 F = Module.finrank 𝕜 ↥U →
            ∀ {β α δ : ℝ},
              β ≤ α →
                0 < δ →
                  TauCeti.DavisKahanTheory.TanThetaIntervalGap A U X β α δ →
                    ∀ (tanTheta0 : F →ₗ[𝕜] E),
                      tanTheta0.singularValues = TauCeti.principalTangents (TauCeti.approximateSubspace X) U →
                        δ * N.toFun tanTheta0 ≤ N.toFun (TauCeti.ritzResidual A X)
~~~~

`TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) (T : E →L[ℝ] E),
  IsSelfAdjoint T →
    ∀ (V Z : Submodule ℝ E) [inst_3 : V.HasOrthogonalProjection] [inst_4 : Z.HasOrthogonalProjection] (hV : T.Reduces V)
      {beta alpha delta : ℝ},
      beta ≤ alpha →
        0 < delta →
          spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal Z T) ⊆ Set.Icc beta alpha →
            spectrum ℝ (T.restrict ⋯) ⊆ Set.Ici (alpha + delta) →
              N.Mem (TauCeti.DavisKahan1970.theorem63ResidualReal T Z) →
                ∃ tanTheta0,
                  TauCeti.DavisKahan1970.HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
                    N.Mem tanTheta0 ∧
                      delta * N.gauge tanTheta0 ≤ N.gauge (TauCeti.DavisKahan1970.theorem63ResidualReal T Z)
~~~~

`TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E] {T A : E →L[ℂ] E}
  {U V : Submodule ℂ E} [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm),
  (↑T).IsSymmetric →
    IsSelfAdjoint A →
      T.Reduces V →
        (∀ x ∈ U, A x ∈ U) →
          ∀ {alpha delta : ℝ},
            0 < delta →
              (∀ (z : ↥U),
                  RCLike.re (inner ℂ ((TauCeti.DavisKahan.ExactTanTheta.theorem63Compression T U) z) z) ≤
                    alpha * ‖z‖ ^ 2) →
                (∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (T y) y)) →
                  TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent U V →
                    N.Mem (T - A) →
                      N.Mem (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) ∧
                        delta * N.gauge (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) ≤ N.gauge (T - A)
~~~~

`TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A T : E →L[ℝ] E} {U V : Submodule ℝ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection],
  IsSelfAdjoint T →
    IsSelfAdjoint A →
      T.Reduces V →
        (∀ x ∈ U, A x ∈ U) →
          ∀ {alpha delta : ℝ},
            0 < delta →
              (∀ (z : ↥U), inner ℝ ((TauCeti.DavisKahan1970.compressOperatorReal U T) z) z ≤ alpha * ‖z‖ ^ 2) →
                (∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (T y) y) →
                  TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent U V →
                    N.Mem (T - A) →
                      N.Mem (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) ∧
                        delta * N.gauge (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) ≤ N.gauge (T - A)
~~~~

`TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_real_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_real_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] {U V : Submodule ℝ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) (A : TauCeti.DavisKahanExt.ClosedOperator)
  (D : TauCeti.DavisKahan.TanTheta.UnboundedTrialBlock A U) (H : E →L[ℝ] E),
  IsSelfAdjoint H →
    ∀ {alpha delta : ℝ},
      0 < delta →
        ∀ (hVdom : ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain),
          (∀ (x : ↥A.domain), Vᗮ.starProjection (A.toLinearMap x) = A.toLinearMap ⟨Vᗮ.starProjection ↑x, ⋯⟩) →
            (∀ (z : ↥U), inner ℝ (D.operator z) z ≤ alpha * ‖z‖ ^ 2) →
              (∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (A.toLinearMap ⟨y, hy⟩) y) →
                TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent U V →
                  D.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL →
                    N.Mem H →
                      N.Mem (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) ∧
                        delta * N.gauge (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) ≤ N.gauge H
~~~~

`TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {U V : Submodule ℂ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (D : TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData U) (A : TauCeti.DavisKahan.DKClosedOperator)
  (H : E →L[ℂ] E),
  IsSelfAdjoint H →
    ∀ {alpha delta : ℝ},
      0 < delta →
        ∀ (hZA : ∀ (z : ↥D.compression.domain), ↑↑z ∈ A.domain),
          (∀ (z : ↥D.compression.domain), D.action z = A.toLinearMap ⟨↑↑z, ⋯⟩) →
            ∀ (hVdom : ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain),
              (∀ (x : ↥A.domain), Vᗮ.starProjection (A.toLinearMap x) = A.toLinearMap ⟨Vᗮ.starProjection ↑x, ⋯⟩) →
                TauCeti.DavisKahan.ExactSinTheta.SemiboundedAbove D.compression alpha →
                  (∀ y ∈ Vᗮ,
                      ∀ (hy : y ∈ A.domain),
                        (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re (inner ℂ (A.toLinearMap ⟨y, hy⟩) y)) →
                    TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent U V →
                      D.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL →
                        N.Mem H →
                          N.Mem (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) ∧
                            delta * N.gauge (TauCeti.DavisKahanExt.paperTanAngleOperatorC U V) ≤ N.gauge H
~~~~

`TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_real_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_real_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] {U V : Submodule ℝ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm)
  (D : TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData U) (A : TauCeti.DavisKahanExt.ClosedOperator)
  (H : E →L[ℝ] E),
  IsSelfAdjoint H →
    ∀ {alpha delta : ℝ},
      0 < delta →
        ∀ (hZA : ∀ (z : ↥D.compression.domain), ↑↑z ∈ A.domain),
          (∀ (z : ↥D.compression.domain), D.action z = A.toLinearMap ⟨↑↑z, ⋯⟩) →
            ∀ (hVdom : ∀ (x : ↥A.domain), Vᗮ.starProjection ↑x ∈ A.domain),
              (∀ (x : ↥A.domain), Vᗮ.starProjection (A.toLinearMap x) = A.toLinearMap ⟨Vᗮ.starProjection ↑x, ⋯⟩) →
                TauCeti.DavisKahan.ExactSinTheta.SemiboundedAbove D.compression alpha →
                  (∀ y ∈ Vᗮ, ∀ (hy : y ∈ A.domain), (alpha + delta) * ‖y‖ ^ 2 ≤ inner ℝ (A.toLinearMap ⟨y, hy⟩) y) →
                    TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent U V →
                      D.residual = Uᗮ.starProjection ∘SL H ∘SL U.subtypeL →
                        N.Mem H →
                          N.Mem (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) ∧
                            delta * N.gauge (TauCeti.DavisKahanExt.paperTanAngleOperatorR U V) ≤ N.gauge H
~~~~

</details>

**Maintainer note:** The directed residual half now has a scalar-generic, PaperUnitaryInvariantNorm, source-shaped canonical theorem whose public signature exposes the Ritz spectral placement instead of TanThetaIntervalGap. The harder ambient/unbounded half remains represented by the accepted source-shaped complex theorem plus its real companion because the current whole-space angle-operator implementation is field-specific.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

### Davis--Kahan double-angle sin 2 theta theorem

Review priority: `headline`

**Source anchor:** Section 2, sin 2 theta theorem

The Section 2 sin(2 theta) theorem: interval/exterior separation gives directed residual and ambient perturbation bounds with factor two.

**Normalized source statement**

*Setup:*

- Lambda0 and Lambda1 are the exact/perturbed diagonal blocks used by the paper, R is the residual, H is the perturbation, and Theta0/Theta are directed/ambient angles.

*Hypotheses:*

- For beta<=alpha and delta>0, spec(Lambda0) is contained in [beta,alpha] and spec(Lambda1) avoids (beta-delta,alpha+delta).

*Conclusion:*

- delta * ||sin(2 Theta0)|| <= 2 ||R||.
- delta * ||sin(2 Theta)|| <= 2 ||H||.

*Scope:*

- Arbitrary source unitary-invariant norm; real/complex and infinite-dimensional scope, with the maintained unbounded directed-residual extension.

**Canonical compiler-resolved Lean statement(s)**

`TauCeti.DavisKahan1970.sinTwoTheta_headline_generic_directed`

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_headline_generic_directed : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E F : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E]
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

`TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E] {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm),
  IsSelfAdjoint A →
    IsSelfAdjoint B →
      A.Reduces U →
        B.Reduces V →
          ∀ {a b d : ℝ},
            0 < d →
              a ≤ b →
                spectrum ℝ (TauCeti.DavisKahanExt.compressOperator U A) ⊆ Set.Icc a b →
                  (∀ x ∈ spectrum ℝ (TauCeti.DavisKahanExt.compressOperator Uᗮ A), x ≤ a - d ∨ b + d ≤ x) →
                    N.Mem (B - A) →
                      N.Mem (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC U V) ∧
                        d * N.gauge (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC U V) ≤ 2 * N.gauge (B - A)
~~~~

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The literal source unitary-invariant norm. The new directed headline theorem evaluates it over generic RCLike scalars.

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

`TauCeti.DavisKahanTheory.sinTwoThetaEmbedding` — The rectangular directed sin(2 Theta0) representative used by the scalar-generic headline theorem.

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

`TauCeti.DavisKahanTheory.residual` — The literal residual A X - X M appearing on the right-hand side of the directed theorem.

> **UNRESOLVED DEFINITION:** build/semantic-review-qry9vrso.lean:127:7: error(lean.unknownIdentifier): Unknown constant `TauCeti.DavisKahanTheory.residual`

`TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC` — The complex whole-space sin(2 Theta) operator used by the ambient perturbation scope companion.

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

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The scalar field is real or complex. | The canonical directed theorem quantifies over 𝕜 with [RCLike 𝕜] and uses PaperUnitaryInvariantNorm directly. | `claimed_exact` |
| Interval/exterior spectral separation by delta. | hCompressionSpectrum places M in [beta,alpha] and hUnwantedSpectrum literally places the unwanted A-spectrum outside (beta-delta,alpha+delta); no local gap structure is visible in the headline type. | `claimed_exact` |
| delta \|\|sin(2 Theta0)\|\| <= 2 \|\|R\|\|. | sinTwoTheta_headline_generic_directed concludes the factor-two PaperUnitaryInvariantNorm estimate for sinTwoThetaEmbedding U X against residual A X M. | `claimed_exact` |
| delta \|\|sin(2 Theta)\|\| <= 2 \|\|H\|\|. | sinTwoTheta_wholeSpace_paperUINorm supplies the ambient source endpoint, with the real whole-space theorem compiler-checked as a scalar companion. | `scope_companion` |
| Infinite-dimensional and unbounded directed-residual scope. | The generic headline facade is finite-dimensional; the real and complex unbounded directed-residual theorems remain explicit supporting declarations and carry the full source scope. | `scope_companion` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.DavisKahan1970.sinTwoTheta_directedResidual_paperUINorm`

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_directedResidual_paperUINorm : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : E →L[ℂ] E},
  IsSelfAdjoint A →
    ∀ {U V : Submodule ℂ E} [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection],
      A.Reduces U →
        ∀ {a b d : ℝ},
          0 < d →
            a ≤ b →
              spectrum ℝ (TauCeti.DavisKahanExt.compressOperator U A) ⊆ Set.Icc a b →
                (∀ x ∈ spectrum ℝ (TauCeti.DavisKahanExt.compressOperator Uᗮ A), x ≤ a - d ∨ b + d ≤ x) →
                  ∀ (M : ↥V →L[ℂ] ↥V),
                    N.Mem (TauCeti.DavisKahan.residual A V.subtypeL M) →
                      N.Mem (TauCeti.DavisKahan.sinTwoThetaIdealBlock U V) ∧
                        d * N.gauge (TauCeti.DavisKahan.sinTwoThetaIdealBlock U V) ≤
                          2 * N.gauge (TauCeti.DavisKahan.residual A V.subtypeL M)
~~~~

`TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] {A B : E →L[ℝ] E} {U V : Submodule ℝ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm),
  IsSelfAdjoint A →
    IsSelfAdjoint B →
      A.Reduces U →
        B.Reduces V →
          ∀ {a b d : ℝ},
            0 < d →
              a ≤ b →
                spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal U A) ⊆ Set.Icc a b →
                  (∀ x ∈ spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal Uᗮ A), x ≤ a - d ∨ b + d ≤ x) →
                    N.Mem (B - A) →
                      N.Mem (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorR U V) ∧
                        d * N.gauge (TauCeti.DavisKahanExt.paperSinTwoAngleOperatorR U V) ≤ 2 * N.gauge (B - A)
~~~~

`TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm`

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm : ∀ {H : Type u_1}
  [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] [inst_2 : CompleteSpace H] {V : Submodule ℂ H}
  [inst_3 : V.HasOrthogonalProjection] {M : ↥V →L[ℂ] ↥V} {R : ↥V →L[ℂ] H} {A : TauCeti.DavisKahan.DKClosedOperator}
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm)
  (hA : TauCeti.DavisKahanExt.ClosedOperator.IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)
  (hVdom : ∀ (v : ↥V), ↑v ∈ A.domain),
  (∀ (v : ↥V), A.toLinearMap ⟨↑v, ⋯⟩ = R v + ↑(M v)) →
    ∀ {β α δ : ℝ},
      β ≤ α →
        0 < δ →
          TauCeti.DavisKahan.ExactSinTheta.SemiboundedBelow
              (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB) β →
            TauCeti.DavisKahan.ExactSinTheta.SemiboundedAbove
                (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA B hB) α →
              (∀ lam ∈ Set.Ioo (β - δ) (α + δ),
                  ↑lam ∉
                    TauCeti.LinearPMap.spectrum
                      (TauCeti.DavisKahanExt.ClosedOperator.toLinearPMap
                        (TauCeti.DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ ⋯))) →
                N.Mem R →
                  N.Mem
                      (TauCeti.DavisKahan.sinTwoThetaIdealBlock
                        (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) V) ∧
                    δ *
                        N.gauge
                          (TauCeti.DavisKahan.sinTwoThetaIdealBlock
                            (TauCeti.DavisKahan.selfAdjointSpectralSubspace A hA B hB) V) ≤
                      2 * N.gauge R
~~~~

`TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm_real`

~~~~lean
@TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm_real : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] {V : Submodule ℝ E}
  [inst_3 : V.HasOrthogonalProjection] {M : ↥V →L[ℝ] ↥V} {R : ↥V →L[ℝ] E} {A : TauCeti.DavisKahanExt.ClosedOperator}
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) (hA : A.IsSelfAdjoint) (B : Set ℝ)
  (hB : MeasurableSet B) (hVdom : ∀ (v : ↥V), ↑v ∈ A.domain),
  (∀ (v : ↥V), A.toLinearMap ⟨↑v, ⋯⟩ = R v + ↑(M v)) →
    ∀ {δ : ℝ},
      0 < δ →
        TauCeti.DavisKahan.ExactSinTheta.FormBoundedSylvesterGap
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA B hB)
            (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralRestriction A hA Bᶜ ⋯) δ →
          N.Mem R →
            N.Mem
                (TauCeti.DavisKahan.sinTwoThetaIdealBlock
                  (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) V) ∧
              δ *
                  N.gauge
                    (TauCeti.DavisKahan.sinTwoThetaIdealBlock
                      (TauCeti.DavisKahan.RealSpectralRestriction.realSelfAdjointSpectralSubspace A hA B hB) V) ≤
                2 * N.gauge R
~~~~

</details>

**Maintainer note:** The directed residual conclusion now has a scalar-generic PaperUnitaryInvariantNorm facade with the interval/exterior hypotheses and residual written directly in its type. The ambient whole-space endpoint remains field-specific internally, so the complex source-shaped theorem stays as the second canonical declaration and its real sibling is a supporting scalar companion.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

### Davis--Kahan double-angle tan 2 theta theorem

Review priority: `headline`

**Source anchor:** Section 2, tan 2 theta theorem

The Section 2 tan(2 theta) theorem: an ordered gap and a fully off-diagonal perturbation give the directed residual and ambient perturbation bounds with factor two, without a separately assumed tangent-pole exclusion.

**Normalized source statement**

*Setup:*

- A0 and A1 are the two diagonal blocks of A, H0 and H1 are the diagonal perturbation blocks, R is the residual, H is the perturbation, and Theta0/Theta are directed/ambient angles.

*Hypotheses:*

- spec(A0) is contained in [beta,alpha], spec(A1) is contained in [alpha+delta,infinity), and delta>0.
- H0=H1=0 (the perturbation is fully off diagonal).
- No independent hypothesis excluding poles of tan(2 Theta), and no separate spectral placement of the perturbed Lambda blocks, is part of the printed theorem.

*Conclusion:*

- delta * ||tan(2 Theta0)|| <= 2 ||R||.
- delta * ||tan(2 Theta)|| <= 2 ||H||.

*Scope:*

- Arbitrary source unitary-invariant norm, with real/complex and unbounded ambient companions.

**Canonical compiler-resolved Lean statement(s)**

`TauCeti.DavisKahan1970.tanTwoTheta_headline_generic`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_headline_generic : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E}
  [FiniteDimensional 𝕜 ↥U] {a b : ℝ},
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

`TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection] {β α δ : ℝ},
  IsSelfAdjoint A →
    IsSelfAdjoint H →
      (∀ x ∈ U, A x ∈ U) →
        (∀ x ∈ V, (A + H) x ∈ V) →
          0 < δ →
            spectrum ℝ (TauCeti.DavisKahanExt.compressOperator U A) ⊆ Set.Icc β α →
              spectrum ℝ (TauCeti.DavisKahanExt.compressOperator Uᗮ A) ⊆ Set.Ici (α + δ) →
                (∀ x ∈ U, H x ∈ Uᗮ) →
                  (∀ x ∈ Uᗮ, H x ∈ U) →
                    N.Mem (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) →
                      N.Mem
                          (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U
                            (2 *
                              (TauCeti.DavisKahan1970.paperProjectorDifference U V *
                                TauCeti.DavisKahan1970.paperDoubleSecant U V))) ∧
                        δ *
                            N.gauge
                              (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U
                                (2 *
                                  (TauCeti.DavisKahan1970.paperProjectorDifference U V *
                                    TauCeti.DavisKahan1970.paperDoubleSecant U V))) ≤
                          2 * N.gauge (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H)
~~~~

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The literal source unitary-invariant norm; tanTwoTheta_headline_generic is already generic over RCLike 𝕜 at this norm scope.

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

`TauCeti.DavisKahanTheory.absDoubleAngleTangent` — The branch-free scalar function 2 t / |1-t^2| applied to graph-coordinate singular values; this is the generic theorem’s representation of |tan(2 Theta)|.

~~~~lean
def TauCeti.DavisKahanTheory.absDoubleAngleTangent : ℝ → ℝ :=
fun t => 2 * t / |1 - t ^ 2|
~~~~

`TauCeti.approximationSingularValue` — The approximation-number singular-value sequence used to express the branch-free tangent representative in arbitrary Hilbert space.

> **UNRESOLVED DEFINITION:** build/semantic-review-qry9vrso.lean:175:7: error(lean.unknownIdentifier): Unknown constant `TauCeti.approximationSingularValue`

`TauCeti.DavisKahan1970.paperDoubleSecant` — The source-shaped U,V directed-corner implementation used by the second canonical theorem; its invertibility is derived internally rather than assumed.

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

`TauCeti.DavisKahan1970.paperProjectorDifference` — The projector-difference factor used to build the source-shaped directed tan(2 Theta0) representative.

~~~~lean
def TauCeti.DavisKahan1970.paperProjectorDifference.{v} : {E : Type v} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      (U V : Submodule ℂ E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → E →L[ℂ] E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℂ E] U V [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  V.starProjection - U.starProjection
~~~~

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The scalar field is real or complex. | tanTwoTheta_headline_generic is an alias of the already proved branch-free theorem quantified over 𝕜 with [RCLike 𝕜] and the literal PaperUnitaryInvariantNorm. | `claimed_exact` |
| A has an ordered block gap and H is fully off diagonal. | The generic theorem writes the form bounds hUb/hUa and the two literal off-diagonal mapping hypotheses hHU/hHUperp directly; no named gap or oddness predicate hides them. | `claimed_exact` |
| The perturbed invariant subspace is arbitrary and no independent tan(2 Theta) pole hypothesis is assumed. | The generic theorem describes the invariant perturbed graph by hTmem, hTzero and hinv and uses the branch-free absDoubleAngleTangent singular values; it has no T<1, IsQuarterAcute, or cos(2 theta) premise. | `claimed_exact` |
| delta \|\|tan(2 Theta)\|\| <= 2 \|\|H\|\|. | With delta = b-a, tanTwoTheta_headline_generic concludes (b-a) * N.gauge tanTwoTheta <= 2 * N.gauge H for every source norm. | `claimed_exact` |
| delta \|\|tan(2 Theta0)\|\| <= 2 \|\|R\|\| in the source-shaped U,V corner notation. | The second canonical declaration gives the literal compression-spectrum/off-diagonal directed-corner theorem with no caller-supplied pole certificate. | `claimed_exact` |
| Infinite-dimensional/unbounded scope. | The generic branch-free canonical theorem removes ambient finite-dimensionality but still assumes a finite-dimensional graph base U; the full arbitrary-dimensional and unbounded real/complex endpoints remain compiler-checked supporting declarations. | `scope_companion` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A H : E →L[ℝ] E} {U V : Submodule ℝ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection] {β α δ : ℝ},
  IsSelfAdjoint A →
    IsSelfAdjoint H →
      (∀ x ∈ U, A x ∈ U) →
        (∀ x ∈ V, (A + H) x ∈ V) →
          0 < δ →
            spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal U A) ⊆ Set.Icc β α →
              spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal Uᗮ A) ⊆ Set.Ici (α + δ) →
                (∀ x ∈ U, H x ∈ Uᗮ) →
                  (∀ x ∈ Uᗮ, H x ∈ U) →
                    N.Mem (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H) →
                      N.Mem (TauCeti.DavisKahan1970.paperTanTwoDirectedCornerR U V) ∧
                        δ * N.gauge (TauCeti.DavisKahan1970.paperTanTwoDirectedCornerR U V) ≤
                          2 * N.gauge (TauCeti.DavisKahan.ExactSinTheta.paperProjectionBlock Uᗮ U H)
~~~~

`TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection] {β α δ : ℝ},
  IsSelfAdjoint A →
    IsSelfAdjoint H →
      (∀ x ∈ U, A x ∈ U) →
        (∀ x ∈ V, (A + H) x ∈ V) →
          0 < δ →
            spectrum ℝ (TauCeti.DavisKahanExt.compressOperator U A) ⊆ Set.Icc β α →
              spectrum ℝ (TauCeti.DavisKahanExt.compressOperator Uᗮ A) ⊆ Set.Ici (α + δ) →
                (∀ x ∈ U, H x ∈ Uᗮ) →
                  (∀ x ∈ Uᗮ, H x ∈ U) →
                    N.Mem H →
                      N.Mem (TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC U V) ∧
                        δ * N.gauge (TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H
~~~~

`TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] {A H : E →L[ℝ] E} {U V : Submodule ℝ E}
  [inst_3 : U.HasOrthogonalProjection] [inst_4 : V.HasOrthogonalProjection]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {β α δ : ℝ},
  IsSelfAdjoint A →
    IsSelfAdjoint H →
      (∀ x ∈ U, A x ∈ U) →
        (∀ x ∈ V, (A + H) x ∈ V) →
          0 < δ →
            spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal U A) ⊆ Set.Icc β α →
              spectrum ℝ (TauCeti.DavisKahan1970.compressOperatorReal Uᗮ A) ⊆ Set.Ici (α + δ) →
                (∀ x ∈ U, H x ∈ Uᗮ) →
                  (∀ x ∈ Uᗮ, H x ∈ U) →
                    N.Mem H →
                      N.Mem (TauCeti.DavisKahanExt.paperTanTwoAngleOperatorR U V) ∧
                        δ * N.gauge (TauCeti.DavisKahanExt.paperTanTwoAngleOperatorR U V) ≤ 2 * N.gauge H
~~~~

`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact : ∀ {G : Type u_1}
  [inst : NormedAddCommGroup G] [inst_1 : InnerProductSpace ℂ G] [inst_2 : CompleteSpace G]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
  (hA : IsSelfAdjoint A),
  TauCeti.IsOddFor (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B →
    IsSelfAdjoint Z →
      Z * Z = 1 →
        ∀ (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z),
          (∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x)) →
            (∀ (x : ↥A.domain),
                ↑x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯ → RCLike.re (inner ℂ (↑A x) ↑x) ≤ a * ‖↑x‖ ^ 2) →
              (∀ (x : ↥A.domain),
                  ↑x ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ →
                    b * ‖↑x‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A x) ↑x)) →
                a < b →
                  N.Mem
                      (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression
                        (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)
                        B) →
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
                              (TauCeti.DavisKahan.ExactSinTheta.paperBlockCompression
                                (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ
                                (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B)
~~~~

`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E} {a b c : ℝ}
  (hA : IsSelfAdjoint A),
  TauCeti.IsOddFor (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B →
    IsSelfAdjoint Z →
      Z * Z = 1 →
        ∀ (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z),
          (∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x)) →
            (∀ (x : ↥A.domain),
                ↑x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯ → inner ℝ (↑A x) ↑x ≤ a * ‖↑x‖ ^ 2) →
              (∀ (x : ↥A.domain),
                  ↑x ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯)ᗮ → b * ‖↑x‖ ^ 2 ≤ inner ℝ (↑A x) ↑x) →
                a < b →
                  N.Mem
                      (TauCeti.DavisKahan1970.reflectionResidualCorner
                        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B) →
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

`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact : ∀ {G : Type u_1} [inst : NormedAddCommGroup G]
  [inst_1 : InnerProductSpace ℂ G] [inst_2 : CompleteSpace G]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
  (hA : IsSelfAdjoint A),
  IsSelfAdjoint B →
    TauCeti.IsOddFor (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) B →
      IsSelfAdjoint Z →
        Z * Z = 1 →
          ∀ (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z),
            (∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x)) →
              (∀ (x : ↥A.domain),
                  ↑x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯ → RCLike.re (inner ℂ (↑A x) ↑x) ≤ a * ‖↑x‖ ^ 2) →
                (∀ (x : ↥A.domain),
                    ↑x ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯)ᗮ →
                      b * ‖↑x‖ ^ 2 ≤ RCLike.re (inner ℂ (↑A x) ↑x)) →
                  a < b →
                    N.Mem B →
                      IsUnit
                          ((TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯).diagonalPart Z *
                            (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯).diagonalPart Z) ∧
                        N.Mem
                            (TauCeti.DavisKahan1970.unboundedReflectionTangent
                              (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) Z) ∧
                          (b - a) *
                              N.gauge
                                (TauCeti.DavisKahan1970.unboundedReflectionTangent
                                  (TauCeti.LinearPMap.specRange hA (Set.Iic c) ⋯) Z) ≤
                            2 * N.gauge B
~~~~

`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact`

~~~~lean
@TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E]
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm) {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E} {a b c : ℝ}
  (hA : IsSelfAdjoint A),
  IsSelfAdjoint B →
    TauCeti.IsOddFor (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) B →
      IsSelfAdjoint Z →
        Z * Z = 1 →
          ∀ (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z),
            (∀ (x : ↥A.domain), ↑A ⟨Z ↑x, ⋯⟩ + B (Z ↑x) = Z (↑A x) + Z (B ↑x)) →
              (∀ (x : ↥A.domain),
                  ↑x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯ → inner ℝ (↑A x) ↑x ≤ a * ‖↑x‖ ^ 2) →
                (∀ (x : ↥A.domain),
                    ↑x ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯)ᗮ → b * ‖↑x‖ ^ 2 ≤ inner ℝ (↑A x) ↑x) →
                  a < b →
                    N.Mem B →
                      IsUnit
                          ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯).diagonalPart Z *
                            (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯).diagonalPart Z) ∧
                        N.Mem
                            (TauCeti.DavisKahan1970.unboundedReflectionTangent
                              (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) Z) ∧
                          (b - a) *
                              N.gauge
                                (TauCeti.DavisKahan1970.unboundedReflectionTangent
                                  (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) ⋯) Z) ≤
                            2 * N.gauge B
~~~~

</details>

**Maintainer note:** Unlike tan Theta and sin 2Theta, the branch-free tan 2Theta paper-norm theorem was already scalar-generic. The review now promotes it to the canonical headline name. Its generic proof is necessarily graph-coordinate shaped, so the source-shaped U,V directed-corner theorem remains canonical alongside it and the report prints absDoubleAngleTangent/approximationSingularValue context explicitly.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

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

- The headline packet uses the source-shaped consecutive-block theorem; the library also proves an RCLike generalization.

**Canonical compiler-resolved Lean statement(s)**

`TauCeti.yuWangSamworth_sinTheta_block_le`

~~~~lean
@TauCeti.yuWangSamworth_sinTheta_block_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
  {hA : A.IsSymmetric} {hB : B.IsSymmetric} {n d r s : ℕ} {hn : Module.finrank 𝕜 E = n} (hsn : s + 1 ≤ n)
  (hd : r + d = s + 1) {u v : Fin d → E},
  TauCeti.IsOrderedEigenframe hA hn (TauCeti.consecutiveEmb ⋯) u →
    TauCeti.IsOrderedEigenframe hB hn (TauCeti.consecutiveEmb ⋯) v →
      ∀ {Δ : ℝ},
        0 < Δ →
          TauCeti.OrderedBlockBoundaryGap hA hn r s Δ →
            TauCeti.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u)) (Submodule.span 𝕜 (Set.range v)) ≤
              2 *
                  min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                    ((TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (B - A)) /
                Δ
~~~~

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.OrderedBlockBoundaryGap` — The literal two population boundary gaps around the consecutive block r,...,s; it contains no sample-gap condition.

~~~~lean
def TauCeti.OrderedBlockBoundaryGap.{u_1, u_2} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {n : ℕ} → {T : E →ₗ[𝕜] E} → T.IsSymmetric → Module.finrank 𝕜 E = n → ℕ → ℕ → ℝ → Prop :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n} {T} hT hn r s Δ =>
  (∀ (q p : Fin n), ↑q + 1 = r → ↑p = r → Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p) ∧
    ∀ (q p : Fin n), ↑q = s → ↑p = s + 1 → Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p
~~~~

`TauCeti.IsOrderedEigenframe` — Says the supplied frame consists of orthonormal eigenvectors at the specified positions in the sorted eigenvalue list.

~~~~lean
def TauCeti.IsOrderedEigenframe.{u_1, u_2} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {n d : ℕ} →
              {T : E →ₗ[𝕜] E} → T.IsSymmetric → Module.finrank 𝕜 E = n → (Fin d ↪ Fin n) → (Fin d → E) → Prop :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n d} {T} hT hn e w =>
  TauCeti.IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w
~~~~

`TauCeti.consecutiveEmb` — The index embedding selecting exactly the consecutive positions r,...,s.

~~~~lean
def TauCeti.consecutiveEmb : {n d r : ℕ} → r + d ≤ n → Fin d ↪ Fin n :=
fun {n d r} h => { toFun := fun i => ⟨r + ↑i, ⋯⟩, inj' := ⋯ }
~~~~

`TauCeti.sinThetaFrobenius` — The Frobenius norm of the sine/cross-projection operator between the two subspaces.

~~~~lean
def TauCeti.sinThetaFrobenius.{u_1, u_2} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            (U V : Submodule 𝕜 E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → ℝ :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] U V
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  (TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (TauCeti.sinThetaMap U V)
~~~~

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| The block is the consecutive ordered indices r,...,s and d=s-r+1. | hd : r + d = s + 1 and consecutiveEmb (hd.trans_le hsn) select precisely those indices (0-based Lean indexing). | `claimed_exact` |
| Only the population exterior gaps enter Delta. | hgap : OrderedBlockBoundaryGap hA hn r s Delta; its printed #print contains only eigenvalues of A (the population operator), never B. | `claimed_exact` |
| V and V-hat are eigenvector blocks at the same ordered indices. | hu/hv : IsOrderedEigenframe ... (consecutiveEmb ...) u/v. | `claimed_exact` |
| No sample eigengap. | There is no gap predicate involving hB/B in the canonical theorem type. | `claimed_exact` |
| Frobenius sine bound with min(sqrt(d)\|\|E\|\|op,\|\|E\|\|F) and constant 2. | The conclusion of yuWangSamworth_sinTheta_block_le is literal up to A/B notation for Sigma/Sigma-hat. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.yuWangSamworth_sinTheta_le`

~~~~lean
@TauCeti.yuWangSamworth_sinTheta_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
  (hB : B.IsSymmetric) {U V : Submodule 𝕜 E} [inst_4 : U.HasOrthogonalProjection] [inst_5 : V.HasOrthogonalProjection],
  TauCeti.IsInvariant A U →
    TauCeti.IsInvariant B V →
      TauCeti.CorrespondingEigenblock hA hB U V →
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

**Maintainer note:** The canonical declaration is the consecutive-block wrapper, not the more abstract CorrespondingEigenblock theorem, so the reviewer sees the paper indices and population boundary gap directly.

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

- The canonical review declaration is the real-matrix statement so O-hat appears literally as a matrix in the orthogonal group.

**Canonical compiler-resolved Lean statement(s)**

`TauCeti.yuWangSamworth_alignedFrame_block_real_le`

~~~~lean
@TauCeti.yuWangSamworth_alignedFrame_block_real_le : ∀ {F : Type u_1} [inst : NormedAddCommGroup F]
  [inst_1 : InnerProductSpace ℝ F] [inst_2 : FiniteDimensional ℝ F] {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric}
  {hB : B.IsSymmetric} {n d r s : ℕ} {hn : Module.finrank ℝ F = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
  {u v : Fin d → F},
  TauCeti.IsOrderedEigenframe hA hn (TauCeti.consecutiveEmb ⋯) u →
    TauCeti.IsOrderedEigenframe hB hn (TauCeti.consecutiveEmb ⋯) v →
      ∀ {Δ : ℝ},
        0 < Δ →
          TauCeti.OrderedBlockBoundaryGap hA hn r s Δ →
            ∃ O ∈ Matrix.orthogonalGroup (Fin d) ℝ,
              √(∑ i, ‖∑ j, O j i • v j - u i‖ ^ 2) ≤
                2 * √2 *
                    min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                      ((TauCeti.UnitarilyInvariantSeminorm.frobenius ℝ F).toFun (B - A)) /
                  Δ
~~~~

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.OrderedBlockBoundaryGap` — The two population boundary gaps and no sample gap.

~~~~lean
def TauCeti.OrderedBlockBoundaryGap.{u_1, u_2} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {n : ℕ} → {T : E →ₗ[𝕜] E} → T.IsSymmetric → Module.finrank 𝕜 E = n → ℕ → ℕ → ℝ → Prop :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n} {T} hT hn r s Δ =>
  (∀ (q p : Fin n), ↑q + 1 = r → ↑p = r → Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p) ∧
    ∀ (q p : Fin n), ↑q = s → ↑p = s + 1 → Δ ≤ hT.eigenvalues hn q - hT.eigenvalues hn p
~~~~

`TauCeti.IsOrderedEigenframe` — The supplied population and sample frames at the same sorted consecutive indices.

~~~~lean
def TauCeti.IsOrderedEigenframe.{u_1, u_2} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {n d : ℕ} →
              {T : E →ₗ[𝕜] E} → T.IsSymmetric → Module.finrank 𝕜 E = n → (Fin d ↪ Fin n) → (Fin d → E) → Prop :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n d} {T} hT hn e w =>
  TauCeti.IsEigenFamily T (fun i => hT.eigenvalues hn (e i)) w
~~~~

`TauCeti.consecutiveEmb` — The consecutive block r,...,s.

~~~~lean
def TauCeti.consecutiveEmb : {n d r : ℕ} → r + d ≤ n → Fin d ↪ Fin n :=
fun {n d r} h => { toFun := fun i => ⟨r + ↑i, ⋯⟩, inj' := ⋯ }
~~~~

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| Same population-only gap and consecutive eigenvector blocks as the first conclusion. | The canonical theorem repeats the same hd, hu, hv, hDelta and OrderedBlockBoundaryGap hypotheses. | `claimed_exact` |
| There exists O-hat in O(d). | The conclusion existentially returns O : Matrix (Fin d) (Fin d) R with O in Matrix.orthogonalGroup. | `claimed_exact` |
| V-hat O-hat is compared to the supplied V, not to a reselected population basis. | The left side is sqrt(sum_i \|\|sum_j O j i • v j - u i\|\|^2), with u and v exactly the supplied frames from the hypotheses. | `claimed_exact` |
| Constant 2^(3/2) and the same min numerator. | The conclusion is 2 * sqrt 2 * min(sqrt d * \|\|B-A\|\|op, \|\|B-A\|\|F) / Delta. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

`TauCeti.yuWangSamworth_alignedFrame_block_le`

~~~~lean
@TauCeti.yuWangSamworth_alignedFrame_block_le : ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2}
  [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
  {hA : A.IsSymmetric} {hB : B.IsSymmetric} {n d r s : ℕ} {hn : Module.finrank 𝕜 E = n} (hsn : s + 1 ≤ n)
  (hd : r + d = s + 1) {u v : Fin d → E},
  TauCeti.IsOrderedEigenframe hA hn (TauCeti.consecutiveEmb ⋯) u →
    ∀ (hv : TauCeti.IsOrderedEigenframe hB hn (TauCeti.consecutiveEmb ⋯) v) {Δ : ℝ},
      0 < Δ →
        TauCeti.OrderedBlockBoundaryGap hA hn r s Δ →
          ∃ O,
            (∀ (x y : EuclideanSpace 𝕜 (Fin d)), inner 𝕜 (O x) (O y) = inner 𝕜 x y) ∧
              √(∑ i, ‖TauCeti.frameComp ⋯ O i - u i‖ ^ 2) ≤
                2 * √2 *
                    min (√↑d * ‖LinearMap.toContinuousLinearMap (B - A)‖)
                      ((TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E).toFun (B - A)) /
                  Δ
~~~~

</details>

**Maintainer note:** Using the real source-shaped wrapper makes every symbol in the printed aligned-frame conclusion visible in the theorem type.

**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`

- Verdict: _fill in_
- Hidden or stronger Lean hypothesis, if any: _fill in_
- Missing or weakened conclusion, if any: _fill in_
- Is every project-local notion needed to judge the theorem expanded above? _fill in_
- Suggested replacement theorem/context, if needed: _fill in_

---

## Scope intentionally omitted

Rows marked `major`, `supporting`, or `technical` are excluded from the default `headline` packet. Use `--importance major` for the broader tier. The exhaustive paper censuses remain the authority for full-paper coverage.
