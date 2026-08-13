# Semantic alignment review: headline mathematical statements

Generated: `2026-08-13T16:10:06+00:00`
Repository commit: `7e485601f8ef5237fc762c1a5789ddd8fa75d58f`
Working tree clean: `yes`
Importance threshold: `headline`
Papers: Davis--Kahan 1970, Yu--Wang--Samworth 2015
Compiler semantic probe run: `yes`
Compiler probe exit code: `0`

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

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily` — The scalar-generic ideal/norm family used by the natural-input sine theorem; its gauge is the quantity written as a unitary-invariant norm.

~~~~lean
structure TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily.{u, v} (𝕜 : Type u) [RCLike 𝕜] :
  Type (max u (v + 1))
number of parameters: 2
fields:
  TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily.toSymmetricOperatorIdealFamily : TauCeti.SymmetricOperatorIdealFamily
      𝕜
  TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily.isComplete : self.toSymmetricOperatorIdealFamily.IsComplete
  TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily.gauge_le_of_forall_kyFanApproximationGauge_le : ∀
      {E F : Type v} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace 𝕜 E] [inst_2 : CompleteSpace E]
      [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] [inst_5 : CompleteSpace F] {A B : E →L[𝕜] F},
      (∀ (k : ℕ),
          TauCeti.ApproximationNumber.kyFanApproximationGauge k A ≤
            TauCeti.ApproximationNumber.kyFanApproximationGauge k B) →
        self.toSymmetricOperatorIdealFamily.gauge A ≤ self.toSymmetricOperatorIdealFamily.gauge B
constructor:
  TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily.mk.{u, v} {𝕜 : Type u} [RCLike 𝕜]
    (toSymmetricOperatorIdealFamily : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    (isComplete : toSymmetricOperatorIdealFamily.IsComplete)
    (gauge_le_of_forall_kyFanApproximationGauge_le :
      ∀ {E F : Type v} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace 𝕜 E] [inst_2 : CompleteSpace E]
        [inst_3 : NormedAddCommGroup F] [inst_4 : InnerProductSpace 𝕜 F] [inst_5 : CompleteSpace F] {A B : E →L[𝕜] F},
        (∀ (k : ℕ),
            TauCeti.ApproximationNumber.kyFanApproximationGauge k A ≤
              TauCeti.ApproximationNumber.kyFanApproximationGauge k B) →
          toSymmetricOperatorIdealFamily.gauge A ≤ toSymmetricOperatorIdealFamily.gauge B) :
    TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily 𝕜
~~~~

`TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap` — Exactly packages the three allowed spectral-separation configurations, including the interval/exterior hypothesis used in Section 2 and the two ordered half-line variants.

~~~~lean
inductive TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap.{v} : {E F : Type v} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      [inst_2 : NormedAddCommGroup F] →
        [inst_3 : InnerProductSpace ℂ F] →
          TauCeti.DavisKahanExt.ClosedOperator → TauCeti.DavisKahanExt.ClosedOperator → ℝ → Prop
number of parameters: 9
constructors:
TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap.intervalExterior : ∀ {E F : Type v} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℂ E] [inst_2 : NormedAddCommGroup F] [inst_3 : InnerProductSpace ℂ F]
  {A : TauCeti.DavisKahanExt.ClosedOperator} {B : TauCeti.DavisKahanExt.ClosedOperator} {δ β α : ℝ},
  β ≤ α →
    TauCeti.DavisKahan.ExactSinTheta.SpectralIntervalExteriorGap A B β α δ →
      TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap A B δ
TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap.leftAboveRightBelow : ∀ {E F : Type v}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E] [inst_2 : NormedAddCommGroup F]
  [inst_3 : InnerProductSpace ℂ F] {A : TauCeti.DavisKahanExt.ClosedOperator} {B : TauCeti.DavisKahanExt.ClosedOperator}
  {δ : ℝ} (c : ℝ),
  Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆ Set.Ici (c + δ) →
    Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B.toLinearPMap ⊆ Set.Iic c →
      TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap A B δ
TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap.leftBelowRightAbove : ∀ {E F : Type v}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℂ E] [inst_2 : NormedAddCommGroup F]
  [inst_3 : InnerProductSpace ℂ F] {A : TauCeti.DavisKahanExt.ClosedOperator} {B : TauCeti.DavisKahanExt.ClosedOperator}
  {δ : ℝ} (c : ℝ),
  Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap ⊆ Set.Iic c →
    Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum B.toLinearPMap ⊆ Set.Ici (c + δ) →
      TauCeti.DavisKahan.ExactSinTheta.SpectralSylvesterGap A B δ
~~~~

`TauCeti.DavisKahan.ExactSinTheta.generalResidual` — The residual A X - X A0 appearing on the right side of the theorem.

~~~~lean
def TauCeti.DavisKahan.ExactSinTheta.generalResidual.{u, v} : {𝕜 : Type u} →
  [inst : RCLike 𝕜] →
    {E F : Type v} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [inst_3 : NormedAddCommGroup F] →
            [inst_4 : InnerProductSpace 𝕜 F] → (E →L[𝕜] E) → (F →L[𝕜] E) → (F →L[𝕜] F) → F →L[𝕜] E :=
fun {𝕜} [RCLike 𝕜] {E F} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] A
    X A₀ =>
  A ∘SL X - X ∘SL A₀
~~~~

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| A0 is self-adjoint and the exact complementary block Lambda1 is self-adjoint. | The canonical theorem takes self-adjoint closed operators A0 and A and constructs the complementary self-adjoint spectral restriction of A internally. | `claimed_exact` |
| Interval/exterior separation by delta, allowing the two spectral roles to be interchanged. | hgap : SpectralSylvesterGap A0 (selfAdjointSpectralRestriction A ... Sᶜ ...) delta; the printed #print of SpectralSylvesterGap exposes its intervalExterior constructor and both ordered alternatives. | `claimed_exact` |
| R = A X - X A0. | hReq states the residual identity pointwise on the domain, with Rop the bounded residual operator. | `claimed_exact` |
| delta \|\|sin Theta0\|\| <= \|\|R\|\|. | The conclusion is delta * N.gauge ((I - E E*) X) <= N.gauge Rop; for an isometric trial map this operator carries the directed sine singular values. | `claimed_exact` |
| Infinite-dimensional/unbounded scope. | The canonical declaration is the unbounded closed-operator spectral-subspace theorem; bounded and real companions are separately compiler-checked below. | `scope_companion` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

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

`TauCeti.DavisKahan1970.sinTheta_real_exactPaper`

~~~~lean
@TauCeti.DavisKahan1970.sinTheta_real_exactPaper : ∀ {E F G H : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : NormedAddCommGroup F]
  [inst_4 : InnerProductSpace ℝ F] [inst_5 : CompleteSpace F] [inst_6 : NormedAddCommGroup G]
  [inst_7 : InnerProductSpace ℝ G] [inst_8 : CompleteSpace G] [inst_9 : NormedAddCommGroup H]
  [inst_10 : InnerProductSpace ℝ H] [inst_11 : CompleteSpace H] {E₀ F₀ : Type u_1} [inst_12 : NormedAddCommGroup E₀]
  [inst_13 : InnerProductSpace ℝ E₀] [inst_14 : CompleteSpace E₀] [inst_15 : NormedAddCommGroup F₀]
  [inst_16 : InnerProductSpace ℝ F₀] [inst_17 : CompleteSpace F₀]
  (P : TauCeti.DavisKahan.ExactSinTheta.PaperRealIsometricTheoremData)
  (S : TauCeti.DavisKahan.ExactSinTheta.PaperSinThetaRepresentativeAcross P.canonicalSinTheta)
  (N : TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm),
  N.Mem P.data.residual → N.Mem S.operator ∧ P.gap * N.gauge S.operator ≤ N.gauge P.data.residual
~~~~

</details>

**Maintainer note:** The primary review theorem uses natural spectral inputs instead of the older bundled FormBoundedIsometricSinThetaProblem, specifically so that the hypothesis surface is visible to an external reviewer.

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

`TauCeti.DavisKahanTheory.TanThetaIntervalGap` — The one-sided spectral hypothesis: the Ritz compression lies in [beta,alpha] and the unwanted exact spectrum lies in [alpha+delta,infinity).

~~~~lean
def TauCeti.DavisKahanTheory.TanThetaIntervalGap.{u_1, u_2, u_3} : {𝕜 : Type u_1} →
  [inst : RCLike 𝕜] →
    {E : Type u_2} →
      [inst_1 : NormedAddCommGroup E] →
        [inst_2 : InnerProductSpace 𝕜 E] →
          [FiniteDimensional 𝕜 E] →
            {F : Type u_3} →
              [inst_4 : NormedAddCommGroup F] →
                [inst_5 : InnerProductSpace 𝕜 F] →
                  [FiniteDimensional 𝕜 F] →
                    (E →ₗ[𝕜] E) → (U : Submodule 𝕜 E) → [U.HasOrthogonalProjection] → (F →ₗᵢ[𝕜] E) → ℝ → ℝ → ℝ → Prop :=
fun {𝕜} [RCLike 𝕜] {E} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {F} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] A U [U.HasOrthogonalProjection] X β α δ =>
  TauCeti.SpectrumIn (TauCeti.compression A X) ⊤ (Set.Icc β α) ∧ TauCeti.SpectrumIn A Uᗮ (Set.Ici (α + δ))
~~~~

`TauCeti.DavisKahan.Frontier.CrossedDefectsEquivalent` — The standing nonacute direct-rotation existence condition: the two crossed defect spaces are unitarily isomorphic.

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

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The paper-faithful arbitrary unitary-invariant norm used by the infinite-dimensional ambient theorem.

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

`TauCeti.DavisKahanExt.paperTanAngleOperatorC` — The canonical ambient tan(Theta) operator whose approximation singular values are the tangents of the principal angles.

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
| spec(A0) subset [beta,alpha] and unwanted exact spectrum subset [alpha+delta,infinity). | TanThetaIntervalGap unfolds to exactly those two spectral containments for the directed theorem. | `claimed_exact` |
| H0=0 / Rayleigh--Ritz choice. | The canonical directed theorem is stated directly for ritzResidual A X, i.e. the off-diagonal residual of the Rayleigh--Ritz compression. | `claimed_exact` |
| delta \|\|tan Theta0\|\| <= \|\|R\|\|. | The first canonical declaration concludes delta * N.toFun tanTheta0 <= N.toFun (ritzResidual A X), with tanTheta0 constrained to have the principal tangent singular values. | `claimed_exact` |
| delta \|\|tan Theta\|\| <= \|\|H\|\|. | The second canonical declaration concludes delta * N.gauge (paperTanAngleOperatorC U V) <= N.gauge H. | `claimed_exact` |
| No separately assumed tangent-pole exclusion in the printed theorem. | The finite directed theorem derives transversality from TanThetaIntervalGap; the ambient unbounded theorem instead exposes the paper-wide crossed-defect/direct-rotation existence condition. | `claimed_exact` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

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

</details>

**Maintainer note:** Two canonical declarations are shown because the printed theorem has two genuinely different conclusions: a directed residual estimate and an ambient perturbation estimate.

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

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The source-faithful arbitrary unitary-invariant norm used for the paper endpoint.

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

`TauCeti.DavisKahan.sinTwoThetaIdealBlock` — The directed doubled-angle block; its singular-value sequence represents sin(2 Theta0).

~~~~lean
def TauCeti.DavisKahan.sinTwoThetaIdealBlock.{u, v} : {𝕜 : Type u} →
  [inst : RCLike 𝕜] →
    {H : Type v} →
      [inst_1 : NormedAddCommGroup H] →
        [inst_2 : InnerProductSpace 𝕜 H] →
          (U V : Submodule 𝕜 H) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → H →L[𝕜] H :=
fun {𝕜} [RCLike 𝕜] {H} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] U V [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] =>
  U.starProjection ∘SL (Submodule.map (↑V.reflection.toLinearEquiv) Uᗮ).starProjection
~~~~

`TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC` — The ambient doubled-angle sine operator representing sin(2 Theta).

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
| Interval/exterior spectral separation by delta. | Both canonical declarations state the selected spectrum in [a,b] and the complementary spectrum outside (a-d,b+d). | `claimed_exact` |
| delta \|\|sin(2 Theta0)\|\| <= 2 \|\|R\|\|. | sinTwoTheta_directedResidual_paperUINorm concludes d * N.gauge (sinTwoThetaIdealBlock U V) <= 2 * N.gauge residual. | `claimed_exact` |
| delta \|\|sin(2 Theta)\|\| <= 2 \|\|H\|\|. | sinTwoTheta_wholeSpace_paperUINorm concludes the factor-two perturbation estimate for paperSinTwoAngleOperatorC. | `claimed_exact` |
| Real/infinite/unbounded scope. | Real whole-space and real/complex unbounded directed-residual companions are compiler-checked below. | `scope_companion` |

<details>
<summary><strong>Supporting scope declarations</strong></summary>

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

**Maintainer note:** The canonical surface shows one declaration for each printed conclusion rather than mixing them with the later unequal-dimension and helper variants.

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

**Local semantic dictionary**

These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.

`TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — The source-faithful arbitrary unitary-invariant norm used in the paper endpoint.

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

`TauCeti.DavisKahan1970.paperDoubleSecant` — The secant factor used to realize the absolute tangent of twice the principal angle without introducing a source-extraneous pole hypothesis.

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

`TauCeti.DavisKahan1970.paperProjectorDifference` — The projector-difference operator used to build the ambient/direct doubled-angle tangent representative.

~~~~lean
def TauCeti.DavisKahan1970.paperProjectorDifference.{v} : {E : Type v} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℂ E] →
      (U V : Submodule ℂ E) → [U.HasOrthogonalProjection] → [V.HasOrthogonalProjection] → E →L[ℂ] E :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℂ E] U V [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] =>
  V.starProjection - U.starProjection
~~~~

`TauCeti.DavisKahan1970.unboundedReflectionTangent` — The unbounded ambient reflection/tangent representative used in the source-scope endpoint.

~~~~lean
def TauCeti.DavisKahan1970.unboundedReflectionTangent.{u_2, u_3} : {𝕜 : Type u_2} →
  [inst : RCLike 𝕜] →
    {G : Type u_3} →
      [inst_1 : NormedAddCommGroup G] →
        [inst_2 : InnerProductSpace 𝕜 G] →
          (U : Submodule 𝕜 G) → [U.HasOrthogonalProjection] → (G →L[𝕜] G) → G →L[𝕜] G :=
fun {𝕜} [RCLike 𝕜] {G} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] U [U.HasOrthogonalProjection] Z =>
  U.offDiagonalPart Z * Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) * U.diagonalPart Z
~~~~

**Clause-by-clause alignment claim**

| Source clause | Lean realization | Status |
|---|---|---|
| Ordered gap: A0 below A1 by delta. | The directed canonical theorem states the U-compression spectrum in [beta,alpha] and the U^perp compression spectrum in [alpha+delta,infinity). | `claimed_exact` |
| H0=H1=0. | The directed theorem has the two literal off-diagonal mapping assumptions H(U) subset U^perp and H(U^perp) subset U; the unbounded theorem uses IsOddFor the spectral splitting. | `claimed_exact` |
| No independent tan(2 Theta) pole hypothesis. | The canonical directed theorem has no transversality/invertibility premise; the needed secant invertibility is obtained internally. The unbounded ambient theorem returns IsUnit as part of its conclusion before the tangent estimate. | `claimed_exact` |
| delta \|\|tan(2 Theta0)\|\| <= 2 \|\|R\|\|. | The directed canonical theorem concludes the factor-two gauge estimate for the directed corner representative. | `claimed_exact` |
| delta \|\|tan(2 Theta)\|\| <= 2 \|\|H\|\|. | The unbounded ambient canonical theorem concludes (b-a) * gauge(unboundedReflectionTangent) <= 2 * gauge(B). | `claimed_exact` |

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

</details>

**Maintainer note:** The packet deliberately prints the local doubled-angle tangent representatives so the reviewer can inspect that no hidden pole/separation hypothesis has been smuggled into their definitions.

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
