/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (exact configuration undetermined)
-/
module

public import DavisKahan.Sources.DavisKahan1970.Ideals.WhereDefinedNormTransfer
public import DavisKahan.Sources.DavisKahan1970.Section4DirectRotationSource
public import DavisKahan.Sources.DavisKahan1970.Section6SourceScope

/-!
# Sections 4–6 with where-defined unitary-invariant norms

The inequalities below use the normalized symmetric ideal family, without
unconditional Fan dominance or a conclusion transferring ideal membership.
Both displayed norms are required to exist. Operator and spectral hypotheses
are inherited from the unbounded analytic theorems.
-/

public section
namespace TauCeti.DavisKahan1970
open TauCeti TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Angle TauCeti.DavisKahan.Sylvester
open scoped InnerProductSpace
noncomputable section
universe u v

section Corollary41Complex
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
/-- Corollary 4.1 where both displayed ideal norms exist. -/
theorem corollary4_1_directRotation_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : H →L[ℂ] H) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    N.Mem ((1 - D) ∘L U.starProjection) → N.Mem ((1 - W) ∘L U.starProjection) →
      N.gaugeReal ((1 - D) ∘L U.starProjection) ≤
        N.gaugeReal ((1 - W) ∘L U.starProjection) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (one_pos)
    (X := ((1 - D) ∘L U.starProjection)) (Y := ((1 - W) ∘L U.starProjection)) fun M hM =>
      by simpa only [one_mul] using
        (corollary4_1_directRotation_sourceExact_complex M U V hcompact D hD W hWunitary hWmap hM)
  intro hX hY
  simpa only [one_mul] using h hX hY
end Corollary41Complex

section Proposition43Complex
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
/-- Proposition 4.3 where both displayed ideal norms exist. -/
theorem proposition4_3_directRotation_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : H →L[ℂ] H) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    N.Mem ((1 - star D) * (1 - D)) → N.Mem ((1 - star W) * (1 - W)) →
      N.gaugeReal ((1 - star D) * (1 - D)) ≤ N.gaugeReal ((1 - star W) * (1 - W)) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (one_pos)
    (X := ((1 - star D) * (1 - D))) (Y := ((1 - star W) * (1 - W))) fun M hM =>
      by simpa only [one_mul] using
        (proposition4_3_directRotation_sourceExact_complex M U V hcompact D hD W hWunitary hWmap hM)
  intro hX hY
  simpa only [one_mul] using h hX hY
end Proposition43Complex

section SylvesterComplex

/-- Theorem 5.2 where both displayed ideal norms exist. -/
theorem theorem5_2_whereDefinedUIN_complex
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : _root_.LinearPMap.SylvesterEquation A B X R) :
    N.Mem X → N.Mem R →
      δ * N.gaugeReal X ≤ N.gaugeReal R := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (hδ)
    (X := X) (Y := R) fun M hM =>
      theorem5_2_sourceExact_complex M hA hB hδ hAlow hBhigh hsyl hM
  exact h
end SylvesterComplex

section GeneralizedSineComplex

/-- Theorem 6.1 where both displayed ideal norms exist. -/
theorem theorem6_1_whereDefinedUIN_complex
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperator E₀ F₀ hframe hε)) :
    N.Mem S.operator → N.Mem R →
      δ * ε * N.gaugeReal S.operator ≤ N.gaugeReal R := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (mul_pos hδ hε)
    (X := S.operator) (Y := R) fun M hM =>
      theorem6_1_sourceExact_complex M A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hε hframe hδ hgap S hM
  exact h
end GeneralizedSineComplex

section Corollary41Real
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
/-- Corollary 4.1 where both displayed ideal norms exist. -/
theorem corollary4_1_directRotation_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : E →L[ℝ] E) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    N.Mem ((1 - D) ∘L U.starProjection) → N.Mem ((1 - W) ∘L U.starProjection) →
      N.gaugeReal ((1 - D) ∘L U.starProjection) ≤
        N.gaugeReal ((1 - W) ∘L U.starProjection) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (one_pos)
    (X := ((1 - D) ∘L U.starProjection)) (Y := ((1 - W) ∘L U.starProjection)) fun M hM =>
      by simpa only [one_mul] using
        (corollary4_1_directRotation_sourceExact_real M U V hcompact D hD W hWunitary hWmap hM)
  intro hX hY
  simpa only [one_mul] using h hX hY
end Corollary41Real

section Proposition43Real
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
/-- Proposition 4.3 where both displayed ideal norms exist. -/
theorem proposition4_3_directRotation_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : E →L[ℝ] E) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    N.Mem ((1 - star D) * (1 - D)) → N.Mem ((1 - star W) * (1 - W)) →
      N.gaugeReal ((1 - star D) * (1 - D)) ≤ N.gaugeReal ((1 - star W) * (1 - W)) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (one_pos)
    (X := ((1 - star D) * (1 - D))) (Y := ((1 - star W) * (1 - W))) fun M hM =>
      by simpa only [one_mul] using
        (proposition4_3_directRotation_sourceExact_real M U V hcompact D hD W hWunitary hWmap hM)
  intro hX hY
  simpa only [one_mul] using h hX hY
end Proposition43Real

section SylvesterReal

/-- Theorem 5.2 where both displayed ideal norms exist. -/
theorem theorem5_2_whereDefinedUIN_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : _root_.LinearPMap.SylvesterEquation A B X R) :
    N.Mem X → N.Mem R →
      δ * N.gaugeReal X ≤ N.gaugeReal R := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (hδ)
    (X := X) (Y := R) fun M hM =>
      theorem5_2_sourceExact_real M hA hB hδ hAlow hBhigh hsyl hM
  exact h
end SylvesterReal

section GeneralizedSineReal

/-- Theorem 6.1 where both displayed ideal norms exist. -/
theorem theorem6_1_whereDefinedUIN_real
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℝ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℝ F₀'] [CompleteSpace F₀']
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : DavisKahan.Sylvester.FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperatorReal E₀ F₀ hframe hε)) :
    N.Mem S.operator → N.Mem R →
      δ * ε * N.gaugeReal S.operator ≤ N.gaugeReal R := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (mul_pos hδ hε)
    (X := S.operator) (Y := R) fun M hM =>
      theorem6_1_sourceExact_real M A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hε hframe hδ hgap S hM
  exact h
end GeneralizedSineReal

section Pinching
variable {E : Type v}
/-- Lemma 6.2 where both displayed ideal norms exist. -/
theorem lemma6_2_whereDefinedUIN_rclike {𝕜 : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} 𝕜)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} :
    N.Mem (diagonalPair U V K) → N.Mem K →
      N.gaugeReal (diagonalPair U V K) ≤ N.gaugeReal K := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (one_pos)
    (X := (diagonalPair U V K)) (Y := K) fun M hM =>
      by simpa only [one_mul] using (lemma6_2_separable M U V hM)
  intro hX hY
  simpa only [one_mul] using h hX hY
end Pinching

section SymmetricSine

/-- Proposition 6.1 where both displayed ideal norms exist. -/
theorem proposition6_1_commonDomain_whereDefinedUIN_rclike
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} 𝕜)
    {A B : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : _root_.LinearPMap.IsReducing A U)
    (hV : _root_.LinearPMap.IsReducing B V)
    (Hop : E →L[𝕜] E) (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (A.restrict hU.isInvariant) (B.restrict hV.orthogonal.isInvariant) δ)
    (hgapVU : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (B.restrict hV.isInvariant) (A.restrict hU.orthogonal.isInvariant) δ) :
    N.Mem (DavisKahan.Angle.ambientSinThetaOperator U V) → N.Mem Hop →
      δ * N.gaugeReal (DavisKahan.Angle.ambientSinThetaOperator U V) ≤ N.gaugeReal Hop := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N (hδ)
    (X := (DavisKahan.Angle.ambientSinThetaOperator U V)) (Y := Hop) fun M hM =>
      proposition6_1_commonDomain_normalizedUIN_rclike M hA hB hU hV Hop hdomain
        hperturbation hδ hgapUV hgapVU hM
  exact h
end SymmetricSine

/-- Lemma 6.1: uniform where-defined block comparisons imply the sum comparison. -/
theorem lemma6_1_sourceOperators_whereDefinedUIN_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℂ] E)
    (h₀ : ∀ M : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ K) →
        M.Mem (projectionBlock Ω Γ L) →
        M.gaugeReal (projectionBlock Ω Γ K) ≤ M.gaugeReal (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      M.Mem (projectionBlock Ωᗮ Γᗮ K) →
        M.Mem (projectionBlock Ωᗮ Γᗮ L) →
        M.gaugeReal (projectionBlock Ωᗮ Γᗮ K) ≤ M.gaugeReal (projectionBlock Ωᗮ Γᗮ L)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) →
      N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) →
      N.gaugeReal (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
        N.gaugeReal (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N one_pos
    (X :=
      (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K)) (Y := (projectionBlock Ω Γ L + projectionBlock
      Ωᗮ Γᗮ L)) fun M hM => by
      obtain ⟨hm, hl⟩ := lemma6_1_sourceOperators_separable_complex M Ω Γ K L
        (fun S hS => normalizedUnitaryInvariant_le_of_all_whereDefinedUIN S h₀ hS)
        (fun S hS => normalizedUnitaryInvariant_le_of_all_whereDefinedUIN S h₁ hS) hM
      exact ⟨hm, by simpa only [one_mul] using hl⟩
  intro hK hL
  simpa only [one_mul] using h hK hL

/-- Lemma 6.1's converse, with uniform where-defined norm comparisons. -/
theorem lemma6_1_converse_sourceOperators_whereDefinedUIN_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (Ω Γ : Submodule ℂ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℂ] E)
    (hK : ContinuousLinearMap.SameSingularValues (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ K))
    (hL : ContinuousLinearMap.SameSingularValues (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ L))
    (hsum : ∀ M : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ,
      M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) →
        M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) →
        M.gaugeReal (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
        M.gaugeReal (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L)) :
    N.Mem (projectionBlock Ω Γ K) →
      N.Mem (projectionBlock Ω Γ L) →
      N.gaugeReal (projectionBlock Ω Γ K) ≤ N.gaugeReal (projectionBlock Ω Γ L) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N one_pos
    (X := (projectionBlock Ω Γ K)) (Y := (projectionBlock Ω Γ L)) fun M hM => by
      obtain ⟨hm, hl⟩ := lemma6_1_converse_sourceOperators_separable_complex M Ω Γ K L hK hL
        (fun S hS => normalizedUnitaryInvariant_le_of_all_whereDefinedUIN S hsum hS) hM
      exact ⟨hm, by simpa only [one_mul] using hl⟩
  intro hKmem hLmem
  simpa only [one_mul] using h hKmem hLmem

/-- Lemma 6.1: uniform where-defined block comparisons imply the sum comparison. -/
theorem lemma6_1_sourceOperators_whereDefinedUIN_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℝ] E)
    (h₀ : ∀ M : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ K) →
        M.Mem (projectionBlock Ω Γ L) →
        M.gaugeReal (projectionBlock Ω Γ K) ≤ M.gaugeReal (projectionBlock Ω Γ L))
    (h₁ : ∀ M : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ,
      M.Mem (projectionBlock Ωᗮ Γᗮ K) →
        M.Mem (projectionBlock Ωᗮ Γᗮ L) →
        M.gaugeReal (projectionBlock Ωᗮ Γᗮ K) ≤ M.gaugeReal (projectionBlock Ωᗮ Γᗮ L)) :
    N.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) →
      N.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) →
      N.gaugeReal (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
        N.gaugeReal (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N one_pos
    (X :=
      (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K)) (Y := (projectionBlock Ω Γ L + projectionBlock
      Ωᗮ Γᗮ L)) fun M hM => by
      obtain ⟨hm, hl⟩ := lemma6_1_sourceOperators_separable_real M Ω Γ K L
        (fun S hS => normalizedUnitaryInvariant_le_of_all_whereDefinedUIN S h₀ hS)
        (fun S hS => normalizedUnitaryInvariant_le_of_all_whereDefinedUIN S h₁ hS) hM
      exact ⟨hm, by simpa only [one_mul] using hl⟩
  intro hK hL
  simpa only [one_mul] using h hK hL

/-- Lemma 6.1's converse, with uniform where-defined norm comparisons. -/
theorem lemma6_1_converse_sourceOperators_whereDefinedUIN_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℝ] E)
    (hK : ContinuousLinearMap.SameSingularValues (projectionBlock Ω Γ K) (projectionBlock Ωᗮ Γᗮ K))
    (hL : ContinuousLinearMap.SameSingularValues (projectionBlock Ω Γ L) (projectionBlock Ωᗮ Γᗮ L))
    (hsum : ∀ M : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ,
      M.Mem (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) →
        M.Mem (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L) →
        M.gaugeReal (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K) ≤
        M.gaugeReal (projectionBlock Ω Γ L + projectionBlock Ωᗮ Γᗮ L)) :
    N.Mem (projectionBlock Ω Γ K) →
      N.Mem (projectionBlock Ω Γ L) →
      N.gaugeReal (projectionBlock Ω Γ K) ≤ N.gaugeReal (projectionBlock Ω Γ L) := by
  have h := whereDefinedUIN_of_normalizedUnitaryInvariant N one_pos
    (X := (projectionBlock Ω Γ K)) (Y := (projectionBlock Ω Γ L)) fun M hM => by
      obtain ⟨hm, hl⟩ := lemma6_1_converse_sourceOperators_separable_real M Ω Γ K L hK hL
        (fun S hS => normalizedUnitaryInvariant_le_of_all_whereDefinedUIN S hsum hS) hM
      exact ⟨hm, by simpa only [one_mul] using hl⟩
  intro hKmem hLmem
  simpa only [one_mul] using h hKmem hLmem

end
end TauCeti.DavisKahan1970
