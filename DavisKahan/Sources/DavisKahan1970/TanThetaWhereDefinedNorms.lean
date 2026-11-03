/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (exact configuration undetermined)
-/
module
public import DavisKahan.Sources.DavisKahan1970.Ideals.WhereDefinedNormTransfer
public import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbient
public import DavisKahan.Sources.DavisKahan1970.TanThetaUnboundedAmbientReal
public import DavisKahan.Sources.DavisKahan1970.TanThetaDirectedUnbounded
public import DavisKahan.Sources.DavisKahan1970.DirectedTrigonometricPresentation

/-!
# Unbounded tangent estimates with where-defined norms

The directed tangent representative and pole exclusion are constructed independently
of the norm family. Comparisons require both displayed norms to exist, and do not
transfer ideal membership. The ambient statements retain bounded definedness of
the ambient tangent, as required by the source's norm convention.
-/
public section
namespace TauCeti.DavisKahan1970
open TauCeti TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Angle TauCeti.DavisKahan.Sylvester
open TauCeti.DavisKahan.TanTheta
open scoped InnerProductSpace
attribute [local instance] Submodule.completeSpace_coe_of_hasOrthogonalProjection
noncomputable section
universe u v

section Ambientcomplex
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
/-- The ambient tangent comparison where both norms exist. -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, u} ℂ)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hdefined : HasDefinedAmbientTangent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL) :
    N.Mem (tanAngleOperatorC U V) → N.Mem H →
      delta * N.gaugeReal (tanAngleOperatorC U V) ≤ N.gaugeReal H := by
  exact whereDefinedUIN_of_normalizedUnitaryInvariant N hdelta
    (X := (tanAngleOperatorC U V)) (Y := H) fun M hM =>
      tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_complex M D hV H hH
        hdelta hupper hUnwanted hdefined hResidual hM
end Ambientcomplex

section Directedcomplex
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Directed tangent representative and comparison, without norm-domain solidity. -/
theorem tanTheta_directed_unboundedRitz_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (R : Z →L[ℂ] H) (hR : D.trial.residual = R) :
    (∀ n, ((theorem63DirectedSineBlock Z V).singularValue n : ℝ) < 1) ∧
      ∃ tanTheta0 : Z →L[ℂ] H,
        HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.ScaledGaugeLEWhereDefined delta tanTheta0 R := by
  subst hR
  have hlt := approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex
    D hV hdelta hupper hUnwanted
  obtain ⟨tanTheta0, htan⟩ := exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V hlt
  refine ⟨hlt, tanTheta0, htan, ?_⟩
  exact whereDefinedUIN_of_symmetricNorming N hdelta fun M hM =>
    tanTheta_directed_unboundedRitz_symmetricNorming_complex M D hV
      hdelta hupper hUnwanted tanTheta0 htan hM
/-- The comparison holds for every representative with the prescribed singular sequence. -/
theorem tanTheta_directed_unboundedRitz_representative_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (R : Z →L[ℂ] H) (hR : D.trial.residual = R)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0) :
    N.ScaledGaugeLEWhereDefined delta tanTheta0 R := by
  subst hR
  exact whereDefinedUIN_of_symmetricNorming N hdelta fun M hM =>
    tanTheta_directed_unboundedRitz_symmetricNorming_complex M D hV
      hdelta hupper hUnwanted tanTheta0 htan hM
end Directedcomplex

section Ambientreal
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
/-- The ambient tangent comparison where both norms exist. -/
theorem tanTheta_ambient_unboundedRitz_definedTangent_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E}
    (D : DavisKahan.UnboundedRitzPair A U)
    (hV : DavisKahan.ReducingComplement A V)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hdefined : HasDefinedAmbientTangentReal U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL) :
    N.Mem (tanAngleOperatorR U V) → N.Mem H →
      delta * N.gaugeReal (tanAngleOperatorR U V) ≤ N.gaugeReal H := by
  exact whereDefinedUIN_of_normalizedUnitaryInvariant N hdelta
    (X := (tanAngleOperatorR U V)) (Y := H) fun M hM =>
      tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_real M D hV H hH
        hdelta hupper hUnwanted hdefined hResidual hM
end Ambientreal

section Directedreal
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- Directed tangent representative and comparison, without norm-domain solidity. -/
theorem tanTheta_directed_unboundedRitz_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (R : Z →L[ℝ] E) (hR : D.trial.residual = R) :
    (∀ n, ((theorem63DirectedSineBlockReal Z V).singularValue n : ℝ) < 1) ∧
      ∃ tanTheta0 : Z →L[ℝ] E,
        HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
        N.ScaledGaugeLEWhereDefined delta tanTheta0 R := by
  subst hR
  have hlt := approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_real
    D hV hdelta hupper hUnwanted
  obtain ⟨tanTheta0, htan⟩ := exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V hlt
  refine ⟨hlt, tanTheta0, htan, ?_⟩
  exact whereDefinedUIN_of_symmetricNorming N hdelta fun M hM =>
    tanTheta_directed_unboundedRitz_symmetricNorming_real M D hV
      hdelta hupper hUnwanted tanTheta0 htan hM
/-- The comparison holds for every representative with the prescribed singular sequence. -/
theorem tanTheta_directed_unboundedRitz_representative_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (R : Z →L[ℝ] E) (hR : D.trial.residual = R)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0) :
    N.ScaledGaugeLEWhereDefined delta tanTheta0 R := by
  subst hR
  exact whereDefinedUIN_of_symmetricNorming N hdelta fun M hM =>
    tanTheta_directed_unboundedRitz_symmetricNorming_real M D hV
      hdelta hupper hUnwanted tanTheta0 htan hM
end Directedreal

/-- Literal directed tangent on the original carrier, with no norm-membership transfer. -/
theorem tanTheta_directed_unboundedRitz_presentation_whereDefinedUIN_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {A : E →ₗ.[ℂ] E} {Z V : Submodule ℂ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (R : Z →L[ℂ] E) (hR : D.trial.residual = R) :
    (∀ n, ((TanTheta.directedSineBlock Z V).singularValue n : ℝ) < 1) ∧
      N.ScaledGaugeLEWhereDefined delta (sourceDirectedTanThetaOperator Z V) R := by
  subst hR
  obtain ⟨hpole, -, -⟩ :=
    tanTheta_directed_unboundedRitz_symmetricNorming_presentation_complex
      (kyFanNormingFunction 1 one_pos) D hV hdelta hupper hUnwanted
      (kyFanNormingFunction_mem 1 one_pos _)
  refine ⟨hpole, ?_⟩
  apply whereDefinedUIN_of_symmetricNorming N hdelta
  intro M hM
  obtain ⟨-, hmem, hbound⟩ :=
    tanTheta_directed_unboundedRitz_symmetricNorming_presentation_complex
      M D hV hdelta hupper hUnwanted hM
  exact ⟨hmem, hbound⟩

/-- Literal directed tangent on the original carrier, with no norm-membership transfer. -/
theorem tanTheta_directed_unboundedRitz_presentation_whereDefinedUIN_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E} {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (R : Z →L[ℝ] E) (hR : D.trial.residual = R) :
    (∀ n, ((TanTheta.directedSineBlock Z V).singularValue n : ℝ) < 1) ∧
      N.ScaledGaugeLEWhereDefined delta (sourceDirectedTanThetaOperator Z V) R := by
  subst hR
  obtain ⟨hpole, -, -⟩ :=
    tanTheta_directed_unboundedRitz_symmetricNorming_presentation_real
      (kyFanNormingFunction 1 one_pos) D hV hdelta hupper hUnwanted
      (kyFanNormingFunction_mem 1 one_pos _)
  refine ⟨hpole, ?_⟩
  apply whereDefinedUIN_of_symmetricNorming N hdelta
  intro M hM
  obtain ⟨-, hmem, hbound⟩ :=
    tanTheta_directed_unboundedRitz_symmetricNorming_presentation_real
      M D hV hdelta hupper hUnwanted hM
  exact ⟨hmem, hbound⟩

end
end TauCeti.DavisKahan1970
