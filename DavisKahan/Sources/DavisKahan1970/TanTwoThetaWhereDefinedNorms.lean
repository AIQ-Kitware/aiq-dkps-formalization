/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (exact configuration undetermined)
-/
module
public import DavisKahan.Sources.DavisKahan1970.Ideals.WhereDefinedNormTransfer
public import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedAmbientExact
public import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExactReal
public import DavisKahan.Sources.DavisKahan1970.DirectedTrigonometricPresentation

/-!
# Double-angle tangent estimates with where-defined norms

Pole exclusion and the directed singular-value correspondence are retained. The
norm comparison asks for exactly the two displayed operators to belong to the
normalized symmetric family. The literal directed presentations use the original
scalar carrier, including real norm families on real operators. A separate real
configuration/complexified-operator API retains its precise transport statement
under one complex norm family.
-/
public section
namespace TauCeti.DavisKahan1970
open TauCeti TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Angle TauCeti.DavisKahan.Sylvester
open TauCeti.RealComplexification TauCeti.DavisKahan.Foundation.RealComplexification
open scoped InnerProductSpace
attribute [local instance] Submodule.completeSpace_coe_of_hasOrthogonalProjection
noncomputable section
universe u v

section ambientcomplex
variable {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]
/-- The ambient double-angle tangent comparison where both norms exist. -/
theorem tanTwoTheta_ambient_unbounded_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace G]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, u} ℂ)
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
    (hab : a < b) :
    (∀ t ∈ spectrum ℝ (TauCeti.DavisKahan.Angle.angleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V),
        Real.cos (2 * t) ≠ 0) ∧
      (N.Mem (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) → N.Mem B →
      (b - a) * N.gaugeReal (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gaugeReal B) := by
  obtain ⟨hcos, -, -⟩ :=
    tanTwoTheta_ambient_unbounded_normalizedUIN_complex (kyFanNormalizedUnitaryInvariantNorm 1 one_pos)
    V hA hBsa hB hV hUa hUb hab (mem_kyFanNormalizedUnitaryInvariantNorm 1 one_pos _)
  refine ⟨hcos, ?_⟩
  exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N (sub_pos.mpr hab) two_pos
    (X := (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V)) (Y := B) fun M hM => by
      obtain ⟨-, hm, hl⟩ :=
        tanTwoTheta_ambient_unbounded_normalizedUIN_complex M V hA hBsa hB hV hUa hUb hab hM
      exact ⟨hm, hl⟩
end ambientcomplex

section directedcomplex
variable {Ea : Type*} [NormedAddCommGroup Ea] [InnerProductSpace ℂ Ea] [CompleteSpace Ea]
variable (U V : Submodule ℂ Ea) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
/-- The directed double-angle tangent comparison where both norms exist. -/
theorem tanTwoTheta_directed_unboundedResidual_whereDefinedUIN_complex
    [TopologicalSpace.SeparableSpace Ea]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, _} ℂ)
    {A : Ea →ₗ.[ℂ] Ea} {B : Ea →L[ℂ] Ea} {a b : ℝ}
    (hA : IsSelfAdjoint A) (hred : _root_.LinearPMap.IsReducing A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : _root_.LinearPMap.IsReducing (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Ea) ∈ U →
      RCLike.re ⟪A x, (x : Ea)⟫_ℂ ≤ a * ‖(x : Ea)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Ea) ∈ Uᗮ →
      b * ‖(x : Ea)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Ea)⟫_ℂ)
    (hab : a < b) :
    (∀ n : ℕ, ((DavisKahan.sinTwoThetaIdealBlock U V).singularValue n : ℝ) < 1) ∧
      (∀ n : ℕ,
        ((projectionBlock Uᗮ U
            (2 * (projectorDifference U V * doubleSecant U V))).singularValue n : ℝ) =
          Real.tan (Real.arcsin
            (((DavisKahan.sinTwoThetaIdealBlock U V).singularValue n : ℝ)))) ∧
      (N.Mem (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V))) →
        N.Mem (projectionBlock Uᗮ U B) →
      (b - a) * N.gaugeReal
          (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V))) ≤
        2 * N.gaugeReal (projectionBlock Uᗮ U B)) := by
  obtain ⟨hpole, htan, -, -⟩ :=
    tanTwoTheta_directed_unboundedResidual_normalizedUIN_complex U V
    (kyFanNormalizedUnitaryInvariantNorm 1 one_pos) hA hred hB hV hUa hUb hab
    (mem_kyFanNormalizedUnitaryInvariantNorm 1 one_pos _)
  refine ⟨hpole, htan, ?_⟩
  exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N (sub_pos.mpr hab) two_pos
    (X :=
      (projectionBlock Uᗮ U (2 * (projectorDifference U V * doubleSecant U V)))) (Y := (projectionBlock
      Uᗮ U B)) fun M hM => by
      obtain ⟨-, -, hm, hl⟩ :=
        tanTwoTheta_directed_unboundedResidual_normalizedUIN_complex U V M hA hred hB hV hUa hUb hab hM
      exact ⟨hm, hl⟩
end directedcomplex

section ambientreal
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
/-- The ambient double-angle tangent comparison where both norms exist. -/
theorem tanTwoTheta_ambient_unbounded_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, u} ℝ)
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
    (hab : a < b) :
    (∀ t ∈ spectrum ℝ (TauCeti.DavisKahan.Angle.angleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V),
        Real.cos (2 * t) ≠ 0) ∧
      (N.Mem (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V) → N.Mem B →
      (b - a) * N.gaugeReal (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gaugeReal B) := by
  obtain ⟨hcos, -, -⟩ :=
    tanTwoTheta_ambient_unbounded_normalizedUIN_real (kyFanNormalizedUnitaryInvariantNorm 1 one_pos) V
    hA hBsa hB hV hUa hUb hab (mem_kyFanNormalizedUnitaryInvariantNorm 1 one_pos _)
  refine ⟨hcos, ?_⟩
  exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N (sub_pos.mpr hab) two_pos
    (X := (TauCeti.DavisKahan.Angle.absTanTwoAngleOperatorR
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) V)) (Y := B) fun M hM => by
      obtain ⟨-, hm, hl⟩ := tanTwoTheta_ambient_unbounded_normalizedUIN_real M V hA hBsa hB hV hUa hUb hab hM
      exact ⟨hm, hl⟩
end ambientreal

section directedreal
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {A : E →ₗ.[ℝ] E} {B : E →L[ℝ] E} {a b : ℝ}
/-- The directed double-angle tangent comparison where both norms exist. -/
theorem tanTwoTheta_directed_unboundedResidual_whereDefinedUIN_real
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, _} ℂ)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hA : _root_.IsSelfAdjoint A)
    (hred : _root_.LinearPMap.IsReducing A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : _root_.LinearPMap.IsReducing (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U → ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ → b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) :
    (∀ n : ℕ, ((DavisKahan.sinTwoThetaIdealBlock U V).singularValue n : ℝ) < 1) ∧
      (∀ n : ℕ,
        ((tanTwoDirectedCornerR U V).singularValue n : ℝ) =
          Real.tan (Real.arcsin
            (((DavisKahan.sinTwoThetaIdealBlock U V).singularValue n : ℝ)))) ∧
      (N.Mem (tanTwoDirectedCornerR U V) → N.Mem (complexify (projectionBlock Uᗮ U B)) →
      (b - a) * N.gaugeReal (tanTwoDirectedCornerR U V) ≤
        2 * N.gaugeReal (complexify (projectionBlock Uᗮ U B))) := by
  obtain ⟨hpole, htan, -, -⟩ :=
    tanTwoTheta_directed_unboundedResidual_normalizedUIN_real
      (kyFanNormalizedUnitaryInvariantNorm 1 one_pos) U V hA hred hB hV hUa hUb hab
      (mem_kyFanNormalizedUnitaryInvariantNorm 1 one_pos _)
  refine ⟨hpole, htan, ?_⟩
  exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N (sub_pos.mpr hab) two_pos
    (X := (tanTwoDirectedCornerR U V)) (Y := (complexify (projectionBlock Uᗮ U B))) fun M hM => by
      obtain ⟨-, -, hm, hl⟩ :=
        tanTwoTheta_directed_unboundedResidual_normalizedUIN_real M U V hA hred hB hV hUa hUb hab hM
      exact ⟨hm, hl⟩
end directedreal

/-- The directed doubled tangent on the original scalar carrier, with both norms defined. -/
theorem tanTwoTheta_directed_unboundedResidual_presentation_whereDefinedUIN_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {A : E →ₗ.[ℂ] E} {B : E →L[ℂ] E} {a b : ℝ}
    {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A) (hred : _root_.LinearPMap.IsReducing A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : _root_.LinearPMap.IsReducing (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hab : a < b) :
    (∀ n, ((DavisKahan.sinTwoThetaIdealBlock U V).singularValue n : ℝ) < 1) ∧
      (N.Mem (sourceDirectedTanTwoThetaOperator V U) →
        N.Mem (blockCompression Uᗮ U B) →
        (b - a) * N.gaugeReal (sourceDirectedTanTwoThetaOperator V U) ≤
          2 * N.gaugeReal (blockCompression Uᗮ U B)) := by
  obtain ⟨hpole, -, -⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_complex
      (kyFanNormingFunction 1 one_pos) V hA hred hB hV hUa hUb hab
      (kyFanNormingFunction_mem 1 one_pos _)
  refine ⟨hpole, ?_⟩
  apply whereDefinedUIN_of_symmetricNorming_mul N (sub_pos.mpr hab) two_pos
  intro M hM
  obtain ⟨-, hmem, hbound⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_complex
      M V hA hred hB hV hUa hUb hab hM
  exact ⟨hmem, hbound⟩

/-- The directed doubled tangent on the original scalar carrier, with both norms defined. -/
theorem tanTwoTheta_directed_unboundedResidual_presentation_whereDefinedUIN_real
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E} {B : E →L[ℝ] E} {a b : ℝ}
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A) (hred : _root_.LinearPMap.IsReducing A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : _root_.LinearPMap.IsReducing (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) :
    (∀ n, ((DavisKahan.sinTwoThetaIdealBlock U V).singularValue n : ℝ) < 1) ∧
      (N.Mem (sourceDirectedTanTwoThetaOperator V U) →
        N.Mem (blockCompression Uᗮ U B) →
        (b - a) * N.gaugeReal (sourceDirectedTanTwoThetaOperator V U) ≤
          2 * N.gaugeReal (blockCompression Uᗮ U B)) := by
  obtain ⟨hpole, -, -⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_real
      (kyFanNormingFunction 1 one_pos) V hA hred hB hV hUa hUb hab
      (kyFanNormingFunction_mem 1 one_pos _)
  refine ⟨hpole, ?_⟩
  apply whereDefinedUIN_of_symmetricNorming_mul N (sub_pos.mpr hab) two_pos
  intro M hM
  obtain ⟨-, hmem, hbound⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_real
      M V hA hred hB hV hUa hUb hab hM
  exact ⟨hmem, hbound⟩


end
end TauCeti.DavisKahan1970
