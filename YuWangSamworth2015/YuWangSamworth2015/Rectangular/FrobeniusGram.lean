/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import YuWangSamworth2015.GroundedImports
public import TauCeti.Analysis.InnerProductSpace.Gram.Perturbation
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten

/-!
# Frobenius perturbation bounds for rectangular Gram operators

This module supplies the missing Frobenius branch in the rectangular
Yu--Wang--Samworth argument.  For `D = Â - A`, it proves

`‖Â⋆Â - A⋆A‖_F ≤ (‖Â‖ + ‖A‖) ‖D‖_F`

and the analogous left-Gram estimate. The proof consumes Tau Ceti's
cross-dimensional Schatten ideal law at `p = 2` and its Frobenius endpoint.
The left-Gram bound follows from the right-Gram bound for the adjoint, using
Tau Ceti's Schatten adjoint invariance. Both results hold over `RCLike`.
-/

public section

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Frobenius perturbation bound for the right Gram operator. -/
theorem frobenius_rightGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)
        ((Â.adjoint ∘ₗ Â) - (A.adjoint ∘ₗ A)) ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        UnitarilyInvariantSeminorm.frobenius 𝕜 E F (Â - A) := by
  let : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  let : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  let D : E →ₗ[𝕜] F := Â - A
  have hidentityCLM :=
    ContinuousLinearMap.adjoint_comp_self_sub_adjoint_comp_self
      Â.toContinuousLinearMap A.toContinuousLinearMap
  have hidentity :
      (Â.adjoint ∘ₗ Â) - (A.adjoint ∘ₗ A) =
        Â.adjoint ∘ₗ D + D.adjoint ∘ₗ A := by
    ext x
    have hx := congrArg (fun T : E →L[𝕜] E => T x) hidentityCLM
    simp [D]
  rw [hidentity]
  refine (map_add_le_add
    (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)) _ _).trans ?_
  have hleft :
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)
          (Â.adjoint ∘ₗ D) ≤
        ‖Â.toContinuousLinearMap‖ *
          UnitarilyInvariantSeminorm.frobenius 𝕜 E F D := by
    have h := UnitarilyInvariantSeminorm.schatten_comp_le_left 2 Â.adjoint D
      (fun y => Â.adjoint.toContinuousLinearMap.le_opNorm y)
    simpa only [UnitarilyInvariantSeminorm.schatten_two,
      LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map] using h
  have hright :
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (D.adjoint ∘ₗ A) ≤
        ‖A.toContinuousLinearMap‖ *
          UnitarilyInvariantSeminorm.frobenius 𝕜 E F D := by
    have h := UnitarilyInvariantSeminorm.schatten_comp_le_left 2 A.adjoint D
      (fun y => A.adjoint.toContinuousLinearMap.le_opNorm y)
    rw [← (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜)
        (E := E) (F := E)).map_eq_of_singularValues_eq
      (LinearMap.singularValues_adjoint (D.adjoint ∘ₗ A)), LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint]
    simpa only [UnitarilyInvariantSeminorm.schatten_two,
      LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map] using h
  calc
    UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (Â.adjoint ∘ₗ D) +
          UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (D.adjoint ∘ₗ A)
        ≤ ‖Â.toContinuousLinearMap‖ *
              UnitarilyInvariantSeminorm.frobenius 𝕜 E F D +
            ‖A.toContinuousLinearMap‖ *
              UnitarilyInvariantSeminorm.frobenius 𝕜 E F D :=
      add_le_add hleft hright
    _ = (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
          UnitarilyInvariantSeminorm.frobenius 𝕜 E F D := by ring

/-- Frobenius perturbation bound for the left Gram operator. -/
theorem frobenius_leftGram_sub_le
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := F)
        ((Â ∘ₗ Â.adjoint) - (A ∘ₗ A.adjoint)) ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        UnitarilyInvariantSeminorm.frobenius 𝕜 E F (Â - A) := by
  let : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  let : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  -- Left Gram is the right Gram of the adjoint.  Invariance of the
  -- rectangular Frobenius norm under adjoint gives the same coefficient.
  have h := frobenius_rightGram_sub_le A.adjoint Â.adjoint
  have hdiff :
      UnitarilyInvariantSeminorm.frobenius 𝕜 F E (Â.adjoint - A.adjoint) =
        UnitarilyInvariantSeminorm.frobenius 𝕜 E F (Â - A) := by
    have h := UnitarilyInvariantSeminorm.schatten_apply_adjoint 2 (Â - A)
    simpa only [map_sub, UnitarilyInvariantSeminorm.schatten_two] using h
  simpa only [LinearMap.adjoint_adjoint, hdiff, LinearMap.adjoint_toContinuousLinearMap,
    LinearIsometryEquiv.norm_map] using h

omit [FiniteDimensional 𝕜 F] in
/-- The common Gram coefficient is bounded by the source-shaped
Yu--Wang--Samworth coefficient.  Keeping this arithmetic fact separate lets the
operator and Frobenius branches share exactly the same normalization step. -/
theorem sum_opNorm_le_paperCoefficient (A Â : E →ₗ[𝕜] F) :
    ‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖ ≤
      2 * ‖A.toContinuousLinearMap‖ +
        ‖(Â - A).toContinuousLinearMap‖ := by
  have hÂ :
      ‖Â.toContinuousLinearMap‖ ≤
        ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖ := by
    have h := norm_add_le A.toContinuousLinearMap
      (Â - A).toContinuousLinearMap
    have hadd :
        A.toContinuousLinearMap + (Â - A).toContinuousLinearMap =
          Â.toContinuousLinearMap := by
      ext x
      change A x + (Â x - A x) = Â x
      abel
    rwa [hadd] at h
  linarith

/-- Operator-norm perturbation bound with the exact coefficient displayed in
Yu--Wang--Samworth Theorem 3 (Theorem 4 in the 2014 preprint). -/
theorem opNorm_rightGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    ‖((Â.adjoint ∘ₗ Â) - (A.adjoint ∘ₗ A)).toContinuousLinearMap‖ ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  let : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  have h := ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le
    Â.toContinuousLinearMap A.toContinuousLinearMap
  have hgram :
      ‖((Â.adjoint ∘ₗ Â) - (A.adjoint ∘ₗ A)).toContinuousLinearMap‖ =
        ‖Â.toContinuousLinearMap.adjoint ∘L Â.toContinuousLinearMap -
          A.toContinuousLinearMap.adjoint ∘L A.toContinuousLinearMap‖ := by
    congr 1
  rw [hgram]
  exact h.trans (mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â) (norm_nonneg _))

/-- Left-Gram operator-norm counterpart with the exact paper coefficient. -/
theorem opNorm_leftGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    ‖((Â ∘ₗ Â.adjoint) - (A ∘ₗ A.adjoint)).toContinuousLinearMap‖ ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  let : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  have h := ContinuousLinearMap.norm_self_comp_adjoint_sub_self_comp_adjoint_le
    Â.toContinuousLinearMap A.toContinuousLinearMap
  have hgram :
      ‖((Â ∘ₗ Â.adjoint) - (A ∘ₗ A.adjoint)).toContinuousLinearMap‖ =
        ‖Â.toContinuousLinearMap ∘L Â.toContinuousLinearMap.adjoint -
          A.toContinuousLinearMap ∘L A.toContinuousLinearMap.adjoint‖ := by
    congr 1
  rw [hgram]
  exact h.trans (mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â) (norm_nonneg _))

/-- Frobenius perturbation bound for the right Gram operator with the exact
coefficient displayed in Yu--Wang--Samworth Theorem 3 (Theorem 4 in the 2014
preprint). -/
theorem frobenius_rightGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)
        ((Â.adjoint ∘ₗ Â) - (A.adjoint ∘ₗ A)) ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        UnitarilyInvariantSeminorm.frobenius 𝕜 E F (Â - A) := by
  refine (frobenius_rightGram_sub_le A Â).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â)
    (by
      rw [UnitarilyInvariantSeminorm.frobenius_apply (stdOrthonormalBasis 𝕜 E)]
      exact Real.sqrt_nonneg _)

/-- Left-Gram Frobenius counterpart with the exact paper coefficient. -/
theorem frobenius_leftGram_sub_le_paperCoefficient
    (A Â : E →ₗ[𝕜] F) :
    UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := F)
        ((Â ∘ₗ Â.adjoint) - (A ∘ₗ A.adjoint)) ≤
      (2 * ‖A.toContinuousLinearMap‖ +
          ‖(Â - A).toContinuousLinearMap‖) *
        UnitarilyInvariantSeminorm.frobenius 𝕜 E F (Â - A) := by
  refine (frobenius_leftGram_sub_le A Â).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_opNorm_le_paperCoefficient A Â)
    (by
      rw [UnitarilyInvariantSeminorm.frobenius_apply (stdOrthonormalBasis 𝕜 E)]
      exact Real.sqrt_nonneg _)

end DavisKahanTheory
end YuWangSamworth2015
