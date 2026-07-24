/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The rectangular operator modulus

For a bounded operator `T : E -> F` between complex Hilbert spaces, its source
modulus is the positive square root `(T* T)^(1/2)` of the Gram operator `T* T`
on `E`.  This module develops the elementary, purely functional-analytic
properties of that object: it is nonnegative, self-adjoint, squares to the Gram
operator, and preserves the pointwise and operator norms of `T`.

## Namespace note

These declarations are helper facts (not dot notation on a Mathlib type), so
they live under `namespace TauCeti`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations (this file): `rectangularOperatorModulus`,
  `rectangularGram_nonneg`, `rectangularOperatorModulus_nonneg`,
  `isSelfAdjoint_rectangularOperatorModulus`,
  `rectangularOperatorModulus_mul_self`,
  `norm_rectangularOperatorModulus_apply`, `norm_rectangularOperatorModulus`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied (partial — Spectra-coupled and paper-facing
  declarations deferred)**.  The original file additionally proves the
  modulus-invariance theorem for approximation singular values
  (`approximationSingularValue_le_of_norm_apply_le`,
  `sameApproximationSingularValues_of_norm_apply_eq`,
  `sameApproximationSingularValues_rectangularOperatorModulus`,
  `operatorAbs_sameApproximationSingularValues`, `operatorAbs_mem_and_gauge_eq`,
  `paperNorm_operatorAbs_eq`); those depend on Spectra `SpectraBridge`,
  `ForMathlib.operatorAbs`, and paper types, and are **deferred** to a later PR.
  The enclosing namespaces `ForMathlib / DavisKahan / Experimental /
  ExactSinTheta` were flattened to a single `TauCeti`.  No mathematical change.
* Spectra influence: the deferred full modulus-invariance theorem is the only
  Spectra-coupled part; the declarations kept here import only Mathlib.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

noncomputable section

universe v vF

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The positive source modulus `(T* T)^(1/2)` of a rectangular operator. -/
noncomputable def rectangularOperatorModulus (T : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

/-- The Gram operator of a rectangular map is nonnegative. -/
theorem rectangularGram_nonneg (T : E →L[ℂ] F) :
    0 ≤ T.adjoint ∘L T :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self T)

/-- The rectangular modulus is nonnegative. -/
theorem rectangularOperatorModulus_nonneg (T : E →L[ℂ] F) :
    0 ≤ rectangularOperatorModulus T :=
  CFC.sqrt_nonneg _

/-- The rectangular modulus is self-adjoint. -/
theorem isSelfAdjoint_rectangularOperatorModulus (T : E →L[ℂ] F) :
    IsSelfAdjoint (rectangularOperatorModulus T) :=
  IsSelfAdjoint.of_nonneg (rectangularOperatorModulus_nonneg T)

/-- Defining square identity for the rectangular modulus. -/
theorem rectangularOperatorModulus_mul_self (T : E →L[ℂ] F) :
    rectangularOperatorModulus T * rectangularOperatorModulus T =
      T.adjoint ∘L T := by
  exact CFC.sqrt_mul_sqrt_self _ (rectangularGram_nonneg T)

/-- The rectangular modulus preserves the pointwise norm of `T`. -/
theorem norm_rectangularOperatorModulus_apply (T : E →L[ℂ] F) (x : E) :
    ‖rectangularOperatorModulus T x‖ = ‖T x‖ := by
  have hself : (rectangularOperatorModulus T).adjoint =
      rectangularOperatorModulus T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (isSelfAdjoint_rectangularOperatorModulus T).star_eq
  have hmod :
      (⟪rectangularOperatorModulus T x,
          rectangularOperatorModulus T x⟫_ℂ : ℂ) =
        ⟪x, (rectangularOperatorModulus T *
          rectangularOperatorModulus T) x⟫_ℂ := by
    calc
      (⟪rectangularOperatorModulus T x,
          rectangularOperatorModulus T x⟫_ℂ : ℂ)
          = ⟪(rectangularOperatorModulus T).adjoint x,
              rectangularOperatorModulus T x⟫_ℂ := by rw [hself]
      _ = ⟪x, rectangularOperatorModulus T
              (rectangularOperatorModulus T x)⟫_ℂ :=
            ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪x, (rectangularOperatorModulus T *
              rectangularOperatorModulus T) x⟫_ℂ := rfl
  have hT : (⟪T x, T x⟫_ℂ : ℂ) = ⟪x, (T.adjoint ∘L T) x⟫_ℂ := by
    exact (ContinuousLinearMap.adjoint_inner_right T x (T x)).symm
  have hinner :
      (⟪rectangularOperatorModulus T x,
          rectangularOperatorModulus T x⟫_ℂ : ℂ) = ⟪T x, T x⟫_ℂ := by
    rw [hmod, hT, rectangularOperatorModulus_mul_self]
  have hsq : ‖rectangularOperatorModulus T x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- The rectangular modulus has the same operator norm as the original map. -/
theorem norm_rectangularOperatorModulus (T : E →L[ℂ] F) :
    ‖rectangularOperatorModulus T‖ = ‖T‖ := by
  apply le_antisymm
  · refine (rectangularOperatorModulus T).opNorm_le_bound (norm_nonneg T) ?_
    intro x
    rw [norm_rectangularOperatorModulus_apply]
    exact T.le_opNorm x
  · refine T.opNorm_le_bound (norm_nonneg (rectangularOperatorModulus T)) ?_
    intro x
    rw [← norm_rectangularOperatorModulus_apply]
    exact (rectangularOperatorModulus T).le_opNorm x

end

end TauCeti

end
