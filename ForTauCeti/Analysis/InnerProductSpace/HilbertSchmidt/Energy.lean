/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# Additional Hilbert–Schmidt energy formulas

Tau Ceti owns the energy, its basis and adjoint invariance, and its ideal estimates.
Only the finite-partial-sum formula, negation, and the pointwise energy bound remain here.

## Provenance

These consequences were authored in the DKPS donor layer by Jon Crall and Claude Opus 5.
The duplicate construction and energy laws were retired in favor of the accepted API.
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The energy is the supremum of its finite partial sums. -/
theorem hilbertSchmidtEnergy_eq_iSup_sum (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    T.hilbertSchmidtEnergy b = ⨆ s : Finset ι, ∑ i ∈ s, ‖T (b i)‖ₑ ^ 2 := by
  rw [hilbertSchmidtEnergy_def, ENNReal.tsum_eq_iSup_sum]

/-- Energy is unchanged by negation. -/
@[simp] theorem hilbertSchmidtEnergy_neg (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (-T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  simp [hilbertSchmidtEnergy_def]

variable [CompleteSpace E] [CompleteSpace F]

/-- The energy bounds the squared norm of every value of the operator. -/
theorem enorm_apply_sq_le_hilbertSchmidtEnergy_mul (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (x : E) : ‖T x‖ₑ ^ 2 ≤ T.hilbertSchmidtEnergy b * ‖x‖ₑ ^ 2 := by
  calc
    ‖T x‖ₑ ^ 2 ≤ (‖T‖ₑ * ‖x‖ₑ) ^ 2 := by gcongr; exact T.le_opENorm x
    _ = ‖T‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := mul_pow _ _ _
    _ ≤ T.hilbertSchmidtEnergy b * ‖x‖ₑ ^ 2 := by
      gcongr
      exact T.enorm_sq_le_hilbertSchmidtEnergy b

end ContinuousLinearMap
