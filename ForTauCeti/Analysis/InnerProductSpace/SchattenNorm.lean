/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten

/-!
# The finite Schatten and Hilbert–Schmidt comparison

Tau Ceti supplies the rectangular operator, Frobenius, Ky Fan, nuclear, and Schatten seminorms.
This module keeps only the DKPS identity relating finite-dimensional Frobenius norm to the
Hilbert–Schmidt energy of a bounded operator.

## Provenance

The removed Schatten construction and its endpoint proofs duplicated
`TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten`. The retained identity
combines the local Hilbert–Schmidt energy with Tau Ceti's Frobenius norm.
-/

public section

open scoped InnerProductSpace BigOperators

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 F] in
/-- In finite dimension the Hilbert–Schmidt energy is the square of the rectangular
Frobenius norm. Completeness is explicit because finite-dimensional completeness is
not a global instance. -/
theorem hilbertSchmidtEnergy_eq_ofReal_frobenius_sq [CompleteSpace E]
    (A : E →L[𝕜] F) :
    A.hilbertSchmidtEnergy (stdOrthonormalBasis 𝕜 E).toHilbertBasis =
      ENNReal.ofReal (frobenius 𝕜 E F A.toLinearMap ^ 2) := by
  have hsq : frobenius 𝕜 E F A.toLinearMap ^ 2
      = ∑ i, ‖A.toLinearMap (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := by
    exact sq_frobenius_apply (stdOrthonormalBasis 𝕜 E) A.toLinearMap
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_fintype, hsq,
    ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_toHilbertBasis, ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]
  rfl

end TauCeti.UnitarilyInvariantSeminorm
