/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidt
import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

/-!
# Finite-dimensional Frobenius realization of the paper square norm

On finite-dimensional real or complex Hilbert spaces, the paper square norm
built from approximation singular values is exactly the usual rectangular
Frobenius norm.  This is the missing bridge needed to evaluate the printed
Section 6 counterexample by an ordinary finite column calculation.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u vE vF

/-- In finite dimensions, the paper square energy is the finite sum of the
squares of the ordinary rectangular singular values. -/
theorem paperHilbertSchmidtEnergy_eq_ofReal_sum_sq_singularValues
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) :
    paperHilbertSchmidtEnergy A =
      ENNReal.ofReal
        (∑ i : Fin (Module.finrank 𝕜 E),
          A.toLinearMap.singularValues (i : ℕ) ^ 2) := by
  unfold paperHilbertSchmidtEnergy
  rw [tsum_eq_sum (s := Finset.range (Module.finrank 𝕜 E))]
  · rw [← Fin.sum_univ_eq_sum_range,
      ← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [approximationSingularValue_eq_singularValues]
  · intro n hn
    have hfinrank : Module.finrank 𝕜 E ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    rw [approximationSingularValue_eq_singularValues,
      A.toLinearMap.singularValues_of_finrank_le hfinrank]
    simp

/-- In finite dimensions, the basis-free paper square norm is exactly the
rectangular Frobenius norm. -/
theorem paperHilbertSchmidtNorm_eq_rectangularFrobenius
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) :
    paperHilbertSchmidtNorm A =
      ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm.frobenius
        A.toLinearMap := by
  unfold paperHilbertSchmidtNorm
  rw [paperHilbertSchmidtEnergy_eq_ofReal_sum_sq_singularValues,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact (ForMathlib.DavisKahanTheory.RectangularUnitarilyInvariantNorm
    .frobenius_eq_sqrt_sum_sq_singularValues A.toLinearMap).symm

/-- Square-operator spelling of the finite-dimensional Frobenius bridge. -/
theorem paperHilbertSchmidtNorm_eq_frobenius
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E) :
    paperHilbertSchmidtNorm A =
      ForMathlib.UnitarilyInvariantNorm.frobenius 𝕜 E A.toLinearMap := by
  rw [paperHilbertSchmidtNorm_eq_rectangularFrobenius]
  rfl

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
