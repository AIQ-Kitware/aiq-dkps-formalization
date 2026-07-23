/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Core
import ForMathlib.Analysis.Normed.Operator.ApproximationNumberSingularValues

/-!
# Davis--Kahan 1970, Lemma 6.3

The paper uses the first Ky Fan norm in the conclusion, hence the operator
norm.  The quantitative input is near-saturation of the sum of squares of the
first `v` singular values.  This module states both an approximation-number
form and the finite-dimensional singular-value specialization.
-/

open scoped InnerProductSpace
open Finset

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section6Appendix

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Sum of squares of the first `n` approximation numbers. -/
noncomputable def approximationEnergy
    (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ((T.approximationNumber i : ℝ) ^ 2)

/-- Approximation-number form of Davis--Kahan Lemma 6.3. -/
theorem lemma6_3_approximationNumber_leakage
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : approximationEnergy (K ∘L P.starProjection) n >
      approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  sorry

/-- Finite-dimensional singular-value specialization of Lemma 6.3. -/
theorem lemma6_3_singularValue_leakage
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues
            (K ∘L P.starProjection).toLinearMap i : ℝ) ^ 2) >
        ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues K.toLinearMap i : ℝ) ^ 2) - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  sorry

end Section6Appendix
end Frontier
end Experimental
end DavisKahan
end ForMathlib
