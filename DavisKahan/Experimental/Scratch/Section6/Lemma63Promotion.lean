/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.Lemma63

/-!
# Promotion surface for Davis--Kahan 1970, Lemma 6.3

This file separates two logically different statements.

The current frontier equation identifies `K * P` with all of `Q * K`.  That
strong equation annihilates the complementary block immediately, so the
quantitative energy hypothesis is unnecessary.

The source equation identifies `K * P` only with `Q * K * P`.  The resulting
leakage estimate is the substantive statement.  Its approximation-number proof
is supplied by the mathematics-ahead development, and the finite-dimensional
singular-value form is derived here explicitly.
-/

open scoped InnerProductSpace BigOperators
open Finset

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace Section6

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The block equation currently used by the frontier annihilates the leakage
block without any singular-value information. -/
theorem strongBlockEquation_forces_zero_leakage
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K) :
    Q.starProjection ∘L K ∘L (1 - P.starProjection) = 0 := by
  ext x
  have hPidem :
      P.starProjection (P.starProjection x) = P.starProjection x :=
    congrArg (fun T : E →L[ℂ] E => T x)
      P.isIdempotentElem_starProjection
  have hPzero :
      P.starProjection ((1 - P.starProjection) x) = 0 := by
    simp only [sub_apply, one_apply, map_sub]
    rw [hPidem, sub_self]
  have hblock := congrArg
    (fun T : E →L[ℂ] F => T ((1 - P.starProjection) x)) hKP
  simp only [ContinuousLinearMap.comp_apply] at hblock
  calc
    (Q.starProjection ∘L K ∘L (1 - P.starProjection)) x =
        Q.starProjection (K ((1 - P.starProjection) x)) := rfl
    _ = K (P.starProjection ((1 - P.starProjection) x)) := hblock.symm
    _ = 0 := by rw [hPzero, map_zero]
    _ = (0 : E →L[ℂ] F) x := rfl

/-- Grounded replacement for the current approximation-number frontier body.
The rank and energy assumptions are retained only to match its present public
signature. -/
theorem frontier_lemma6_3_approximationNumber_leakage
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      Frontier.Section6Appendix.approximationEnergy
          (K ∘L P.starProjection) n >
        Frontier.Section6Appendix.approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  clear hrankP hrankQ hnear
  rw [strongBlockEquation_forces_zero_leakage K P Q hKP, norm_zero]
  exact hη

/-- Grounded replacement for the current finite-dimensional frontier body.
As above, the present block equation makes the quantitative assumptions
redundant. -/
theorem frontier_lemma6_3_singularValue_leakage
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
  clear hrankP hrankQ hnear
  rw [strongBlockEquation_forces_zero_leakage K P Q hKP, norm_zero]
  exact hη

/-- The present frontier equation implies the paper's source-block equation. -/
theorem sourceBlockEquation_of_strongBlockEquation
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K) :
    K ∘L P.starProjection =
      Q.starProjection ∘L K ∘L P.starProjection := by
  calc
    K ∘L P.starProjection =
        (K ∘L P.starProjection) ∘L P.starProjection := by
      rw [ContinuousLinearMap.comp_assoc,
        P.isIdempotentElem_starProjection]
    _ = Q.starProjection ∘L K ∘L P.starProjection := by rw [hKP]

/-- The frontier energy and the mathematics-ahead square energy are the same
quantity under their two names. -/
theorem approximationEnergy_eq_approximationSquareEnergy
    (T : E →L[ℂ] F) (n : ℕ) :
    Frontier.Section6Appendix.approximationEnergy T n =
      MathAhead.Section6Appendix.approximationSquareEnergy T n := by
  rfl

/-- Paper-faithful approximation-number form.  The positive-prefix hypothesis
is explicit because the proof controls the operator norm through the zeroth
approximation number. -/
theorem paper_lemma6_3_approximationNumber_leakage
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      Frontier.Section6Appendix.approximationEnergy
          (K ∘L P.starProjection) n >
        Frontier.Section6Appendix.approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  clear hrankP
  apply
    MathAhead.Section6Appendix.lemma6_3_approximationNumber_leakage_completed
      K P Q n hn η hη hKP hrankQ
  simpa only [approximationEnergy_eq_approximationSquareEnergy] using hnear

/-- In finite dimensions, the frontier approximation energy is the sum of the
squared ordinary singular values over the same prefix. -/
theorem approximationEnergy_eq_singularValues
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) (n : ℕ) :
    Frontier.Section6Appendix.approximationEnergy T n =
      ∑ i ∈ Finset.range n,
        ((LinearMap.singularValues T.toLinearMap i : ℝ) ^ 2) := by
  unfold Frontier.Section6Appendix.approximationEnergy
  apply Finset.sum_congr rfl
  intro i hi
  have hsv :=
    ContinuousLinearMap.approximationNumber_eq_singularValues T i
  change ((T.approximationNumber i : ℝ) ^ 2) =
    (T.toLinearMap.singularValues i : ℝ) ^ 2
  rw [hsv]
  rfl

/-- Paper-faithful finite-dimensional singular-value specialization. -/
theorem paper_lemma6_3_singularValue_leakage
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues
            (K ∘L P.starProjection).toLinearMap i : ℝ) ^ 2) >
        ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues K.toLinearMap i : ℝ) ^ 2) - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  apply paper_lemma6_3_approximationNumber_leakage
    K P Q n hn η hη hKP hrankP hrankQ
  simpa only [approximationEnergy_eq_singularValues] using hnear

end Section6
end Scratch
end Experimental
end DavisKahan
end ForMathlib
