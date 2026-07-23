/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Lemma63
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank

/-!
# Mathematics-ahead proof of Davis--Kahan Lemma 6.3

The frontier signature accidentally stated

`K * P = Q * K`.

That equation already forces `Q * K * (1-P) = 0`, making the conclusion
trivial and failing to represent the paper.  The source hypothesis is

`K * P = Q * K * P`,

which only says that the image of the selected source block lies in the
selected target block.

This file states the corrected result and exposes the exact three ingredients
of the proof:

1. left compression by a rank-`n` projection cannot increase the first-`n`
   square energy;
2. Hilbert--Schmidt energy splits over the orthogonal domain decomposition
   `P + (1-P)`;
3. operator norm is bounded by the Hilbert--Schmidt energy of the off block.

The final argument is then a scalar subtraction.
-/

open scoped InnerProductSpace BigOperators ENNReal
open Finset

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace Section6Appendix

open ExactSinTheta

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Sum of squares of the first `n` approximation singular values. -/
noncomputable def approximationSquareEnergy
    (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (approximationSingularValue i T) ^ 2

theorem approximationSquareEnergy_nonneg
    (T : E →L[ℂ] F) (n : ℕ) :
    0 ≤ approximationSquareEnergy T n := by
  unfold approximationSquareEnergy
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The zeroth approximation number is the operator norm, so every nonempty
prefix square energy dominates the squared operator norm. -/
theorem opNorm_sq_le_approximationSquareEnergy
    (T : E →L[ℂ] F) {n : ℕ} (hn : 0 < n) :
    ‖T‖ ^ 2 ≤ approximationSquareEnergy T n := by
  unfold approximationSquareEnergy
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
  have hzero :
      (approximationSingularValue 0 T) ^ 2 = ‖T‖ ^ 2 := by
    unfold approximationSingularValue
    rw [T.approximationNumber_zero]
    rfl
  calc
    ‖T‖ ^ 2 = (approximationSingularValue 0 T) ^ 2 := hzero.symm
    _ ≤ ∑ i ∈ Finset.range n,
        (approximationSingularValue i T) ^ 2 := by
      exact Finset.single_le_sum
        (fun i hi => sq_nonneg (approximationSingularValue i T)) hmem

/-- Left composition by an orthogonal projection cannot increase the first
`n` square energy. -/
theorem approximationSquareEnergy_starProjection_comp_le
    (K : E →L[ℂ] F)
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection] (n : ℕ) :
    approximationSquareEnergy (Q.starProjection ∘L K) n ≤
      approximationSquareEnergy K n := by
  unfold approximationSquareEnergy
  apply Finset.sum_le_sum
  intro i hi
  have hcompNN :
      (Q.starProjection ∘L K).approximationNumber i ≤
        ‖Q.starProjection‖₊ * K.approximationNumber i :=
    ContinuousLinearMap.approximationNumber_comp_left_le
      Q.starProjection K i
  have hprojNN : ‖Q.starProjection‖₊ ≤ 1 := by
    exact_mod_cast Q.starProjection_norm_le
  have hcomp :
      approximationSingularValue i (Q.starProjection ∘L K) ≤
        approximationSingularValue i K := by
    unfold approximationSingularValue
    calc
      (((Q.starProjection ∘L K).approximationNumber i : NNReal) : ℝ)
          ≤ ((‖Q.starProjection‖₊ *
              K.approximationNumber i : NNReal) : ℝ) := by
                exact_mod_cast hcompNN
      _ ≤ ((1 * K.approximationNumber i : NNReal) : ℝ) := by
            exact_mod_cast
              (mul_le_mul_of_nonneg_right hprojNN bot_le)
      _ = ((K.approximationNumber i : NNReal) : ℝ) := by simp
  exact pow_le_pow_left₀
    (approximationSingularValue_nonneg i _)
    hcomp 2

/-- A finite-rank operator's prefix square energy is the real form of its
paper Hilbert--Schmidt energy. -/
theorem approximationSquareEnergy_eq_paperEnergy_toReal_of_rank_le
    (T : E →L[ℂ] F) {n : ℕ}
    (hrank : T.rank ≤ (n : Cardinal)) :
    approximationSquareEnergy T n =
      (paperHilbertSchmidtEnergy T).toReal := by
  rw [paperHilbertSchmidtEnergy_eq_sum_range_of_rank_le hrank]
  unfold approximationSquareEnergy
  rw [ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl fun i hi => by
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro i hi
    exact ENNReal.ofReal_ne_top

/-- Rank of a left-compressed operator is bounded by the rank of the
compressing projection. -/
theorem rank_starProjection_comp_le
    (K : E →L[ℂ] F)
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection] :
    (Q.starProjection ∘L K).rank ≤ Q.starProjection.rank := by
  exact LinearMap.rank_comp_le_left
    Q.starProjection.toLinearMap K.toLinearMap

/-- The paper square energy splits over an orthogonal decomposition of the
domain.  This is the basis-free Pythagorean identity used in Lemma 6.3. -/
theorem paperHilbertSchmidtEnergy_domain_projection_add
    (L : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (hfinite : IsPaperHilbertSchmidt L) :
    paperHilbertSchmidtEnergy L =
      paperHilbertSchmidtEnergy (L ∘L P.starProjection) +
      paperHilbertSchmidtEnergy
        (L ∘L (1 - P.starProjection)) := by
  classical
  obtain ⟨ιP, bP, hbP⟩ := exists_hilbertBasis ℂ P
  obtain ⟨ιC, bC, hbC⟩ := exists_hilbertBasis ℂ Pᗮ
  let b : HilbertBasis (ιP ⊕ ιC) ℂ E :=
    HilbertBasis.orthogonalSumSubmodule bP bC P
  rw [paperHilbertSchmidtEnergy_eq_basisEnergy b L,
    paperHilbertSchmidtEnergy_eq_basisEnergy b
      (L ∘L P.starProjection),
    paperHilbertSchmidtEnergy_eq_basisEnergy b
      (L ∘L (1 - P.starProjection))]
  unfold paperHilbertSchmidtBasisEnergy
  rw [Equiv.tsum_sum]
  apply congrArg₂ (· + ·)
  · apply tsum_congr
    intro i
    have hbi : b (Sum.inl i) ∈ P :=
      HilbertBasis.orthogonalSumSubmodule_inl_mem bP bC P i
    have hPfix : P.starProjection (b (Sum.inl i)) = b (Sum.inl i) :=
      P.starProjection_eq_self_iff.mpr hbi
    have hPc0 : (1 - P.starProjection) (b (Sum.inl i)) = 0 := by
      simp [hPfix]
    simp [ContinuousLinearMap.comp_apply, hPfix, hPc0]
  · apply tsum_congr
    intro i
    have hbi : b (Sum.inr i) ∈ Pᗮ :=
      HilbertBasis.orthogonalSumSubmodule_inr_mem bP bC P i
    have hP0 : P.starProjection (b (Sum.inr i)) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff P).mpr hbi
    have hPcfix : (1 - P.starProjection) (b (Sum.inr i)) =
        b (Sum.inr i) := by
      simp [hP0]
    simp [ContinuousLinearMap.comp_apply, hP0, hPcfix]

/-- Under the paper's block-invariance hypothesis the selected source block
is exactly the source restriction of the left-compressed operator. -/
theorem leftCompressed_comp_source_eq
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K ∘L P.starProjection) :
    (Q.starProjection ∘L K) ∘L P.starProjection =
      K ∘L P.starProjection := by
  simpa only [ContinuousLinearMap.comp_assoc] using hKP.symm

/-- Correct approximation-number form of Davis--Kahan 1970, Lemma 6.3. -/
theorem lemma6_3_approximationNumber_leakage_completed
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (hKP :
      K ∘L P.starProjection =
        Q.starProjection ∘L K ∘L P.starProjection)
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      approximationSquareEnergy (K ∘L P.starProjection) n >
        approximationSquareEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  let L : E →L[ℂ] F := Q.starProjection ∘L K
  let A : E →L[ℂ] F := K ∘L P.starProjection
  let B : E →L[ℂ] F :=
    Q.starProjection ∘L K ∘L (1 - P.starProjection)
  have hrankL : L.rank ≤ (n : Cardinal) := by
    dsimp [L]
    exact (rank_starProjection_comp_le K Q).trans hrankQ
  have hLfinite : IsPaperHilbertSchmidt L :=
    isPaperHilbertSchmidt_of_rank_le hrankL
  have hrankA : A.rank ≤ (n : Cardinal) := by
    have hAeq :
        A = Q.starProjection ∘L K ∘L P.starProjection := by
      dsimp [A]
      exact hKP
    rw [hAeq]
    exact
      (rank_starProjection_comp_le
        (K ∘L P.starProjection) Q).trans hrankQ
  have hrankB : B.rank ≤ (n : Cardinal) := by
    dsimp [B]
    exact
      (rank_starProjection_comp_le
        (K ∘L (1 - P.starProjection)) Q).trans hrankQ
  have hsplitE :
      approximationSquareEnergy L n =
        approximationSquareEnergy A n +
          approximationSquareEnergy B n := by
    have henergy :=
      paperHilbertSchmidtEnergy_domain_projection_add L P hLfinite
    have hLP : L ∘L P.starProjection = A := by
      dsimp [L, A]
      exact leftCompressed_comp_source_eq K P Q hKP
    have hLB :
        L ∘L (1 - P.starProjection) = B := by
      rfl
    have hAfinite : IsPaperHilbertSchmidt A :=
      isPaperHilbertSchmidt_of_rank_le hrankA
    have hBfinite : IsPaperHilbertSchmidt B :=
      isPaperHilbertSchmidt_of_rank_le hrankB
    have hreal := congrArg ENNReal.toReal henergy
    rw [hLP, hLB, ENNReal.toReal_add hAfinite hBfinite,
      ← approximationSquareEnergy_eq_paperEnergy_toReal_of_rank_le hrankL,
      ← approximationSquareEnergy_eq_paperEnergy_toReal_of_rank_le hrankA,
      ← approximationSquareEnergy_eq_paperEnergy_toReal_of_rank_le hrankB] at hreal
    exact hreal
  have hLle :
      approximationSquareEnergy L n ≤
        approximationSquareEnergy K n := by
    dsimp [L]
    exact approximationSquareEnergy_starProjection_comp_le K Q n
  have hBenergy : approximationSquareEnergy B n < η ^ 2 := by
    rw [hsplitE] at hLle
    dsimp [A] at hnear
    nlinarith
  have hnormsq : ‖B‖ ^ 2 ≤ approximationSquareEnergy B n :=
    opNorm_sq_le_approximationSquareEnergy B hn
  have hsq : ‖B‖ ^ 2 < η ^ 2 :=
    lt_of_le_of_lt hnormsq hBenergy
  have hnormnonneg : 0 ≤ ‖B‖ := norm_nonneg B
  have hηnonneg : 0 ≤ η := le_of_lt hη
  have hnorm : ‖B‖ < η := by
    nlinarith
  simpa only [B] using hnorm

end Section6Appendix
end MathAhead
end Experimental
end DavisKahan
end ForMathlib
