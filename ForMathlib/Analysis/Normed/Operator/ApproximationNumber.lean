/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Approximation numbers of bounded operators

This file adapts the definition and elementary order API developed in Mathlib
PR #32126 to the project's pinned Mathlib revision.  The zero-based
approximation number of `T` at index `n` is the operator-norm distance from
`T` to continuous linear maps of rank at most `n`.

The declarations here deliberately stop before Hilbert-space-specific results.
Adjoint invariance is in `ApproximationNumberAdjoint`; finite-dimensional
singular-value identification and infinite-dimensional min--max lower bounds
are provided by separate sibling modules.
-/

open NNReal

noncomputable section

universe u v w x y

namespace Cardinal

/-- A natural-number bound on a cardinal is invariant under universe lifting.

Ranks of maps between spaces in different universes are not directly
comparable, but every bound used by the approximation-number API is a natural
number, and natural numbers are fixed by `Cardinal.lift`. -/
theorem le_natCast_of_lift_le {c : Cardinal.{v}} {n : ℕ}
    (h : Cardinal.lift.{w} c ≤ (n : Cardinal)) : c ≤ (n : Cardinal) := by
  rwa [← Cardinal.lift_natCast.{w} n, Cardinal.lift_le] at h

end Cardinal

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} {F : Type w}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Zero-based approximation number: distance in operator norm to maps of
rank at most `n`. -/
private instance approximationNumberIndexNonempty (n : ℕ) :
    Nonempty {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)} :=
  ⟨⟨0, by simp [LinearMap.rank_zero]⟩⟩

noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖₊

@[simp]
theorem approximationNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n =
      ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖₊ :=
  rfl

/-- Every admissible finite-rank approximation bounds the infimum. -/
theorem approximationNumber_le (T : E →L[𝕜] F) {n : ℕ}
    {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal)) :
    T.approximationNumber n ≤ ‖T - R‖₊ :=
  ciInf_le' (fun S : {S : E →L[𝕜] F // S.rank ≤ (n : Cardinal)} =>
    ‖T - S.1‖₊) ⟨R, hR⟩

/-- Lower-bound introduction rule for approximation numbers. -/
theorem le_approximationNumber (T : E →L[𝕜] F) {n : ℕ} (x : ℝ≥0)
    (h : ∀ R : E →L[𝕜] F, R.rank ≤ (n : Cardinal) → x ≤ ‖T - R‖₊) :
    x ≤ T.approximationNumber n := by
  apply le_ciInf
  rintro ⟨R, hR⟩
  exact h R hR

/-- Characterization when a best rank-`n` approximation is available. -/
theorem approximationNumber_eq (T : E →L[𝕜] F) {n : ℕ}
    {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal))
    (hbest : ∀ S : E →L[𝕜] F, S.rank ≤ (n : Cardinal) →
      ‖T - R‖₊ ≤ ‖T - S‖₊) :
    T.approximationNumber n = ‖T - R‖₊ := by
  apply le_antisymm
  · exact T.approximationNumber_le hR
  · exact T.le_approximationNumber _ hbest

/-- The first zero-based approximation number is the operator norm. -/
@[simp]
theorem approximationNumber_zero (T : E →L[𝕜] F) :
    T.approximationNumber 0 = ‖T‖₊ := by
  suffices h : T.approximationNumber 0 = ‖T - 0‖₊ by simpa using h
  apply T.approximationNumber_eq
  · simp [LinearMap.rank_zero]
  · intro R hR
    apply le_of_eq
    congr
    symm
    simpa [LinearMap.range_eq_bot, ← ContinuousLinearMap.toLinearMap_zero,
      ContinuousLinearMap.coe_inj] using hR

/-- Approximation numbers decrease with the allowed rank. -/
theorem antitone_approximationNumber (T : E →L[𝕜] F) :
    Antitone T.approximationNumber := by
  intro n m hnm
  apply T.le_approximationNumber
  intro R hR
  exact T.approximationNumber_le
    (hR.trans (by exact_mod_cast hnm))

/-- Every approximation number is bounded by the operator norm. -/
theorem approximationNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ≤ ‖T‖₊ := by
  calc
    T.approximationNumber n ≤ T.approximationNumber 0 :=
      T.antitone_approximationNumber (Nat.zero_le n)
    _ = ‖T‖₊ := T.approximationNumber_zero

/-- The zero operator has every approximation number equal to zero. -/
@[simp]
theorem zero_approximationNumber (n : ℕ) :
    (0 : E →L[𝕜] F).approximationNumber n = 0 := by
  apply le_antisymm
  · simpa using
      (approximationNumber_le (0 : E →L[𝕜] F) (n := n) (R := 0)
        (by simp [LinearMap.rank_zero]))
  · exact bot_le

/-- Approximation numbers are nonnegative. -/
theorem approximationNumber_nonneg (T : E →L[𝕜] F) (n : ℕ) :
    0 ≤ T.approximationNumber n := bot_le

/-- Near-minimizers exist for the defining infimum. -/
theorem lt_approximationNumber_add_pos (T : E →L[𝕜] F)
    (n : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F,
      R.rank ≤ (n : Cardinal) ∧
        ‖T - R‖₊ < T.approximationNumber n + ε := by
  have hlt : T.approximationNumber n < T.approximationNumber n + ε := by
    exact lt_add_of_pos_right _ hε
  rw [T.approximationNumber_def] at hlt
  obtain ⟨⟨R, hR⟩, hdist⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨R, hR, hdist⟩

/-- Approximation numbers are Lipschitz in the ambient operator norm. -/
theorem approximationNumber_add_le (T S : E →L[𝕜] F) (n : ℕ) :
    (T + S).approximationNumber n ≤ T.approximationNumber n + ‖S‖₊ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have happ := T.lt_approximationNumber_add_pos n hε
  obtain ⟨R, hRrank, hRdist⟩ := happ
  exact le_of_lt <| calc
    (T + S).approximationNumber n ≤ ‖(T + S) - R‖₊ :=
      (T + S).approximationNumber_le hRrank
    _ = ‖(T - R) + S‖₊ := by congr 1 <;> module
    _ ≤ ‖T - R‖₊ + ‖S‖₊ := nnnorm_add_le _ _
    _ < (T.approximationNumber n + ε) + ‖S‖₊ := by
      simpa [add_comm] using add_lt_add_left hRdist ‖S‖₊
    _ = T.approximationNumber n + ‖S‖₊ + ε := by
      ac_rfl

/-- Shifted addition inequality for approximation numbers. Two approximants
of ranks at most `m` and `n` add to an approximant of rank at most `m + n`. -/
theorem approximationNumber_add_le_add
    (T S : E →L[𝕜] F) (m n : ℕ) :
    (T + S).approximationNumber (m + n) ≤
      T.approximationNumber m + S.approximationNumber n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  obtain ⟨R, hRrank, hRdist⟩ :=
    T.lt_approximationNumber_add_pos m hhalf
  obtain ⟨Q, hQrank, hQdist⟩ :=
    S.lt_approximationNumber_add_pos n hhalf
  have hsumRank : (R + Q).rank ≤ ((m + n : ℕ) : Cardinal) := by
    calc
      (R + Q).rank ≤ R.rank + Q.rank := LinearMap.rank_add_le _ _
      _ ≤ (m : Cardinal) + (n : Cardinal) := add_le_add hRrank hQrank
      _ = ((m + n : ℕ) : Cardinal) := by norm_cast
  exact le_of_lt <| calc
    (T + S).approximationNumber (m + n) ≤ ‖(T + S) - (R + Q)‖₊ :=
      (T + S).approximationNumber_le hsumRank
    _ = ‖(T - R) + (S - Q)‖₊ := by congr 1 <;> module
    _ ≤ ‖T - R‖₊ + ‖S - Q‖₊ := nnnorm_add_le _ _
    _ < (T.approximationNumber m + ε / 2) +
        (S.approximationNumber n + ε / 2) := add_lt_add hRdist hQdist
    _ = T.approximationNumber m + S.approximationNumber n + ε := by
      apply NNReal.eq
      simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
      ring

/-- Rank does not increase after right composition. -/
private theorem rank_comp_right_le_rank
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (R : E →L[𝕜] F) (A : G →L[𝕜] E) :
    (R ∘L A).rank ≤ R.rank := by
  change LinearMap.rank (R.toLinearMap.comp A.toLinearMap) ≤
    LinearMap.rank R.toLinearMap
  exact LinearMap.rank_comp_le_left A.toLinearMap R.toLinearMap

/-- Left composition does not raise the rank past a natural-number bound.

The two ranks live in different universes once the codomain is allowed to move
independently, so the comparison is made through `Cardinal.lift`; a
natural-number bound is invariant under lifting, which is all the ideal
inequalities need. -/
private theorem rank_comp_left_le_of_rank_le
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : F →L[𝕜] G) (R : E →L[𝕜] F) {n : ℕ} (hR : R.rank ≤ (n : Cardinal)) :
    (B ∘L R).rank ≤ (n : Cardinal) := by
  have hcomp :
      Cardinal.lift.{w} (LinearMap.rank (B.toLinearMap.comp R.toLinearMap)) ≤
        Cardinal.lift.{x} (LinearMap.rank R.toLinearMap) :=
    LinearMap.lift_rank_comp_le_right R.toLinearMap B.toLinearMap
  have hbound :
      Cardinal.lift.{x} (LinearMap.rank R.toLinearMap) ≤ (n : Cardinal) := by
    calc
      Cardinal.lift.{x} (LinearMap.rank R.toLinearMap)
          ≤ Cardinal.lift.{x} ((n : Cardinal)) := Cardinal.lift_le.mpr hR
      _ = (n : Cardinal) := Cardinal.lift_natCast n
  exact Cardinal.le_natCast_of_lift_le (hcomp.trans hbound)

/-- Right ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_right_le
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] F) (A : G →L[𝕜] E) (n : ℕ) :
    (T ∘L A).approximationNumber n ≤
      T.approximationNumber n * ‖A‖₊ := by
  by_cases hA : ‖A‖₊ = 0
  · calc
      (T ∘L A).approximationNumber n ≤ ‖T ∘L A‖₊ :=
        (T ∘L A).approximationNumber_le_nnnorm n
      _ ≤ ‖T‖₊ * ‖A‖₊ := ContinuousLinearMap.opNNNorm_comp_le _ _
      _ = T.approximationNumber n * ‖A‖₊ := by simp [hA]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεA : 0 < ε / ‖A‖₊ := div_pos hε (bot_lt_iff_ne_bot.mpr hA)
    obtain ⟨R, hRrank, hRdist⟩ :=
      T.lt_approximationNumber_add_pos n hεA
    have hcompRank : (R ∘L A).rank ≤ (n : Cardinal) :=
      (rank_comp_right_le_rank R A).trans hRrank
    exact le_of_lt <| calc
      (T ∘L A).approximationNumber n ≤ ‖(T ∘L A) - (R ∘L A)‖₊ :=
        (T ∘L A).approximationNumber_le hcompRank
      _ = ‖(T - R) ∘L A‖₊ := by congr 1 <;> ext x <;> simp
      _ ≤ ‖T - R‖₊ * ‖A‖₊ := ContinuousLinearMap.opNNNorm_comp_le _ _
      _ < (T.approximationNumber n + ε / ‖A‖₊) * ‖A‖₊ :=
        mul_lt_mul_of_pos_right hRdist (bot_lt_iff_ne_bot.mpr hA)
      _ = T.approximationNumber n * ‖A‖₊ + ε := by
        rw [add_mul, div_mul_cancel₀ ε hA]

/-- Left ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_left_le
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T).approximationNumber n ≤
      ‖B‖₊ * T.approximationNumber n := by
  by_cases hB : ‖B‖₊ = 0
  · calc
      (B ∘L T).approximationNumber n ≤ ‖B ∘L T‖₊ :=
        (B ∘L T).approximationNumber_le_nnnorm n
      _ ≤ ‖B‖₊ * ‖T‖₊ := ContinuousLinearMap.opNNNorm_comp_le _ _
      _ = ‖B‖₊ * T.approximationNumber n := by simp [hB]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεB : 0 < ε / ‖B‖₊ := div_pos hε (bot_lt_iff_ne_bot.mpr hB)
    obtain ⟨R, hRrank, hRdist⟩ :=
      T.lt_approximationNumber_add_pos n hεB
    have hcompRank : (B ∘L R).rank ≤ (n : Cardinal) :=
      rank_comp_left_le_of_rank_le B R hRrank
    exact le_of_lt <| calc
      (B ∘L T).approximationNumber n ≤ ‖(B ∘L T) - (B ∘L R)‖₊ :=
        (B ∘L T).approximationNumber_le hcompRank
      _ = ‖B ∘L (T - R)‖₊ := by congr 1 <;> ext x <;> simp
      _ ≤ ‖B‖₊ * ‖T - R‖₊ := ContinuousLinearMap.opNNNorm_comp_le _ _
      _ < ‖B‖₊ * (T.approximationNumber n + ε / ‖B‖₊) :=
        mul_lt_mul_of_pos_left hRdist (bot_lt_iff_ne_bot.mpr hB)
      _ = ‖B‖₊ * T.approximationNumber n + ε := by
        rw [mul_add, mul_div_cancel₀ ε hB]

/-- Two-sided ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_comp_le
    {G : Type x} {H : Type y}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E)
    (n : ℕ) :
    (L ∘L T ∘L R).approximationNumber n ≤
      ‖L‖₊ * T.approximationNumber n * ‖R‖₊ := by
  calc
    (L ∘L T ∘L R).approximationNumber n
        ≤ (L ∘L T).approximationNumber n * ‖R‖₊ :=
      (L ∘L T).approximationNumber_comp_right_le R n
    _ ≤ (‖L‖₊ * T.approximationNumber n) * ‖R‖₊ := by
      gcongr
      exact approximationNumber_comp_left_le L T n

/-- Rank of scalar multiples is no larger than the original rank. -/
private theorem rank_smul_le_rank (c : 𝕜) (R : E →L[𝕜] F) :
    (c • R).rank ≤ R.rank := by
  refine Submodule.rank_mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨c • x, by simp⟩

/-- Approximation numbers are absolutely homogeneous. -/
theorem approximationNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).approximationNumber n = ‖c‖₊ * T.approximationNumber n := by
  have upper (d : 𝕜) (S : E →L[𝕜] F) :
      (d • S).approximationNumber n ≤ ‖d‖₊ * S.approximationNumber n := by
    by_cases hd : d = 0
    · subst d
      have hz : (0 : E →L[𝕜] F).approximationNumber n = 0 :=
        zero_approximationNumber n
      simpa only [zero_smul, nnnorm_zero, zero_mul] using hz.le
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hdn : ‖d‖₊ ≠ 0 := by simpa using hd
      have hεd : 0 < ε / ‖d‖₊ := div_pos hε (bot_lt_iff_ne_bot.mpr hdn)
      obtain ⟨R, hRrank, hRdist⟩ :=
        S.lt_approximationNumber_add_pos n hεd
      exact le_of_lt <| calc
        (d • S).approximationNumber n ≤ ‖d • S - d • R‖₊ :=
          (d • S).approximationNumber_le ((rank_smul_le_rank d R).trans hRrank)
        _ = ‖d‖₊ * ‖S - R‖₊ := by
          rw [← smul_sub, nnnorm_smul]
        _ < ‖d‖₊ * (S.approximationNumber n + ε / ‖d‖₊) :=
          mul_lt_mul_of_pos_left hRdist (bot_lt_iff_ne_bot.mpr hdn)
        _ = ‖d‖₊ * S.approximationNumber n + ε := by
          rw [mul_add, mul_div_cancel₀ ε hdn]
  by_cases hc : c = 0
  · subst c
    have hz : (0 : E →L[𝕜] F).approximationNumber n = 0 :=
      zero_approximationNumber n
    simpa only [zero_smul, nnnorm_zero, zero_mul] using hz
  apply le_antisymm
  · exact upper c T
  · have hupper := upper c⁻¹ (c • T)
    have hcinv : c⁻¹ • (c • T) = T := by
      rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hcinv, nnnorm_inv] at hupper
    have hnorm_ne : ‖c‖₊ ≠ 0 := by simpa using hc
    calc
      ‖c‖₊ * T.approximationNumber n
          ≤ ‖c‖₊ * (‖c‖₊⁻¹ * (c • T).approximationNumber n) := by
        gcongr
      _ = (c • T).approximationNumber n := by
        rw [← mul_assoc, mul_inv_cancel₀ hnorm_ne, one_mul]


end ContinuousLinearMap

end
