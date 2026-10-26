/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.CanonicalGauge

/-!
# Projection consequences of the canonical min–max API

Tau Ceti owns the coercive-subspace lower bounds and orthogonal-tail min–max
formula. Their duplicate local proofs and real-valued wrappers have been removed.
Consumers use the accepted singular-value statements directly.

The remaining donor results compare projection and restriction norms, express the
norm on the closed unit ball, and bound an approximation number from a spectral band.

## Provenance

The retired min–max proofs originated in
`ForMathlib/Analysis/Normed/Operator/ApproximationNumberMinMax.lean` at DKPS
`fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`. Original authors: Jon Crall and
OpenAI GPT-5.6 Thinking; Kitware, Inc., Apache-2.0. Pre-retirement source remains
in Git history. The surviving projection consequences retain their statements;
this retirement records accepted overlap without inferring historical proof descent.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E₁ : Type v} {F₁ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]

/-- **Compressing by the projection is restricting to the subspace.**  The
orthogonal projection maps the unit ball of `E₁` onto the unit ball of `Vᗮ` and
fixes `Vᗮ`, so the two operator norms coincide. -/
theorem norm_comp_starProjection_orthogonal_eq_norm_comp_subtypeL
    (T : E₁ →L[𝕜] F₁) (V : Submodule 𝕜 E₁) [Vᗮ.HasOrthogonalProjection] :
    ‖T ∘L Vᗮ.starProjection‖ = ‖T ∘L Vᗮ.subtypeL‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hmem : Vᗮ.starProjection x ∈ Vᗮ := Vᗮ.starProjection_apply_mem x
    have hval : (T ∘L Vᗮ.starProjection) x =
        (T ∘L Vᗮ.subtypeL) (⟨Vᗮ.starProjection x, hmem⟩ : Vᗮ) := rfl
    calc ‖(T ∘L Vᗮ.starProjection) x‖
        = ‖(T ∘L Vᗮ.subtypeL) (⟨Vᗮ.starProjection x, hmem⟩ : Vᗮ)‖ := by rw [hval]
      _ ≤ ‖T ∘L Vᗮ.subtypeL‖ * ‖(⟨Vᗮ.starProjection x, hmem⟩ : Vᗮ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T ∘L Vᗮ.subtypeL‖ * ‖x‖ := by
          gcongr
          exact Vᗮ.norm_starProjection_apply_le x
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    have hfix : Vᗮ.starProjection (y : E₁) = (y : E₁) :=
      Vᗮ.starProjection_eq_self_iff.mpr y.2
    have hval : (T ∘L Vᗮ.subtypeL) y = (T ∘L Vᗮ.starProjection) (y : E₁) := by
      simp [ContinuousLinearMap.comp_apply, hfix]
    rw [hval]
    exact ContinuousLinearMap.le_opNorm _ _

/-- **The unit-ball formulation of the orthogonal tail (T09 §B4).**  The tail is
the supremum of `‖T x‖` over the closed unit ball of `Vᗮ`.

Stated on the closed **ball** rather than the unit **sphere**, deliberately: on
`Vᗮ = ⊥` the sphere is empty and its supremum is not the tail, whereas the ball
form holds for every `V`. -/
theorem norm_comp_starProjection_orthogonal_eq_sSup_unitClosedBall
    (T : E₁ →L[𝕜] F₁) (V : Submodule 𝕜 E₁) [Vᗮ.HasOrthogonalProjection] :
    ‖T ∘L Vᗮ.starProjection‖ =
      sSup ((fun x : Vᗮ => ‖T (x : E₁)‖) '' Metric.closedBall 0 1) := by
  rw [T.norm_comp_starProjection_orthogonal_eq_norm_comp_subtypeL V]
  exact ((T ∘L Vᗮ.subtypeL).sSup_unitClosedBall_eq_norm).symm

variable [CompleteSpace E₁]

/-- **A spectral band bounds an approximation number.**

If `P` is an orthogonal projection of rank at most `r` and `T` is bounded by `δ`
off its range, then `aᵣ(T) ≤ δ`.  The competitor is `T ∘L P`, whose rank is at
most `P`'s.

**`0 ≤ δ` is not defensive padding.**  Without it the statement is false: at
`P = 1` the band hypothesis reads `0 ≤ 0` and holds for *any* `δ`, and taking
`r ≥ finrank E` makes the conclusion `0 ≤ δ`, which fails at `δ = -1`.  The
submitted roadmap omitted the hypothesis; it was corrected against this
counterexample, and the two signatures now agree.

`hidem` and `hsa` are used in exactly one place: they make `1 - P` a star
projection, hence a contraction, which is what turns the band bound
`δ * ‖x - P x‖` into `δ * ‖x‖`. -/
theorem approximationNumber_le_of_spectral_band [CompleteSpace F₁]
    {T : E₁ →L[𝕜] F₁} {P : E₁ →L[𝕜] E₁} {r : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hidem : IsIdempotentElem P) (hsa : IsSelfAdjoint P)
    (hrank : P.rank ≤ (r : Cardinal))
    (hband : ∀ x : E₁, ‖T (x - P x)‖ ≤ δ * ‖x - P x‖) :
    T.approximationNumber r ≤ δ := by
  -- `1 - P` is a star projection, hence a contraction.
  have hproj : IsStarProjection (1 - P : E₁ →L[𝕜] E₁) :=
    IsStarProjection.one_sub ⟨hidem, hsa⟩
  have hcontr : ∀ x : E₁, ‖x - P x‖ ≤ ‖x‖ := by
    intro x
    have hle : ‖(1 - P : E₁ →L[𝕜] E₁)‖ ≤ 1 := IsStarProjection.norm_le _ hproj
    calc ‖x - P x‖ = ‖(1 - P : E₁ →L[𝕜] E₁) x‖ := by simp
      _ ≤ ‖(1 - P : E₁ →L[𝕜] E₁)‖ * ‖x‖ := (1 - P : E₁ →L[𝕜] E₁).le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  -- The competitor `T ∘L P` has rank at most `r` and misses by at most `δ`.
  refine le_trans (T.approximationNumber_le_norm_sub (R := T ∘L P) ?_) ?_
  · exact ContinuousLinearMap.rank_comp_le_natCast_right P T hrank
  · refine ContinuousLinearMap.opNorm_le_bound _ hδ fun x => ?_
    have hval : (T - T ∘L P) x = T (x - P x) := by simp
    rw [hval]
    exact (hband x).trans (mul_le_mul_of_nonneg_left (hcontr x) hδ)

end ContinuousLinearMap
