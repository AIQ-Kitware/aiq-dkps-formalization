/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionUniqueness

/-!
# Exact Schatten correction of an approximate two-level symmetry

For the self-adjoint operator `H = gap * P + energy * I`, a Schatten
commutator and an operator-norm residual at most
`gap * 2 * sqrt(p-1) / p` certify a unique Schatten-nearest unitary
commuting exactly with `H`. The positive gap removes any separate
index-balance assumption. The ambient Hilbert space can be infinite.
This is a deterministic nearness theorem, with no implementation,
physical accessibility or statistical guarantee asserted.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **A gap-scaled commutator certificate for unique nearest exact
symmetry.** The two-level form may have trivial eigenspaces; no finite
dimension, finite-rank perturbation, separate defect balance or candidate
block restriction is imposed. All ambient unitary exact symmetries are
included as competitors. -/
theorem exists_unique_nearest_schatten_two_level_symmetry
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (energy gap : ℝ) (hgap : 0 < gap)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * (gap • K.starProjection + energy • 1) -
        (gap • K.starProjection + energy • 1) * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * (gap • K.starProjection + energy • 1) -
        (gap • K.starProjection + energy • 1) * (A : E →L[ℂ] E)‖ ≤
      gap * (2 * Real.sqrt (p.toReal - 1) / p.toReal)) :
    let H : E →L[ℂ] E := gap • K.starProjection + energy • 1
    IsSelfAdjoint H ∧
      ∃! C : E ≃ₗᵢ[ℂ] E, Commute (C : E →L[ℂ] E) H ∧
        ∀ W : E ≃ₗᵢ[ℂ] E, Commute (W : E →L[ℂ] E) H →
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
              ((A : E →L[ℂ] E) - (C : E →L[ℂ] E)) ≤
            (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
              ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)) := by
  let H : E →L[ℂ] E := gap • K.starProjection + energy • 1
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  have hscale (B : E →L[ℂ] E) :
      B * H - H * B = gap • (B * K.starProjection - K.starProjection * B) := by
    dsimp only [H]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_sub]
    abel
  have hcommute (B : E →L[ℂ] E) : Commute B H ↔ Commute B K.starProjection := by
    rw [commute_iff_eq, ← sub_eq_zero, hscale, smul_eq_zero]
    simp only [ne_of_gt hgap, false_or, sub_eq_zero, commute_iff_eq]
  have hback : (A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E) =
      ((gap : ℂ)⁻¹) • ((A : E →L[ℂ] E) * H - H * (A : E →L[ℂ] E)) := by
    rw [hscale, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    change _ = ((gap : ℂ)⁻¹ * (gap : ℂ)) • _
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hgap)), one_smul]
  have hPfinite : Φ.gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞ := by
    rw [hback, Φ.gauge_smul]
    exact ENNReal.mul_ne_top enorm_ne_top hcomm
  have hPnorm : ‖(A : E →L[ℂ] E) * K.starProjection -
      K.starProjection * (A : E →L[ℂ] E)‖ ≤ Real.sin (criticalAngle p.toReal) := by
    change ‖(A : E →L[ℂ] E) * H - H * (A : E →L[ℂ] E)‖ ≤ _ at hnorm
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hgap] at hnorm
    rw [sin_criticalAngle p.toReal hp1]
    exact (mul_le_mul_iff_right₀ hgap).mp hnorm
  have hH : IsSelfAdjoint H :=
    ((IsSelfAdjoint.all gap).smul (isSelfAdjoint_starProjection K)).add
      ((IsSelfAdjoint.all energy).smul (IsSelfAdjoint.one (E →L[ℂ] E)))
  obtain ⟨C, hC, huniq⟩ :=
    exists_unique_nearest_schatten_commuting_unitary_of_commutator_le_critical
      p hp hp1 hp2 K A hPfinite hPnorm
  refine ⟨hH, C, ⟨(hcommute _).mpr hC.1, ?_⟩, ?_⟩
  · intro W hW
    exact hC.2 W ((hcommute _).mp hW)
  · intro V hV
    apply huniq V
    exact ⟨(hcommute _).mp hV.1, fun W hW => hV.2 W ((hcommute _).mpr hW)⟩

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
