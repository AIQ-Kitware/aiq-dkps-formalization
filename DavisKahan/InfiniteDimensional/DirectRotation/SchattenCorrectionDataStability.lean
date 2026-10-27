/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCorrectionUniqueness
public import DavisKahan.Geometry.Polar.CommutingCorrectionStability

/-!
# Certified data stability of nearest Schatten commuting corrections

The unique nearest projection-commuting correction in the closed
canonical regime depends Lipschitz-continuously on the input unitary.
The estimate compares actual global minimizers against all ambient
commuting unitaries and is independent of Hilbert dimension.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Input-unitary error controls the error of every nearest commuting
correction. Both commutators must be native Schatten, and their norms
must lie in the closed canonical regime. Candidate finite cost, rank,
index balance and separability are not assumed. -/
theorem norm_nearest_schatten_corrections_sub_le_of_commutator_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A B C D : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hD : Commute (D : E →L[ℂ] E) K.starProjection)
    (hcommA : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hcommB : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((B : E →L[ℂ] E) * K.starProjection - K.starProjection * (B : E →L[ℂ] E)) ≠ ∞)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hcrit : gamma ≤ Real.sin (criticalAngle p.toReal))
    (hA : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤ gamma)
    (hB : ‖(B : E →L[ℂ] E) * K.starProjection - K.starProjection * (B : E →L[ℂ] E)‖ ≤ gamma)
    (hminA : IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)))
      {W | Commute (W : E →L[ℂ] E) K.starProjection} C)
    (hminB : IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((B : E →L[ℂ] E) - (W : E →L[ℂ] E)))
      {W | Commute (W : E →L[ℂ] E) K.starProjection} D) :
    ‖(C : E →L[ℂ] E) - (D : E →L[ℂ] E)‖ ≤
      ‖(A : E →L[ℂ] E) - (B : E →L[ℂ] E)‖ / Real.sqrt (1 - gamma ^ 2) := by
  have hCeq := eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    p hp hp1 hp2 K A C hC hcommA (hA.trans hcrit) (fun _ hW => hminA hW)
  have hDeq := eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    p hp hp1 hp2 K B D hD hcommB (hB.trans hcrit) (fun _ hW => hminB hW)
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hs1 : Real.sin (criticalAngle p.toReal) < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hc.1, Real.pi_pos], hc.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hc.2
    simpa only [Real.sin_pi_div_two] using h
  exact norm_canonical_corrections_sub_le_of_commutator_norm_le K A B C D hCeq hDeq
    gamma hgamma (hcrit.trans_lt hs1) hA hB

/-- At and below the exact Schatten critical threshold, correction is
data-Lipschitz with the explicit constant `p/(2-p)`. -/
theorem norm_nearest_schatten_corrections_sub_le_at_closed_critical_commutator
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A B C D : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hD : Commute (D : E →L[ℂ] E) K.starProjection)
    (hcommA : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hcommB : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((B : E →L[ℂ] E) * K.starProjection - K.starProjection * (B : E →L[ℂ] E)) ≠ ∞)
    (hA : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal))
    (hB : ‖(B : E →L[ℂ] E) * K.starProjection - K.starProjection * (B : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal))
    (hminA : IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)))
      {W | Commute (W : E →L[ℂ] E) K.starProjection} C)
    (hminB : IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((B : E →L[ℂ] E) - (W : E →L[ℂ] E)))
      {W | Commute (W : E →L[ℂ] E) K.starProjection} D) :
    ‖(C : E →L[ℂ] E) - (D : E →L[ℂ] E)‖ ≤
      p.toReal / (2 - p.toReal) * ‖(A : E →L[ℂ] E) - (B : E →L[ℂ] E)‖ := by
  let theta := criticalAngle p.toReal
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hs : 0 ≤ Real.sin theta := (Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2, Real.pi_pos])).le
  have h := norm_nearest_schatten_corrections_sub_le_of_commutator_norm_le
    p hp hp1 hp2 K A B C D hC hD hcommA hcommB (Real.sin theta) hs le_rfl hA hB hminA hminB
  have hcos : 0 < Real.cos theta := by
    rw [show Real.cos theta = (2 - p.toReal) / p.toReal from cos_criticalAngle _ hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hroot : Real.sqrt (1 - Real.sin theta ^ 2) = (2 - p.toReal) / p.toReal := by
    rw [show 1 - Real.sin theta ^ 2 = Real.cos theta ^ 2 by nlinarith [Real.sin_sq_add_cos_sq theta],
      Real.sqrt_sq hcos.le]
    exact cos_criticalAngle _ hp1 hp2
  rw [hroot] at h
  calc
    _ ≤ ‖(A : E →L[ℂ] E) - (B : E →L[ℂ] E)‖ / ((2 - p.toReal) / p.toReal) := h
    _ = _ := by
      rw [div_div_eq_mul_div]
      ring

private theorem eq_diagonal_factor_of_nearest
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A C : E ≃ₗᵢ[ℂ] E)
    (hC : Commute (C : E →L[ℂ] E) K.starProjection)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal))
    (hmin : IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)))
      {W | Commute (W : E →L[ℂ] E) K.starProjection} C) :
    (C : E →L[ℂ] E) = (K.diagBlock (A : E →L[ℂ] E)).factorThru
      (K.diagBlock (A : E →L[ℂ] E)).modulus := by
  have hCeq := eq_canonical_correction_of_schatten_minimal_of_commutator_le_critical
    p hp hp1 hp2 K A C hC hcomm hnorm (fun _ hW => hmin hW)
  let theta := criticalAngle p.toReal
  have hcos : 0 < Real.cos theta := by
    rw [show Real.cos theta = (2 - p.toReal) / p.toReal from cos_criticalAngle _ hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  exact canonical_correction_eq_diagBlock_factorThru_modulus K A C hCeq _ hcos
    (by nlinarith [Real.sin_sq_add_cos_sq theta])

/-- Exact construction of every nearest commuting correction in the
closed canonical regime. The right side uses Tau Ceti's accepted factor
through the modulus of `PAP + Pperp A Pperp`; feasibility and global
minimality are equivalent to this literal operator equality. -/
theorem schatten_correction_isMin_iff_eq_diagBlock_factorThru_modulus
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[ℂ] E)
    (hcomm : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      ((A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)) ≠ ∞)
    (hnorm : ‖(A : E →L[ℂ] E) * K.starProjection - K.starProjection * (A : E →L[ℂ] E)‖ ≤
      Real.sin (criticalAngle p.toReal)) (C : E ≃ₗᵢ[ℂ] E) :
    (Commute (C : E →L[ℂ] E) K.starProjection ∧
      IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)))
        {W | Commute (W : E →L[ℂ] E) K.starProjection} C) ↔
      (C : E →L[ℂ] E) = (K.diagBlock (A : E →L[ℂ] E)).factorThru
        (K.diagBlock (A : E →L[ℂ] E)).modulus := by
  constructor
  · rintro ⟨hC, hmin⟩
    exact eq_diagonal_factor_of_nearest p hp hp1 hp2 K A C hC hcomm hnorm hmin
  · intro hC
    obtain ⟨D, hD, _⟩ := exists_unique_nearest_schatten_commuting_unitary_of_commutator_le_critical
      p hp hp1 hp2 K A hcomm hnorm
    have hminD : IsMinOn (fun W : E ≃ₗᵢ[ℂ] E =>
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge ((A : E →L[ℂ] E) - (W : E →L[ℂ] E)))
        {W | Commute (W : E →L[ℂ] E) K.starProjection} D := by
      intro W hW
      exact hD.2 W hW
    have heq := eq_diagonal_factor_of_nearest p hp hp1 hp2 K A D hD.1 hcomm hnorm hminD
    have hCD : C = D := by
      ext x
      exact congrArg (fun T : E →L[ℂ] E => T x) (hC.trans heq.symm)
    subst C
    exact ⟨hD.1, hminD⟩

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
