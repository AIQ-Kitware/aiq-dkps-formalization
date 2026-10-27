/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenOptimizerTail

/-!
# Every complex Hilbert-space Schatten optimizer

For `1<p<2`, a Schatten projection pair with an actual crossed-defect
completion has precisely the following global optimizers: canonical
action on the infinite inactive tail, and a finite compatible phase
projection with arbitrary reflecting right-defect unitary on the
remaining angle sector. All competitors are ambient unitaries.
Finite cost and the block structure are conclusions of optimality.
No separability, finite-rank pair or angle simplicity is assumed.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Complete unrestricted Hilbert-space optimizer classification.**
On the entire inactive sector every optimizer is canonical. On the
finite remaining sector, all and only compatible phase projections
and reflecting crossed-defect unitaries occur. The transporter need
not be assumed to have finite cost or preserve any angle block. -/
theorem schatten_transport_isMin_iff_canonical_tail_phase_and_defect_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
        (K.starProjection - L.starProjection) hD) c hc).1
    let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E))) ↔
      (∀ x ∈ Mᗮ, U x = nonacuteDirectRotation K L J x) ∧
      ∃ (V : M ≃ₗᵢ[ℂ] M) (hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀),
        (∀ x : M, (V x : E) = U x) ∧ K₀.map V.toLinearMap = L₀ ∧
        let R₀ := Unitary.linearIsometryEquiv
          (⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
            nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩ :
              unitary (M →L[ℂ] M))
        let C₀ := Proposition35.section3CosAngleOperator K₀ L₀
        let F₀ := schattenPhaseFactor p.toReal C₀
        ∃ P : M →L[ℂ] M, IsStarProjection P ∧ Commute P (R₀ : M →L[ℂ] M) ∧
          (∀ x, P (K₀.reflection x) = K₀.reflection (P x)) ∧
          ∃ D : halmosSourceDefect K₀ L₀ ≃ₗᵢ[ℂ] halmosTargetDefect K₀ L₀,
            (∀ x : halmosSourceDefect K₀ L₀, V x = (D x : M)) ∧
            (∀ y : halmosTargetDefect K₀ L₀, V y = (D.symm y : M)) ∧
            C₀ * (V.trans R₀.symm : M →L[ℂ] M) = C₀ * (F₀ * P + star F₀ * (1 - P)) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
    (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
      (K.starProjection - L.starProjection) hD) c hc).1
  constructor
  · intro hmin
    obtain ⟨T, hTmap, _, _, hTfinite, _, _⟩ :=
      exists_schatten_minimizer_by_finite_correction p hp hp1 hp2 K L J hD c hc hc1 hcrit
    have hfinite := ne_top_of_le_ne_top hTfinite (hmin T hTmap)
    have htail := apply_eq_nonacuteDirectRotation_on_inactive_tail_of_schatten_minimal
      p hp hp1 hp2 K L J hD c hc hc1 hcrit U hmap hfinite hmin
    obtain ⟨V, hdim, hV, hlocal, hiff⟩ :=
      schatten_minimal_iff_cutoff_phase_and_defect_of_canonical_tail p hp hp1 hp2 K L J hD
        c hc hc1 hcrit U hmap hfinite htail
    exact ⟨htail, V, hdim, hV, hlocal, hiff.mp hmin⟩
  · rintro ⟨htail, V, hdim, hV, hlocal, hphase⟩
    have hfinite :=
      ContinuousLinearMap.gauge_schatten_displacement_ne_top_of_finite_restriction_and_ideal_tail
        p.toReal hp1.le M U
      (nonacuteDirectRotation K L J) V hV htail
      ((gauge_nonacuteDirectRotation_ne_top_iff_projection_sub
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le) K L J).mpr hD)
    obtain ⟨V', hdim', hV', _, hiff⟩ :=
      schatten_minimal_iff_cutoff_phase_and_defect_of_canonical_tail p hp hp1 hp2 K L J hD
        c hc hc1 hcrit U hmap hfinite htail
    have heq : V' = V := by
      ext x
      exact (hV' x).trans (hV x).symm
    subst V'
    exact hiff.mpr hphase

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
