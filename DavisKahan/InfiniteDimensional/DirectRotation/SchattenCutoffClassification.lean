/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenGlobalAttainment
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNonacuteClassification
public import ForTauCeti.Analysis.InnerProductSpace.SchattenMinimizerRestriction
public import ForTauCeti.Analysis.InnerProductSpace.UnitaryTailAgreement

/-!
# Exact classification within the canonical-tail family

For a transporter with the actual canonical action on a subcritical
cutoff tail, unrestricted ambient minimality is equivalent to minimality
of its actual finite restriction. The complete finite phase/defect
classification applies to that restriction, including multiplicities and
right angles. Competitors in the ambient minimum remain unrestricted.

This theorem assumes the competitor's canonical tail action. Proving that
every ambient optimizer has this action is a separate necessity theorem;
it cannot be inferred from existence of a canonical-tail optimizer.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Canonical-tail reduction of the full ambient minimum.** The
actual finite restriction is globally optimal precisely when the
original transporter is globally optimal. Only the transporter being
classified is assumed to have canonical tail action; competing ambient
unitaries have no block or tail restriction. -/
theorem schatten_minimal_iff_finite_restriction_of_canonical_tail
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (htail : ∀ x ∈ (eigenSpan (K.sinAngleOperator L) (Set.Ioi c))ᗮ,
      U x = nonacuteDirectRotation K L J x) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
        (K.starProjection - L.starProjection) hD) c hc).1
    ∃ V : M ≃ₗᵢ[ℂ] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ((∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E))) ↔
      (∀ W : M ≃ₗᵢ[ℂ] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        UnitarilyInvariantSeminorm.schatten ℂ M M p (LinearMap.id - V.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℂ M M p (LinearMap.id - W.toLinearMap) ^ p.toReal)) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hRred : M.IsReducing R.toLinearMap :=
    sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hcompact c hc
  have hUred : M.IsReducing U.toLinearMap := U.isReducing_of_eq_on_orthogonal R M hRred htail
  obtain ⟨V, hV, _, _⟩ := U.exists_restriction_of_finite_invariant M hUred.mem_invtSubmodule
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M U V hmap hV
  obtain ⟨T, hTmap, hTtail, _, _, _, hTmin⟩ :=
    exists_schatten_minimizer_by_finite_correction p hp hp1 hp2 K L J hD c hc hc1 hcrit
  have hTred : M.IsReducing T.toLinearMap := T.isReducing_of_eq_on_orthogonal R M hRred hTtail
  have hiff := schatten_minimal_iff_restriction_of_minimizing_reference_tail p.toReal hp1.le
    K L M U T hmap hTmap hfinite hTmin hK hTred.mem_invtSubmodule
    (fun x hx => (htail x hx).trans (hTtail x hx).symm) V hV
  have hvalue (W : M ≃ₗᵢ[ℂ] M) :
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (W : M →L[ℂ] M)) ^ p.toReal =
        ENNReal.ofReal (UnitarilyInvariantSeminorm.schatten ℂ M M p
          (LinearMap.id - W.toLinearMap) ^ p.toReal) := by
    rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp]
    rfl
  refine ⟨V, hV, hlocal, hiff.trans ?_⟩
  constructor
  · intro hmin W hW
    have h := ENNReal.rpow_le_rpow (hmin W hW) (zero_lt_one.trans hp1).le
    rw [hvalue V, hvalue W] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  · intro hmin W hW
    apply (ENNReal.rpow_le_rpow_iff (zero_lt_one.trans hp1)).mp
    rw [hvalue V, hvalue W]
    exact ENNReal.ofReal_le_ofReal (hmin W hW)

/-- **Phase/defect classification for a canonical-tail transporter.**
Every finite compatible phase projection and every reflecting unitary
on the right-angle defects occur exactly as in the complete finite
classification. The canonical tail hypothesis remains explicit. -/
theorem schatten_minimal_iff_cutoff_phase_and_defect_of_canonical_tail
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal))
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (htail : ∀ x ∈ (eigenSpan (K.sinAngleOperator L) (Set.Ioi c))ᗮ,
      U x = nonacuteDirectRotation K L J x) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let _ : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L
      (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
        (K.starProjection - L.starProjection) hD) c hc).1
    let K₀ := K.comap M.subtype
    let L₀ := L.comap M.subtype
    ∃ (V : M ≃ₗᵢ[ℂ] M) (hKL : Module.finrank ℂ K₀ = Module.finrank ℂ L₀),
      (∀ x : M, (V x : E) = U x) ∧ K₀.map V.toLinearMap = L₀ ∧
      let R₀ := Unitary.linearIsometryEquiv
        (⟨nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL),
          nonacuteDirectRotation_mem_unitary K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hKL)⟩ :
            unitary (M →L[ℂ] M))
      let C₀ := Proposition35.section3CosAngleOperator K₀ L₀
      let F₀ := schattenPhaseFactor p.toReal C₀
      (∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E))) ↔
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
  obtain ⟨V, hV, hlocal, hiff⟩ :=
    schatten_minimal_iff_finite_restriction_of_canonical_tail p hp hp1 hp2 K L J hD
      c hc hc1 hcrit U hmap hfinite htail
  have hdim : Module.finrank ℂ (K.comap M.subtype) = Module.finrank ℂ (L.comap M.subtype) := by
    have h := V.toLinearEquiv.finrank_map_eq (K.comap M.subtype)
    rw [hlocal] at h
    exact h.symm
  exact ⟨V, hdim, hV, hlocal, hiff.trans
    (schatten_transport_isMin_iff_phase_and_defect_complex p hp hp1 hp2
      (K.comap M.subtype) (L.comap M.subtype) hdim V hlocal)⟩

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
