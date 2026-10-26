/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.FiniteSpectralCutoff
public import DavisKahan.Geometry.Polar.DirectRotationIdeal
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReplaceFiniteTransport
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite

/-!
# Actual finite spectral phase corrections in a Schatten transport fiber

Optimize the actual restricted pair on a finite sine spectral sector,
and splice that optimizer into a completed canonical rotation. The
result still transports the full Hilbert-space pair, has finite Schatten
cost, agrees with the canonical rotation on the whole complementary
tail, and differs from it by rank at most the cutoff dimension.

The exact cost identity in this theorem is for the finite block only.
Global infinite-rank optimality additionally needs the subcritical-tail
trace identity and an additive cost decomposition; neither is assumed
or asserted here.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A balanced Schatten projection pair admits an actual admissible
phase correction on each finite common reducing block. The finite
block attains its exact phase sum, the canonical tail is preserved,
and the full ambient corrected transport still has finite Schatten cost.
This constructs candidates; it does not assert global tail optimality. -/
theorem exists_schatten_phase_correction_on_finite_block
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 ≤ p.toReal)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hRM : ∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M) :
    let R := nonacuteDirectRotation K L J
    ∃ W : M ≃ₗᵢ[ℂ] M, ∃ U : E ≃ₗᵢ[ℂ] E,
      (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype ∧
      UnitarilyInvariantSeminorm.schatten ℂ M M p (LinearMap.id - W.toLinearMap) ^ p.toReal =
        ∑ i : Fin (Module.finrank ℂ (K.comap M.subtype)), phaseMinimum p.toReal
          ((K.comap M.subtype).principalAngles (L.comap M.subtype) i) ∧
      K.map U.toLinearMap = L ∧ (∀ x : M, U x = (W x : E)) ∧
      (∀ x ∈ Mᗮ, U x = R x) ∧
      (R.toLinearMap - U.toLinearMap).rank ≤ Module.finrank ℂ M ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
        (1 - (U : E →L[ℂ] E)) ≠ ∞ := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hRmap : K.map R.toLinearMap = L := by
    apply (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
    exact nonacuteDirectRotation_reflection_intertwines K L J
  obtain ⟨V, hV, _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
  have hVmap := K.map_comap_subtype_of_isometry_restriction L M R V hRmap hV
  have hdim := V.toLinearEquiv.finrank_map_eq (K.comap M.subtype)
  rw [hVmap] at hdim
  obtain ⟨W, hWmap, hWcost⟩ := exists_unitary_attaining_schatten_principalAngles_complex
    p hp (K.comap M.subtype) (L.comap M.subtype) hdim.symm
  obtain ⟨U, hUmap, hUM, hUperp, hRank⟩ :=
    K.exists_transport_replacing_finite_block L M hK R hRmap hRM W hWmap
  refine ⟨W, U, hWmap, hWcost, hUmap, hUM, hUperp, hRank, ?_⟩
  have hRcost : Φ.gauge (1 - (R : E →L[ℂ] E)) ≠ ∞ :=
    (gauge_nonacuteDirectRotation_ne_top_iff_projection_sub Φ K L J).mpr hD
  have hupdate : Φ.gauge ((R : E →L[ℂ] E) - (U : E →L[ℂ] E)) ≠ ∞ :=
    OperatorIdealFamily.gauge_schatten_ne_top_of_rank_le p.toReal hp1 _
      (Module.finrank ℂ M) hRank
  have hsum : Φ.gauge (1 - (R : E →L[ℂ] E)) +
      Φ.gauge ((R : E →L[ℂ] E) - (U : E →L[ℂ] E)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hRcost, hupdate⟩
  apply ne_top_of_le_ne_top hsum
  have h := Φ.gauge_add_le (1 - (R : E →L[ℂ] E))
    ((R : E →L[ℂ] E) - (U : E →L[ℂ] E))
  rwa [sub_add_sub_cancel] at h

/-- **An optimized finite sector in the actual infinite transport
fiber.** At `1<p<2`, every positive sine cutoff admits a finite-cost
ambient transport whose cutoff restriction is a global finite-block
minimizer, whose tail equals the completed canonical rotation, and
whose update rank is at most the cutoff dimension. Minimality here is
explicitly only for the restricted block, not the full ambient cost. -/
theorem exists_schatten_phase_correction_on_sine_cutoff
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (c : ℝ) (hc : 0 < c) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    let R := nonacuteDirectRotation K L J
    ∃ W : M ≃ₗᵢ[ℂ] M, ∃ U : E ≃ₗᵢ[ℂ] E,
      (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype ∧
      (∀ V : M ≃ₗᵢ[ℂ] M,
        (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype →
        (∑' k, ((1 - (W : M →L[ℂ] M)).singularValue k : ℝ≥0∞) ^ p.toReal) ≤
          ∑' k, ((1 - (V : M →L[ℂ] M)).singularValue k : ℝ≥0∞) ^ p.toReal) ∧
      K.map U.toLinearMap = L ∧ (∀ x : M, U x = (W x : E)) ∧
      (∀ x ∈ Mᗮ, U x = R x) ∧
      (R.toLinearMap - U.toLinearMap).rank ≤ Module.finrank ℂ M ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E)) ≠ ∞ := by
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    p.toReal hp1.le (K.starProjection - L.starProjection) hD
  obtain ⟨hM, hK, _, _⟩ := finite_sine_spectral_cutoff K L hcompact c hc
  let : FiniteDimensional ℂ M := hM
  have hRM : ∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M :=
    (sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hcompact c hc).mem_invtSubmodule
  obtain ⟨W, U, hWmap, hWcost, hUmap, hUM, hUperp, hRank, hfinite⟩ :=
    exists_schatten_phase_correction_on_finite_block p hp hp1.le K L M J hD hK hRM
  refine ⟨W, U, hWmap, ?_, hUmap, hUM, hUperp, hRank, hfinite⟩
  intro V hVmap
  have hvalue (X : M ≃ₗᵢ[ℂ] M) :
      (∑' k, ((1 - (X : M →L[ℂ] M)).singularValue k : ℝ≥0∞) ^ p.toReal) =
        ENNReal.ofReal (UnitarilyInvariantSeminorm.schatten ℂ M M p
          (LinearMap.id - X.toLinearMap) ^ p.toReal) := by
    rw [← OperatorIdealFamily.gauge_schatten_rpow p.toReal hp1.le,
      OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp]
    rfl
  rw [hvalue W, hvalue V, hWcost]
  apply ENNReal.ofReal_le_ofReal
  exact sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2
    (K.comap M.subtype) (L.comap M.subtype) (Unitary.linearIsometryEquiv.symm V)
    (by simpa only [MulEquiv.apply_symm_apply] using hVmap)

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
