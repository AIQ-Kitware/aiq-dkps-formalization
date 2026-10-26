/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCanonicalSection
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteTransport
public import ForTauCeti.Analysis.OperatorIdeal.SchattenSpectralLimit

/-!
# Exact canonical Schatten costs for compact uniformly acute pairs

Projection-adapted finite sections carry the actual canonical rotation.
Both displacement and directed-sine costs decrease on these sections.
Norm convergence and lower semicontinuity identify the complete ambient
cost, including divergent extended costs and nonseparable fixed sectors.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition Filter
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Truncating a canonical rotation on an actual finite common reducing
block gives exactly the canonical angle cost of the truncated pair. -/
theorem schatten_canonical_truncation_rpow_eq_sine_sum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 ≤ p.toReal)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hacute : IsUniformlyAcute K L)
    (hRM : ∀ x ∈ M, nonacuteDirectRotation K L J x ∈ M)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (V : E ≃ₗᵢ[ℂ] E)
    (hV : ∀ x ∈ M, V x = nonacuteDirectRotation K L J x)
    (hfix : ∀ x ∈ Mᗮ, V x = x) :
    (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
        (1 - (V : E →L[ℂ] E)) ^ p.toReal =
      ∑' j, ENNReal.ofReal (phasePower p.toReal
        (Real.arcsin ((K.sinThetaMap (K.map V.toLinearMap)).singularValue j : ℝ)) 0) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨W, hW, _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
  have hdisp : 1 - (V : E →L[ℂ] E) = M.subtypeL ∘L
      (1 - (W : M →L[ℂ] M)) ∘L M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      change (x : E) - V x = (x : E) - (W x : E)
      rw [hW, hV x x.property]
      rfl
    · intro x hx
      change x - V x = 0
      rw [hfix x hx, sub_self]
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  have hsin := K.sinThetaMap_map_truncation_eq_comp_starProjection L M R V
    hmap hRM hK hL hV hfix
  have hsinext : (K.sinThetaMap L) ∘L M.starProjection = M.subtypeL ∘L
      ((K.comap M.subtype).sinThetaMap (L.comap M.subtype)) ∘L
        M.orthogonalProjectionOnto := by
    apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
    constructor
    · intro x
      change K.sinThetaMap L (M.starProjection (x : E)) = _
      rw [M.starProjection_eq_self_iff.mpr x.property]
      exact (K.sinThetaMap_comap_subtype_apply_of_invariant L M
        hK.mem_invtSubmodule hL.mem_invtSubmodule x).symm
    · intro x hx
      change K.sinThetaMap L (M.starProjection x) = 0
      rw [M.starProjection_apply_eq_zero_iff.mpr hx, map_zero]
  rw [hdisp, OperatorIdealFamily.gauge_orthogonal_extension, hsin, hsinext]
  simp_rw [ContinuousLinearMap.singularValue_orthogonal_extension]
  exact schatten_canonical_restriction_rpow_eq_sine_sum p hp hp1 K L M J hacute W hW
    hK.mem_invtSubmodule hL.mem_invtSubmodule

/-- **Exact infinite-rank canonical cost.** For every finite `p>=1`,
a compact projection difference and uniform acuteness suffice to express
the canonical Schatten displacement power as its intrinsic sine-angle
canonical phase sum. No Schatten membership or separability is assumed. -/
theorem schatten_nonacuteDirectRotation_rpow_eq_canonical_sine_sum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 ≤ p.toReal)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (hacute : IsUniformlyAcute K L) :
    (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
        (1 - nonacuteDirectRotation K L J) ^ p.toReal =
      ∑' j, ENNReal.ofReal (phasePower p.toReal
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)) 0) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  choose V M hM hnorm hK hL hRM hV hfix hcost using fun n : ℕ =>
    exists_finite_canonical_approximation K L J hD (1 / ((n : ℝ) + 1)) (by positivity)
  have hlim : Tendsto (fun n => (V n : E →L[ℂ] E)) atTop (𝓝 (R : E →L[ℂ] E)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)))
  let S (A : E →L[ℂ] E) := (1 - A * K.starProjection * star A) * K.starProjection
  have hS : Continuous S := by dsimp only [S]; fun_prop
  have hsin (W : E ≃ₗᵢ[ℂ] E) : K.sinThetaMap (K.map W.toLinearMap) = S (W : E →L[ℂ] E) := by
    have hproj := (K.map_eq_iff_conjugate_starProjection (K.map W.toLinearMap) W).mp rfl
    rw [Submodule.sinThetaMap_def, Submodule.starProjection_orthogonal, ← hproj]
    rfl
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  let f (s : ℝ≥0) := ENNReal.ofReal (phasePower p.toReal (Real.arcsin (s : ℝ)) 0)
  have hsinR : S (R : E →L[ℂ] E) = K.sinThetaMap L := by
    simpa only [hmap] using (hsin R).symm
  have hp0 : 0 ≤ p.toReal := (zero_le_one : (0 : ℝ) ≤ 1).trans hp1
  have heq (n : ℕ) : (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
        (1 - (V n : E →L[ℂ] E)) ^ p.toReal = ∑' j, f ((S (V n)).singularValue j) := by
    let : FiniteDimensional ℂ (M n) := hM n
    rw [← hsin]
    exact schatten_canonical_truncation_rpow_eq_sine_sum p hp hp1 K L (M n) J hacute
      (hRM n) (hK n) (hL n) (V n) (hV n) (hfix n)
  have hdom (n : ℕ) : (∑' j, f ((S (V n)).singularValue j)) ≤
      ∑' j, f ((S R).singularValue j) := by
    let : FiniteDimensional ℂ (M n) := hM n
    rw [← hsin, hsinR,
      K.sinThetaMap_map_truncation_eq_comp_starProjection L (M n) R (V n) hmap
        (hRM n) (hK n) (hL n) (hV n) (hfix n)]
    apply ENNReal.tsum_le_tsum
    intro j
    apply monotone_sine_canonical_phasePower p.toReal hp0
    calc
      _ ≤ (K.sinThetaMap L).singularValue j * ‖(M n).starProjection‖₊ :=
        ContinuousLinearMap.singularValue_comp_le_right _ _ j
      _ ≤ (K.sinThetaMap L).singularValue j * 1 := by
        gcongr
        exact_mod_cast (M n).starProjection_norm_le
      _ = _ := mul_one _
  have htrace := OperatorIdealFamily.gauge_schatten_rpow_eq_tsum_of_dominated_approximation
    p.toReal hp1 f (continuous_sine_canonical_phasePower p.toReal hp0)
    (1 - (R : E →L[ℂ] E)) (S R)
    (fun n => 1 - (V n : E →L[ℂ] E)) (fun n => S (V n))
    ((continuous_const.sub continuous_id).tendsto _ |>.comp hlim)
    ((hS.tendsto _).comp hlim) heq
    (fun n => ENNReal.rpow_le_rpow (hcost n _) hp0) hdom
  rw [hsinR] at htrace
  exact htrace

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
