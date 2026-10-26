/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.CanonicalApproximation
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCanonicalOptimality
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteCore

/-!
# Exact canonical Schatten costs on actual finite sections

An actual finite unitary restriction of a uniformly acute ambient
canonical rotation has precisely the canonical scalar cost of the
restricted pair. All finite exponents at least one are included.
The cost uses the native operator-ideal gauge and intrinsic sine
singular values, so it is ready for passage to Hilbert-space limits.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The canonical scalar cost is nonnegative throughout the physical
angle interval, for every real exponent. -/
theorem canonical_phasePower_nonneg (p theta : ℝ)
    (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ phasePower p theta 0 := by
  have hsin : 0 ≤ Real.sin (theta / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  simp only [phasePower, add_zero, sub_zero]
  exact add_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hsin) _)
    (Real.rpow_nonneg (mul_nonneg (by norm_num) hsin) _)

omit [CompleteSpace E] in
/-- The canonical angle penalty is continuous as a function of a sine
singular value, including zero and the right-angle endpoint. -/
theorem continuous_sine_canonical_phasePower (p : ℝ) (hp : 0 ≤ p) :
    Continuous (fun s : ℝ≥0 => ENNReal.ofReal (phasePower p (Real.arcsin (s : ℝ)) 0)) := by
  have hbase : Continuous (fun s : ℝ≥0 => 2 * Real.sin (Real.arcsin (s : ℝ) / 2)) := by
    fun_prop
  have hpow := (Real.continuous_rpow_const hp).comp hbase
  simpa only [Function.comp_def, Pi.add_apply, phasePower, phaseChord, add_zero, sub_zero] using
    ENNReal.continuous_ofReal.comp (hpow.add hpow)

omit [CompleteSpace E] in
/-- The canonical spectral penalty is monotone in the sine value. -/
theorem monotone_sine_canonical_phasePower (p : ℝ) (hp : 0 ≤ p) :
    Monotone (fun s : ℝ≥0 => ENNReal.ofReal (phasePower p (Real.arcsin (s : ℝ)) 0)) := by
  intro a b hab
  have ha0 : 0 ≤ Real.arcsin (a : ℝ) := Real.arcsin_nonneg.mpr a.coe_nonneg
  have hb0 : 0 ≤ Real.arcsin (b : ℝ) := Real.arcsin_nonneg.mpr b.coe_nonneg
  have hsin : Real.sin (Real.arcsin (a : ℝ) / 2) ≤
      Real.sin (Real.arcsin (b : ℝ) / 2) :=
    Real.monotoneOn_sin
      ⟨by linarith [Real.pi_pos], by linarith [Real.arcsin_le_pi_div_two (a : ℝ)]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.arcsin_le_pi_div_two (b : ℝ)]⟩
      (div_le_div_of_nonneg_right (Real.arcsin_le_arcsin hab) (by norm_num))
  have hnonneg : 0 ≤ 2 * Real.sin (Real.arcsin (a : ℝ) / 2) :=
    mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.arcsin_le_pi_div_two (a : ℝ), Real.pi_pos]))
  have hpow := Real.rpow_le_rpow hnonneg
    (mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 2)) hp
  apply ENNReal.ofReal_le_ofReal
  simp only [phasePower, phaseChord, add_zero, sub_zero]
  exact add_le_add hpow hpow

/-- **Exact cost of an actual canonical finite section.** The retained
unitary is identified with the canonical rotation of the restricted
pair before applying the finite principal-angle cost formula. -/
theorem schatten_canonical_restriction_rpow_eq_sine_sum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 ≤ p.toReal)
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional ℂ M]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hacute : IsUniformlyAcute K L)
    (V : M ≃ₗᵢ[ℂ] M)
    (hV : ∀ x : M, (V x : E) = nonacuteDirectRotation K L J x)
    (hK : ∀ x ∈ M, K.starProjection x ∈ M)
    (hL : ∀ x ∈ M, L.starProjection x ∈ M) :
    (OperatorIdealFamily.schatten ℂ p.toReal hp1).gauge
        (1 - (V : M →L[ℂ] M)) ^ p.toReal =
      ∑' j, ENNReal.ofReal (phasePower p.toReal
        (Real.arcsin (((K.comap M.subtype).sinThetaMap
          (L.comap M.subtype)).singularValue j : ℝ)) 0) := by
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L J, nonacuteDirectRotation_mem_unitary K L J⟩ :
      unitary (E →L[ℂ] E))
  have hmap : K.map R.toLinearMap = L :=
    (Submodule.map_eq_iff_intertwines_reflection K L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L J)
  have hlocal : K₀.map V.toLinearMap = L₀ :=
    K.map_comap_subtype_of_isometry_restriction L M R V hmap hV
  have hdim : Module.finrank ℂ K₀ = Module.finrank ℂ L₀ := by
    have h := V.toLinearEquiv.finrank_map_eq K₀
    rw [hlocal] at h
    exact h.symm
  have hacute₀ : IsUniformlyAcute K₀ L₀ :=
    (K.projectionGap_comap_subtype_le_of_invariant L M hK hL).trans_lt hacute
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute₀
  have hcanonical : (V : M →L[ℂ] M) =
      nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hdim) := by
    calc
      _ = spectraCanonicalPolarFactor K₀ L₀ :=
        nonacuteDirectRotation_restriction_eq_canonicalPolarFactor_of_acute
          K L M J V hV hK hz hz'
      _ = _ := (nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K₀ L₀
        (finiteCrossedDefectEquiv K₀ L₀ hdim) hz hz').symm
  have hlin : (1 - (V : M →L[ℂ] M)).toLinearMap = LinearMap.id -
      (nonacuteDirectRotation K₀ L₀ (finiteCrossedDefectEquiv K₀ L₀ hdim)).toLinearMap := by
    rw [hcanonical]
    rfl
  have hp0 : p.toReal ≠ 0 := by linarith
  have hf : ENNReal.ofReal (phasePower p.toReal 0 0) = 0 := by
    simp [phasePower, phaseChord, Real.zero_rpow hp0]
  rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp, hlin,
    nonacuteDirectRotation_schatten_rpow_eq_sum_complex p hp K₀ L₀ hdim,
    OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
      (fun s => ENNReal.ofReal (phasePower p.toReal (Real.arcsin (s : ℝ)) 0))
      (by simpa only [NNReal.coe_zero, Real.arcsin_zero] using hf)]
  simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
  have hnonneg (i : Fin (Module.finrank ℂ K₀)) :
      0 ≤ phasePower p.toReal (K₀.principalAngles L₀ i) 0 :=
    canonical_phasePower_nonneg _ _
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
  exact Submodule.sum_principalAngles_eq_sum_singularValues_arcsin K₀ L₀
    (fun t => ENNReal.ofReal (phasePower p.toReal t 0)) hf

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
