/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle
import DavisKahan.FiniteDimensional.DirectRotation.SchattenStationarity

/-!
# The two spectral roots of the Schatten unitary gradient

The argument-free unitary gradient symbol agrees with `p * phaseAmplitude`
on positive principal phases. Thus its positive spectral levels have two
branches, separated by the scalar critical angle. This connects the compiled
stationarity identity to the scalar optimization calculus.
-/

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set

noncomputable section

/-- On positive principal phases, the matrix-gradient symbol is exactly
the amplitude already used in scalar phase optimization. -/
theorem schattenPhaseDerivative_exp_eq_amplitude (p t : ℝ)
    (ht : t ∈ Ioo 0 Real.pi) :
    schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) =
      p * phaseAmplitude p t := by
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have hc := phaseChord_pos ht.1 ht.2
  have hpow : phaseChord t ^ (p - 2) * phaseChord t = phaseChord t ^ (p - 1) := by
    rw [← Real.rpow_add_one hc.ne']
    congr 1
    ring
  rw [schattenPhaseDerivative_exp, abs_of_pos hs]
  change p * phaseChord t ^ (p - 2) * Real.sin t = _
  have hsin : Real.sin t = phaseChord t * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := by congr 1; ring
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) := Real.sin_two_mul _
      _ = _ := rfl
  rw [hsin, phaseAmplitude]
  calc
    _ = p * Real.cos (t / 2) * (phaseChord t ^ (p - 2) * phaseChord t) := by ring
    _ = _ := by rw [hpow]; ring

/-- The phase-gradient derivative on the positive principal range is
the scalar curvature used in the two-phase operator variation. -/
theorem schattenPhaseDerivative_exp_hasDerivAt (p t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt (fun u : ℝ => schattenPhaseDerivative p (Complex.exp ((u : ℂ) * Complex.I)))
      (p * amplitudeDerivative p t) t := by
  have hd := (phaseAmplitude_hasDerivAt p t (phaseChord_pos ht.1 ht.2)).const_mul p
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact schattenPhaseDerivative_exp_eq_amplitude p u hu

/-- A positive gradient level can only come from a positive interior
principal phase. The endpoint phases `0` and `pi` have zero symbol. -/
theorem principal_phase_pos_of_schattenPhaseDerivative_pos
    (p t : ℝ) (hp : 0 < p) (ht : |t| ≤ Real.pi)
    (hg : 0 < schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I))) :
    t ∈ Ioo 0 Real.pi := by
  rw [schattenPhaseDerivative_exp] at hg
  have hcoef : 0 ≤ p * (2 * |Real.sin (t / 2)|) ^ (p - 2) :=
    mul_nonneg hp.le (Real.rpow_nonneg (by positivity) _)
  have hsin : 0 < Real.sin t := by
    by_contra h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hcoef (le_of_not_gt h))) hg
  have ht0 : 0 < t := by
    by_contra h
    have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h)
      (by linarith [neg_abs_le t])
    exact (not_lt_of_ge hs) hsin
  refine ⟨ht0, lt_of_le_of_ne (le_trans (le_abs_self t) ht) ?_⟩
  intro heq
  rw [heq, Real.sin_pi] at hsin
  exact lt_irrefl 0 hsin

/-- Every positive gradient level below its maximum has exactly one
positive phase on each side of the critical angle. -/
theorem schattenPhaseDerivative_two_roots (p g : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p)) :
    (∃! a, a ∈ Ioo 0 (criticalAngle p) ∧
      schattenPhaseDerivative p (Complex.exp ((a : ℂ) * Complex.I)) = g) ∧
    (∃! b, b ∈ Ioo (criticalAngle p) Real.pi ∧
      schattenPhaseDerivative p (Complex.exp ((b : ℂ) * Complex.I)) = g) := by
  have hp0 : 0 < p := by linarith
  have hcrit := criticalAngle_mem p hp1 hp2
  obtain ⟨ha, hb⟩ := phaseAmplitude_two_roots p (g / p) hp1 hp2
    (div_pos hg0 hp0) ((div_lt_iff₀ hp0).2 (by simpa only [mul_comm] using hgm))
  have heq (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
      schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
        phaseAmplitude p t = g / p := by
    rw [schattenPhaseDerivative_exp_eq_amplitude p t ht,
      eq_div_iff hp0.ne', mul_comm]
  constructor
  · obtain ⟨a, ha, huniq⟩ := ha
    refine ⟨a, ⟨ha.1, (heq a ⟨ha.1.1, by linarith [ha.1.2, hcrit.2, Real.pi_pos]⟩).2 ha.2⟩, ?_⟩
    intro t ht
    exact huniq t ⟨ht.1, (heq t ⟨ht.1.1, by linarith [ht.1.2, hcrit.2, Real.pi_pos]⟩).1 ht.2⟩
  · obtain ⟨b, hb, huniq⟩ := hb
    refine ⟨b, ⟨hb.1, (heq b ⟨by linarith [hb.1.1, hcrit.1], hb.1.2⟩).2 hb.2⟩, ?_⟩
    intro t ht
    exact huniq t ⟨ht.1, (heq t ⟨by linarith [ht.1.1, hcrit.1], ht.1.2⟩).1 ht.2⟩

/-- The two branches exhaust a positive gradient level in the full
principal-phase range, including negative phases and the endpoints. -/
theorem schattenPhaseDerivative_level_set (p g : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p)) :
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      ∀ t : ℝ, |t| ≤ Real.pi →
        (schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
          t = a ∨ t = b) := by
  obtain ⟨⟨a, ha, huniq_a⟩, ⟨b, hb, huniq_b⟩⟩ :=
    schattenPhaseDerivative_two_roots p g hp1 hp2 hg0 hgm
  refine ⟨a, ha.1, b, hb.1, ?_⟩
  intro t ht
  constructor
  · intro hlevel
    have hpos := principal_phase_pos_of_schattenPhaseDerivative_pos p t
      (by linarith : 0 < p) ht (by rw [hlevel]; exact hg0)
    rcases lt_trichotomy t (criticalAngle p) with hlt | heq | hgt
    · exact Or.inl (huniq_a t ⟨⟨hpos.1, hlt⟩, hlevel⟩)
    · have hcrit := criticalAngle_mem p hp1 hp2
      rw [heq, schattenPhaseDerivative_exp_eq_amplitude p (criticalAngle p)
        ⟨hcrit.1, by linarith [hcrit.2, Real.pi_pos]⟩] at hlevel
      exact False.elim (hgm.ne hlevel.symm)
    · exact Or.inr (huniq_b t ⟨⟨hgt, hpos.2⟩, hlevel⟩)
  · rintro (rfl | rfl)
    · exact ha.2
    · exact hb.2

/-- The amplitude reaches its maximum precisely at the critical angle. -/
theorem phaseAmplitude_le_criticalAngle (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht : t ∈ Icc 0 Real.pi) :
    phaseAmplitude p t ≤ phaseAmplitude p (criticalAngle p) := by
  have hcrit := criticalAngle_mem p hp1 hp2
  rcases le_total t (criticalAngle p) with hle | hle
  · exact (phaseAmplitude_strictMonoOn p hp1 hp2).monotoneOn
      ⟨ht.1, hle⟩ ⟨hcrit.1.le, le_rfl⟩ hle
  · exact (phaseAmplitude_strictAntiOn p hp1 hp2).antitoneOn
      ⟨le_rfl, by linarith [hcrit.2, Real.pi_pos]⟩ ⟨hle, ht.2⟩ hle

/-- The amplitude has a unique maximizer on the full positive phase range. -/
theorem phaseAmplitude_eq_criticalAngle_iff (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht : t ∈ Icc 0 Real.pi) :
    phaseAmplitude p t = phaseAmplitude p (criticalAngle p) ↔ t = criticalAngle p := by
  have hc := criticalAngle_mem p hp1 hp2
  constructor
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := phaseAmplitude_strictMonoOn p hp1 hp2
        ⟨ht.1, hlt.le⟩ ⟨hc.1.le, le_rfl⟩ hlt
      exact h.ne heq
    · have h := phaseAmplitude_strictAntiOn p hp1 hp2
        ⟨le_rfl, by linarith [hc.2, Real.pi_pos]⟩ ⟨hgt.le, ht.2⟩ hgt
      exact h.ne heq
  · rintro rfl
    rfl

/-- At the maximal positive gradient level the two branches coincide
at the critical angle; there is no second allowed principal phase. -/
theorem schattenPhaseDerivative_max_level_set (p t : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (ht : |t| ≤ Real.pi) :
    schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) =
        p * phaseAmplitude p (criticalAngle p) ↔ t = criticalAngle p := by
  have hc := criticalAngle_mem p hp1 hp2
  have hp0 : 0 < p := by linarith
  have hmax : 0 < phaseAmplitude p (criticalAngle p) := by
    have h := phaseAmplitude_strictMonoOn p hp1 hp2
      ⟨le_rfl, hc.1.le⟩ ⟨hc.1.le, le_rfl⟩ hc.1
    rwa [phaseAmplitude_zero p hp1] at h
  constructor
  · intro hlevel
    have htpos := principal_phase_pos_of_schattenPhaseDerivative_pos p t hp0 ht
      (by rw [hlevel]; exact mul_pos hp0 hmax)
    rw [schattenPhaseDerivative_exp_eq_amplitude p t htpos] at hlevel
    exact (phaseAmplitude_eq_criticalAngle_iff p t hp1 hp2
      ⟨htpos.1.le, htpos.2.le⟩).1 (mul_left_cancel₀ hp0.ne' hlevel)
  · rintro rfl
    exact schattenPhaseDerivative_exp_eq_amplitude p (criticalAngle p)
      ⟨hc.1, by linarith [hc.2, Real.pi_pos]⟩

/-- The same two positive roots determine the negative gradient level by
changing their signs. This gives a common pair of roots for opposite blocks. -/
theorem schattenPhaseDerivative_signed_level_sets (p g : ℝ)
    (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p)) :
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      (∀ t : ℝ, |t| ≤ Real.pi →
        (schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g ↔
          t = a ∨ t = b)) ∧
      (∀ t : ℝ, |t| ≤ Real.pi →
        (schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = -g ↔
          t = -a ∨ t = -b)) := by
  obtain ⟨a, ha, b, hb, hlevel⟩ := schattenPhaseDerivative_level_set p g hp1 hp2 hg0 hgm
  refine ⟨a, ha, b, hb, hlevel, ?_⟩
  intro t ht
  calc
    _ ↔ schattenPhaseDerivative p (Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) = g := by
      rw [schattenPhaseDerivative_exp_neg, neg_eq_iff_eq_neg]
    _ ↔ -t = a ∨ -t = b := hlevel (-t) (by simpa only [abs_neg] using ht)
    _ ↔ t = -a ∨ t = -b := by simp only [neg_eq_iff_eq_neg]

/-- Every positive spectral level of an actual unitary gradient is bounded
by the maximal scalar amplitude. Spectral mapping supplies a unit-circle
phase realizing the level, so there are no additional positive blocks
beyond the submaximal and coalescing-root cases. -/
theorem positive_gradient_spectrum_le_max
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E]
    (p g : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (U : unitary (E →L[ℂ] E))
    (hg : (g : ℂ) ∈ spectrum ℂ (schattenUnitaryGradient p (U : E →L[ℂ] E))) :
    g ≤ p * phaseAmplitude p (criticalAngle p) := by
  have hf : ContinuousOn (fun z : ℂ => (schattenPhaseDerivative p z : ℂ))
      (spectrum ℂ (U : E →L[ℂ] E)) :=
    ((U : E →L[ℂ] E).finite_spectrum ℂ).continuousOn _
  rw [schattenUnitaryGradient_def] at hg
  have hs := cfc_map_spectrum (R := ℂ) (a := (U : E →L[ℂ] E))
    (f := fun z : ℂ => (schattenPhaseDerivative p z : ℂ)) (by infer_instance) hf
  rw [hs] at hg
  obtain ⟨z, hz, hzg⟩ := hg
  have hn : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary U.2 hz
  have hphase : Complex.exp (((z.arg : ℝ) : ℂ) * Complex.I) = z := by
    simpa only [hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
  have hreal : schattenPhaseDerivative p z = g := Complex.ofReal_injective hzg
  have harg := principal_phase_pos_of_schattenPhaseDerivative_pos p z.arg
    (by linarith) (Complex.abs_arg_le_pi z) (by rw [hphase, hreal]; exact hg0)
  calc
    g = p * phaseAmplitude p z.arg := by
      rw [← schattenPhaseDerivative_exp_eq_amplitude p z.arg harg, hphase, hreal]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (phaseAmplitude_le_criticalAngle p z.arg hp1 hp2 ⟨harg.1.le, harg.2.le⟩) (by linarith)

/-- On a positive submaximal gradient eigenspace, all principal eigenphases
of the unitary lie in the same pair of scalar roots. The unitary is arbitrary;
the stationarity identity will subsequently pair its opposite gradient levels. -/
theorem gradient_eigenphases_have_two_roots
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E]
    (p g : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hg0 : 0 < g)
    (hgm : g < p * phaseAmplitude p (criticalAngle p))
    (U : E →L[ℂ] E) [IsStarNormal U] :
    ∃ a ∈ Ioo 0 (criticalAngle p), ∃ b ∈ Ioo (criticalAngle p) Real.pi,
      ∀ (x : E) (t : ℝ), x ≠ 0 → |t| ≤ Real.pi →
        U x = Complex.exp ((t : ℂ) * Complex.I) • x →
        schattenUnitaryGradient p U x = (g : ℂ) • x → t = a ∨ t = b := by
  obtain ⟨a, ha, b, hb, hlevel⟩ := schattenPhaseDerivative_level_set p g hp1 hp2 hg0 hgm
  refine ⟨a, ha, b, hb, ?_⟩
  intro x t hx ht hU hG
  have hcalc := schattenUnitaryGradient_apply_of_apply_eq_smul p U x _ hU
  rw [hG] at hcalc
  have hscalar := smul_left_injective ℂ hx hcalc
  have hreal : schattenPhaseDerivative p (Complex.exp ((t : ℂ) * Complex.I)) = g := by
    exact_mod_cast hscalar.symm
  exact (hlevel t ht).1 hreal

end

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
