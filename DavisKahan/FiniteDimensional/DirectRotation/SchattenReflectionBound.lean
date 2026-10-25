/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseMinimum
public import DavisKahan.FiniteDimensional.DirectRotation.ComplexTracePrincipalAngles
public import ForTauCeti.Analysis.InnerProductSpace.SchattenInvolution
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle

/-!
# The principal-angle lower bound for reflecting transporters

A reflection has displacement singular values zero and two. Its Schatten
power is therefore a fixed multiple of its nuclear displacement. The existing
projection-distance lower bound and the scalar endpoint competitor show
that its cost dominates the proposed principal-angle sum.

The principal angles in the public statement are the accepted Tau Ceti API.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

/-- The endpoint competitor bounds a principal-plane cost by the sine
of its physical angle. -/
theorem phaseMinimum_le_two_rpow_mul_sin (p theta : ℝ) (hp : 1 ≤ p)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    phaseMinimum p theta ≤ (2 : ℝ) ^ p * Real.sin theta := by
  have hs : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  calc
    phaseMinimum p theta ≤ (2 * Real.sin theta) ^ p :=
      phaseMinimum_le_endpoint p theta hp hθ.1
    _ = (2 : ℝ) ^ p * Real.sin theta ^ p := Real.mul_rpow (by norm_num) hs
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_self_of_le_one hs (Real.sin_le_one theta) hp)
      (Real.rpow_nonneg (by norm_num) _)

/-- For an interior physical angle and an exponent greater than one,
the sine comparison is strict. -/
theorem phaseMinimum_lt_two_rpow_mul_sin (p theta : ℝ) (hp : 1 < p)
    (hθ : theta ∈ Ioo 0 (Real.pi / 2)) :
    phaseMinimum p theta < (2 : ℝ) ^ p * Real.sin theta := by
  have hs : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin theta < 1 := by
    simpa only [Real.sin_pi_div_two] using Real.strictMonoOn_sin
      ⟨by linarith [Real.pi_pos, hθ.1], hθ.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hθ.2
  calc
    phaseMinimum p theta ≤ (2 * Real.sin theta) ^ p :=
      phaseMinimum_le_endpoint p theta hp.le hθ.1.le
    _ = (2 : ℝ) ^ p * Real.sin theta ^ p := Real.mul_rpow (by norm_num) hs.le
    _ < _ := mul_lt_mul_of_pos_left (Real.rpow_lt_self_of_lt_one hs hs1 hp)
      (Real.rpow_pos_of_pos (by norm_num) _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem fullKyFanSum_eq_nuclear (A : E →ₗ[ℂ] E) :
    TauCeti.kyFanSum (Module.finrank ℂ E) A =
      UnitarilyInvariantSeminorm.nuclear ℂ E E A := by
  rw [TauCeti.kyFanSum_eq_kyFan, UnitarilyInvariantSeminorm.kyFan_apply]
  exact A.kyFanSum_eq_nuclear (LinearMap.finrank_range_le A)

/-- The displacement of a reflecting transporter dominates the endpoint
sine cost of its actual principal angles. -/
theorem two_rpow_mul_sum_sin_le_selfAdjoint_transport_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsSelfAdjoint (W : E →L[ℂ] E))
    (hmap : P.map W.toLinearMap = Q) :
    (2 : ℝ) ^ p.toReal *
        (∑ i : Fin (Module.finrank ℂ P), Real.sin (P.principalAngles Q i)) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) ^ p.toReal := by
  have hPQ : Module.finrank ℂ P = Module.finrank ℂ Q := by
    rw [← hmap]
    exact (W.toLinearEquiv.finrank_map_eq P).symm
  have hsines : TauCeti.principalSines P Q = P.principalSines Q := by
    rw [TauCeti.principalSines, Submodule.principalSines_def]
    congr 1
    rw [Submodule.sinThetaMap_def]
    rfl
  have htrace := ComplexTraceOptimality.kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles
    P Q hPQ
  rw [fullKyFanSum_eq_nuclear] at htrace
  simp_rw [ComplexTraceOptimality.sin_principalAngles_eq_principalSines, hsines,
    ← Submodule.sin_principalAngles] at htrace
  have hbound := projectionDifference_uiNorm_le_displacement
    (UnitarilyInvariantSeminorm.nuclear ℂ E E) P Q W hmap
  have hcost : UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal =
      (2 : ℝ) ^ (p.toReal - 1) * UnitarilyInvariantSeminorm.nuclear ℂ E E
        (LinearMap.id - W.toLinearMap) := by
    exact schatten_displacement_rpow_of_isSelfAdjoint
      (Unitary.linearIsometryEquiv.symm W) hW p hp
  have hpow : (2 : ℝ) ^ p.toReal = (2 : ℝ) ^ (p.toReal - 1) * 2 := by
    rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  calc
    _ = (2 : ℝ) ^ (p.toReal - 1) *
        UnitarilyInvariantSeminorm.nuclear ℂ E E (projection P - projection Q) := by
      rw [htrace, hpow]
      ring
    _ ≤ (2 : ℝ) ^ (p.toReal - 1) * UnitarilyInvariantSeminorm.nuclear ℂ E E
        (LinearMap.id - W.toLinearMap) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by norm_num) _)
    _ = _ := hcost.symm

/-- Every self-adjoint unitary transporter dominates the exact scalar
minimum summed over the accepted principal angles of the subspace pair. -/
theorem sum_phaseMinimum_le_selfAdjoint_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsSelfAdjoint (W : E →L[ℂ] E))
    (hmap : P.map W.toLinearMap = Q) :
    (∑ i : Fin (Module.finrank ℂ P), phaseMinimum p.toReal (P.principalAngles Q i)) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) ^ p.toReal := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  calc
    _ ≤ (2 : ℝ) ^ p.toReal *
        ∑ i : Fin (Module.finrank ℂ P), Real.sin (P.principalAngles Q i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => phaseMinimum_le_two_rpow_mul_sin p.toReal _ hp1
        ⟨P.principalAngles_nonneg Q i, P.principalAngles_le_pi_div_two Q i⟩)
    _ ≤ _ := two_rpow_mul_sum_sin_le_selfAdjoint_transport_complex p hp P Q W hW hmap

/-- A reflecting transport attaining the scalar minimum has only zero
and right principal angles. Interior angles force a strict cost deficit. -/
theorem principalAngles_eq_zero_or_right_of_selfAdjoint_attains_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsSelfAdjoint (W : E →L[ℂ] E))
    (hmap : P.map W.toLinearMap = Q)
    (hatt : UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal =
        ∑ i : Fin (Module.finrank ℂ P), phaseMinimum p.toReal (P.principalAngles Q i)) :
    ∀ i : Fin (Module.finrank ℂ P),
      P.principalAngles Q i = 0 ∨ P.principalAngles Q i = Real.pi / 2 := by
  classical
  have hle (i : Fin (Module.finrank ℂ P)) :
      phaseMinimum p.toReal (P.principalAngles Q i) ≤
        (2 : ℝ) ^ p.toReal * Real.sin (P.principalAngles Q i) :=
    phaseMinimum_le_two_rpow_mul_sin p.toReal _ hp1.le
      ⟨P.principalAngles_nonneg Q i, P.principalAngles_le_pi_div_two Q i⟩
  have hbound := two_rpow_mul_sum_sin_le_selfAdjoint_transport_complex p hp P Q W hW hmap
  rw [hatt, Finset.mul_sum] at hbound
  have heq := le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) hbound
  intro i
  by_cases hz : P.principalAngles Q i = 0
  · exact Or.inl hz
  by_cases hr : P.principalAngles Q i = Real.pi / 2
  · exact Or.inr hr
  have hstrict := phaseMinimum_lt_two_rpow_mul_sin p.toReal _ hp1
    ⟨lt_of_le_of_ne (P.principalAngles_nonneg Q i) (Ne.symm hz),
      lt_of_le_of_ne (P.principalAngles_le_pi_div_two Q i) hr⟩
  exact False.elim (hstrict.ne
    ((Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp heq i (Finset.mem_univ i)))

/-- For an acute pair, a reflecting transport attaining the scalar
minimum is the identity, including on all common ambient directions. -/
theorem selfAdjoint_attaining_eq_refl_of_acute_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsSelfAdjoint (W : E →L[ℂ] E))
    (hmap : P.map W.toLinearMap = Q)
    (hatt : UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal =
        ∑ i : Fin (Module.finrank ℂ P), phaseMinimum p.toReal (P.principalAngles Q i))
    (hacute : ∀ i : Fin (Module.finrank ℂ P), P.principalAngles Q i < Real.pi / 2) :
    W = LinearIsometryEquiv.refl ℂ E := by
  have hzero (i : Fin (Module.finrank ℂ P)) : P.principalAngles Q i = 0 := by
    rcases principalAngles_eq_zero_or_right_of_selfAdjoint_attains_complex
      p hp hp1 P Q W hW hmap hatt i with hz | hr
    · exact hz
    · exact False.elim ((hacute i).ne hr)
  have hcost : UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - W.toLinearMap) ^ p.toReal = 0 := by
    rw [hatt]
    simp only [hzero, phaseMinimum_zero_angle p.toReal hp1.le, Finset.sum_const_zero]
  have hn := (Real.rpow_eq_zero
    (apply_nonneg _ _) (by linarith : p.toReal ≠ 0)).mp hcost
  have hdisp := (UnitarilyInvariantSeminorm.schatten_apply_eq_zero_iff p).mp hn
  have hid := sub_eq_zero.mp hdisp
  ext x
  exact (congrArg (fun T : E →ₗ[ℂ] E => T x) hid).symm

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
