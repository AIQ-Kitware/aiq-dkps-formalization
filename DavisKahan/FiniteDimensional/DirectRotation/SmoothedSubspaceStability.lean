/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPrincipalAngles
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedStability

/-!
# Quantitative canonical transport from a principal-angle bound

A strict subcritical bound on every accepted principal angle gives a positive
uniform dual weight. The unrestricted weighted transport objective then
controls the squared Frobenius distance to the canonical rotation.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The uniform quadratic-growth coefficient at a strict angle bound. -/
def smoothedStabilityCoefficient (tau bound : ℝ) : ℝ :=
  (Real.cos bound - ((smoothingRadius tau)⁻¹) ^ 2) /
    (2 * Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos bound))

/-- The explicit coefficient is the smallest real part of the weighted
nuclear supporting unitary, with the Frobenius normalization included. -/
theorem smoothedStabilityCoefficient_eq_dualReal
    (tau bound : ℝ) (hτ : 0 < tau)
    (hcut : ((smoothingRadius tau)⁻¹) ^ 2 < Real.cos bound) :
    smoothedStabilityCoefficient tau bound =
      (smoothingRadius tau)⁻¹ *
        dualReal (smoothingRadius tau) (smoothingRadius tau)⁻¹ bound / 2 := by
  let a := smoothingRadius tau
  have ha : 0 < a := lt_trans zero_lt_one (one_lt_smoothingRadius tau hτ)
  have hp : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hc : a * (a⁻¹) ^ 2 = a⁻¹ := by
    rw [pow_two, ← mul_assoc, hp, one_mul]
  have hsub : a⁻¹ ≤ a * Real.cos bound := by
    have h := mul_lt_mul_of_pos_left hcut ha
    change a * (a⁻¹) ^ 2 < a * Real.cos bound at h
    rw [hc] at h
    exact h.le
  have hr : (a * Real.cos bound - a⁻¹) ^ 2 + (a * Real.sin bound) ^ 2 =
      tau ^ 2 + 2 - 2 * Real.cos bound := by
    have hs := smoothingRadius_sq_add_inv_sq tau hτ
    change a ^ 2 + (a⁻¹) ^ 2 = tau ^ 2 + 2 at hs
    nlinarith [Real.sin_sq_add_cos_sq bound,
      congrArg (fun t : ℝ => a ^ 2 * t) (Real.sin_sq_add_cos_sq bound),
      congrArg (fun t : ℝ => 2 * t * Real.cos bound) hp]
  change (Real.cos bound - (a⁻¹) ^ 2) /
      (2 * Real.sqrt (tau ^ 2 + 2 - 2 * Real.cos bound)) =
    a⁻¹ * dualReal a a⁻¹ bound / 2
  rw [dualReal, ite_eq_left hsub, hr]
  have hn : a⁻¹ * (a * Real.cos bound - a⁻¹) =
      Real.cos bound - (a⁻¹) ^ 2 := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha.ne']
    ring
  rw [← hn]
  ring

/-- The coefficient is positive exactly on the strict side of the cutoff
used in the stability theorem. -/
theorem smoothedStabilityCoefficient_pos (tau bound : ℝ) (hτ : 0 < tau)
    (hcut : ((smoothingRadius tau)⁻¹) ^ 2 < Real.cos bound) :
    0 < smoothedStabilityCoefficient tau bound := by
  apply div_pos (sub_pos.mpr hcut)
  apply mul_pos (by norm_num)
  apply Real.sqrt_pos.mpr
  nlinarith [sq_pos_of_pos hτ, Real.cos_le_one bound]

/-- A strict subcritical principal-angle bound gives quantitative growth of
weighted nuclear transport at the canonical rotation, against all admissible
unitaries, including competitors that mix the principal planes. -/
theorem weighted_transport_growth_of_principalAngles_le
    (a b bound : ℝ) (hb : 0 < b) (hab : b < a)
    (hbound : bound ∈ Set.Icc 0 (Real.pi / 2)) (hcut : b < a * Real.cos bound)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ bound) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      b * dualReal a b bound / 2 * UnitarilyInvariantSeminorm.frobenius ℂ E E
          (T.toLinearMap - R.toLinearMap) ^ 2 ≤
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) -
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • R.toLinearMap - (b : ℂ) • LinearMap.id) := by
  let D := finiteCrossedDefectEquiv U V hUV
  let Rop := nonacuteDirectRotation U V D
  let R := Unitary.linearIsometryEquiv
    (⟨Rop, nonacuteDirectRotation_mem_unitary U V D⟩ : unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0⟩ :=
    exists_subspace_paired_rotation_basis U V hUV
  have hle := paired_angles_le_of_principalAngles_le U V e theta hθ hC0 hC1 hCf hJ0
    bound hbound.1 hmax
  have hcos (i) : Real.cos bound ≤ Real.cos (theta i) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (hθ i).1.le
      (by linarith [hbound.2, Real.pi_pos]) (hle i)
  have hsub (i) : b ≤ a * Real.cos (theta i) :=
    hcut.le.trans (mul_le_mul_of_nonneg_left (hcos i) (hb.le.trans hab.le))
  have hweight (i) : dualReal a b bound ≤ dualReal a b (theta i) :=
    dualReal_mono_of_cos_le a b _ _ hb.le hab hcut.le (hcos i)
  let A := (a : ℂ) • R.toLinearMap
  have hA0 (i) : A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)) := by
    change (a : ℂ) • R (e (.inl (0, i))) = _
    have hr : R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)) := hR0 i
    rw [hr, smul_smul, Complex.exp_ofReal_mul_I]
    congr 1
    push_cast
    ring
  have hA1 (i) : A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)) := by
    change (a : ℂ) • R (e (.inl (1, i))) = _
    have hr : R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i)) := hR1 i
    rw [hr, smul_smul, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    congr 1
    push_cast
    ring
  have hAf (j) : A (e (.inr j)) = (a : ℂ) • e (.inr j) := by
    change (a : ℂ) • R (e (.inr j)) = _
    rw [show R (e (.inr j)) = e (.inr j) from hRf j]
  have hcan := weightedNuclear_identity_attains_of_subcritical a b hb hab theta
    (fun i => ⟨(hθ i).1.le, (hθ i).2⟩) hsub e A hA0 hA1 hAf
  have hRref (x : E) : R (U.reflection x) = V.reflection (R x) :=
    nonacuteDirectRotation_reflection_intertwines U V D x
  dsimp only
  intro T hT
  have hTref := (Submodule.map_eq_iff_intertwines_reflection U V T).mp hT
  let Z := R.trans T.symm
  have hcomm (x : E) : Z (U.reflection x) = U.reflection (Z x) := by
    apply T.injective
    change T (T.symm (R (U.reflection x))) = T (U.reflection (T.symm (R x)))
    rw [T.apply_symm_apply, hTref, T.apply_symm_apply, hRref]
  have hg := weightedNuclear_growth_of_commute a b (dualReal a b bound) hb.le hab
    (dualReal_le_one a b bound hb.le hab) theta hweight e A hA0 hA1 hAf U.reflection hJ0 Z hcomm
  rw [← hcan] at hg
  let N := UnitarilyInvariantSeminorm.nuclear ℂ E E
  let F := UnitarilyInvariantSeminorm.frobenius ℂ E E
  have hfactor : A - (b : ℂ) • Z.toLinearMap =
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ∘ₗ Z.toLinearMap := by
    ext x
    simp [A, Z]
  have hN : N (A - (b : ℂ) • Z.toLinearMap) =
      N ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) := by
    rw [hfactor]
    exact N.map_comp_linearIsometryEquiv Z _
  have hFfactor : T.toLinearMap ∘ₗ (Z.toLinearMap - LinearMap.id) =
      R.toLinearMap - T.toLinearMap := by
    ext x
    simp [Z]
  have hF : F (Z.toLinearMap - LinearMap.id) = F (T.toLinearMap - R.toLinearMap) := by
    calc
      _ = F (T.toLinearMap ∘ₗ (Z.toLinearMap - LinearMap.id)) :=
        (F.map_linearIsometryEquiv_comp T _).symm
      _ = F (R.toLinearMap - T.toLinearMap) := congrArg F hFfactor
      _ = _ := by rw [← neg_sub, map_neg_eq_map]
  change b * dualReal a b bound / 2 * F (Z.toLinearMap - LinearMap.id) ^ 2 ≤
    N (A - (b : ℂ) • Z.toLinearMap) - N (A - (b : ℂ) • LinearMap.id) at hg
  rw [hF, hN] at hg
  exact hg

/-- A near-minimizer of the literal smoothed singular-value cost lies near
the canonical rotation whenever every principal angle stays strictly below
the phase transition. The bound covers every admissible unitary transport. -/
theorem smoothed_transport_growth_of_principalAngles_le
    (tau bound : ℝ) (hτ : 0 < tau)
    (hbound : bound ∈ Set.Icc 0 (Real.pi / 2))
    (hcut : ((smoothingRadius tau)⁻¹) ^ 2 < Real.cos bound)
    (U V : Submodule ℂ E) (hUV : Module.finrank ℂ U = Module.finrank ℂ V)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ bound) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation U V (finiteCrossedDefectEquiv U V hUV),
        nonacuteDirectRotation_mem_unitary U V (finiteCrossedDefectEquiv U V hUV)⟩ :
          unitary (E →L[ℂ] E))
    ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
      smoothedStabilityCoefficient tau bound *
          UnitarilyInvariantSeminorm.frobenius ℂ E E (T.toLinearMap - R.toLinearMap) ^ 2 ≤
        smoothedDisplacementCost tau T.toLinearMap -
          smoothedDisplacementCost tau R.toLinearMap := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau hτ
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hab : a⁻¹ < a := lt_trans ((inv_lt_one₀ ha0).mpr ha) ha
  have hsub : a⁻¹ < a * Real.cos bound := by
    have h := mul_lt_mul_of_pos_left hcut ha0
    change a * (a⁻¹) ^ 2 < a * Real.cos bound at h
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at h
    exact h
  have hcost (T : E ≃ₗᵢ[ℂ] E) :
      smoothedDisplacementCost tau T.toLinearMap =
        UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - ((a⁻¹ : ℝ) : ℂ) • LinearMap.id) -
            Module.finrank ℂ E * tau :=
    smoothedDisplacementCost_eq_weightedNuclear tau hτ (Unitary.linearIsometryEquiv.symm T)
  dsimp only
  intro T hT
  rw [hcost, hcost, smoothedStabilityCoefficient_eq_dualReal tau bound hτ hcut]
  convert weighted_transport_growth_of_principalAngles_le a a⁻¹ bound
    (inv_pos.mpr ha0) hab hbound hsub U V hUV hmax T hT using 1
  ring

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
