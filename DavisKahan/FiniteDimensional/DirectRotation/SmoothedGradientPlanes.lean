/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientNoMixing
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedBalancedPhases
public import ForTauCeti.Analysis.InnerProductSpace.OrthogonalProjectionPhases

/-!
# Exact scalar costs on actual Charbonnier gradient blocks

The disjoint large-phase projections at an ambient local minimum admit
a common phase eigenbasis. Each resulting opposite phase pair attains
the exact scalar minimum at its acute mean angle. The sum of those
minimum values is the literal cost of the two actual unitary restrictions.
The uniform positive-level basis theorem includes the coalescing critical
level. The actual zero-gradient block and principal-angle assembly are
handled by the downstream local-to-global theorem.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open Set

private theorem scalar_cost_of_phase_pair
    (tau a b alpha beta : ℝ) (htau : 0 < tau)
    (ha : a ∈ Ioo 0 (smoothedCriticalAngle tau))
    (hb : b ∈ Ioo (smoothedCriticalAngle tau) Real.pi)
    (hbalance : smoothedPhaseDerivative tau (Complex.exp ((a : ℂ) * Complex.I)) =
      smoothedPhaseDerivative tau (Complex.exp ((b : ℂ) * Complex.I)))
    (hpair : (alpha = a ∧ beta = a) ∨
      (alpha = b ∧ beta = a) ∨ (alpha = a ∧ beta = b)) :
    (alpha + beta) / 2 ∈ Ioo 0 (Real.pi / 2) ∧
      (Real.sqrt (tau ^ 2 + ‖Complex.exp ((alpha : ℂ) * Complex.I) - 1‖ ^ 2) - tau) +
        (Real.sqrt (tau ^ 2 +
          ‖Complex.exp (((-beta : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) =
            smoothedPhaseMinimum tau ((alpha + beta) / 2) := by
  have hc := smoothedCriticalAngle_mem tau htau
  have hbalanced := balanced_roots_smoothedPhaseMinimum tau a b htau ha.1
    (ha.2.trans hb.1) hb.2 hbalance
  rcases hpair with h | h | h
  · rw [h.1, h.2, show (a + a) / 2 = a by ring]
    refine ⟨⟨ha.1, ha.2.trans hc.2⟩, ?_⟩
    rw [smoothed_eigenphase_cost_neg,
      smoothedPhaseMinimum_eq_canonical_of_le_critical tau a htau ha.1.le ha.2.le, two_mul]
  · rw [h.1, h.2, add_comm b a]
    refine ⟨hbalanced.1, ?_⟩
    rw [smoothed_eigenphase_cost_neg] at hbalanced ⊢
    exact (add_comm _ _).trans hbalanced.2
  · rw [h.1, h.2]
    exact hbalanced

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every actual positive submaximal gradient block of a constrained local
minimum has a joint phase eigenbasis. Each pair attains the exact scalar
minimum at its mean angle, and their sum is the literal paired cost.
No prescribed block coordinates or simple-spectrum hypothesis is supplied. -/
theorem gradient_block_scalar_minima_of_isLocalMinOn_transports_complex
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g) (hgm : g < (smoothingRadius tau)⁻¹) :
    let L := Module.End.eigenspace
      (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ (V W : L ≃ₗᵢ[ℂ] L)
      (e : OrthonormalBasis (Fin (Module.finrank ℂ L)) ℂ L)
      (alpha beta : Fin (Module.finrank ℂ L) → ℝ),
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (∀ x : L, K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x)) ∧
      (∀ i, V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i) ∧
      (∀ i, W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, (Real.sqrt (tau ^ 2 +
        ‖Complex.exp ((alpha i : ℂ) * Complex.I) - 1‖ ^ 2) - tau) +
        (Real.sqrt (tau ^ 2 +
          ‖Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) =
            smoothedPhaseMinimum tau ((alpha i + beta i) / 2)) ∧
      smoothedDisplacementCost tau V.toLinearMap + smoothedDisplacementCost tau W.toLinearMap =
        ∑ i, smoothedPhaseMinimum tau ((alpha i + beta i) / 2) ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  let L := Module.End.eigenspace
    (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
  obtain ⟨a, ha, b, hb, hga, hgb, V, W, A, B, hA, hB, hAB,
    hVact, hWact, hV, hW⟩ :=
    gradient_block_no_overlap_of_isLocalMinOn_transports_complex
      tau htau K Q U htrans hmin g hg0 hgm
  obtain ⟨e, alpha, beta, hpair, hVe, hWe⟩ :=
    exists_orthogonal_two_phase_basis_complex a b V W A B hA hB hAB hV hW
  have hscalar (i) := scalar_cost_of_phase_pair tau a b (alpha i) (beta i)
    htau ha hb (hga.trans hgb.symm) (hpair i)
  have hc := smoothedCriticalAngle_mem tau htau
  have haPi : a ∈ Ioo 0 Real.pi := ⟨ha.1, by linarith [ha.2, hc.2, Real.pi_pos]⟩
  have hbPi : b ∈ Ioo 0 Real.pi := ⟨hc.1.trans hb.1, hb.2⟩
  refine ⟨V, W, e, alpha, beta, hVact, hWact, hVe, hWe,
    fun i => (hscalar i).1, fun i => (hscalar i).2, ?_, ?_⟩
  · have hVdisp (i : Fin (Module.finrank ℂ L)) :
        ((LinearMap.id : L →ₗ[ℂ] L) - V.toLinearMap) (e i) =
          (1 - Complex.exp ((alpha i : ℂ) * Complex.I)) • e i := by
      change e i - V (e i) = _
      rw [hVe, sub_smul, one_smul]
    have hWdisp (i : Fin (Module.finrank ℂ L)) :
        ((LinearMap.id : L →ₗ[ℂ] L) - W.toLinearMap) (e i) =
          (1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)) • e i := by
      change e i - W (e i) = _
      rw [hWe, sub_smul, one_smul]
    rw [smoothedDisplacementCost, smoothedDisplacementCost,
      sum_singularValues_eq_sum_norm_eigenvalues e _ _ hVdisp
        (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau),
      sum_singularValues_eq_sum_norm_eigenvalues e _ _ hWdisp
        (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [norm_sub_rev] using (hscalar i).2
  · intro i
    rcases hpair i with h | h | h
    · rw [h.1, h.2]
      exact ⟨haPi, haPi⟩
    · rw [h.1, h.2]
      exact ⟨hbPi, haPi⟩
    · rw [h.1, h.2]
      exact ⟨haPi, hbPi⟩

private theorem signed_critical_gradient_apply
    (tau s : ℝ) (htau : 0 < tau) (hs : s = 1 ∨ s = -1)
    (U : unitary (E →L[ℂ] E)) (x : E)
    (hx : smoothedUnitaryGradient tau (U : E →L[ℂ] E) x =
      ((s * (smoothingRadius tau)⁻¹ : ℝ) : ℂ) • x) :
    (U : E →L[ℂ] E) x =
      Complex.exp (((s * smoothedCriticalAngle tau : ℝ) : ℂ) * Complex.I) • x := by
  let D := Module.End.eigenspace (smoothedUnitaryGradient tau
    (U : E →L[ℂ] E)).toLinearMap ((s * (smoothingRadius tau)⁻¹ : ℝ) : ℂ)
  let x' : D := ⟨x, Module.End.mem_eigenspace_iff.mpr hx⟩
  obtain ⟨V, hVact, hV⟩ :=
    signed_critical_gradient_eigenspace_representation_complex tau s htau hs U
  calc
    _ = (V x' : E) := (hVact x').symm
    _ = _ := congrArg (fun T : D →L[ℂ] D => (T x' : E)) hV

private theorem positive_gradient_spectrum_le_max
    (tau g : ℝ) (htau : 0 < tau) (hg0 : 0 < g)
    (U : unitary (E →L[ℂ] E))
    (hg : (g : ℂ) ∈ spectrum ℂ (smoothedUnitaryGradient tau (U : E →L[ℂ] E))) :
    g ≤ (smoothingRadius tau)⁻¹ := by
  have hf : ContinuousOn (fun z : ℂ => (smoothedPhaseDerivative tau z : ℂ))
      (spectrum ℂ (U : E →L[ℂ] E)) :=
    ((U : E →L[ℂ] E).finite_spectrum ℂ).continuousOn _
  change (g : ℂ) ∈ spectrum ℂ
    (cfc (fun z => (smoothedPhaseDerivative tau z : ℂ)) (U : E →L[ℂ] E)) at hg
  rw [cfc_map_spectrum (R := ℂ) (a := (U : E →L[ℂ] E))
    (f := fun z : ℂ => (smoothedPhaseDerivative tau z : ℂ)) (by infer_instance) hf] at hg
  obtain ⟨z, hz, hzg⟩ := hg
  have hreal : smoothedPhaseDerivative tau z = g := Complex.ofReal_injective hzg
  have hbound := abs_smoothedPhaseDerivative_le tau htau z
    (spectrum.norm_eq_one_of_unitary U.property hz)
  rwa [hreal, abs_of_pos hg0] at hbound

/-- Every positive spectral level of an actual local minimum has an
ambient source-reflection-paired phase eigenbasis. This uniform statement
includes the maximal level, where the two scalar branches coalesce.
Each pair attains its exact smoothed scalar minimum. -/
theorem gradient_eigenspace_phase_basis_of_isLocalMinOn_transports_complex
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g)
    (hg : (g : ℂ) ∈ spectrum ℂ (smoothedUnitaryGradient tau (U : E →L[ℂ] E))) :
    let L := Module.End.eigenspace
      (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ L)) ℂ L)
      (alpha beta : Fin (Module.finrank ℂ L) → ℝ),
      (∀ i, (U : E →L[ℂ] E) (e i : E) =
        Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i)) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, (Real.sqrt (tau ^ 2 +
        ‖Complex.exp ((alpha i : ℂ) * Complex.I) - 1‖ ^ 2) - tau) +
        (Real.sqrt (tau ^ 2 +
          ‖Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) =
            smoothedPhaseMinimum tau ((alpha i + beta i) / 2)) ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  let L := Module.End.eigenspace
    (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
  have hgm := positive_gradient_spectrum_le_max tau g htau hg0 U hg
  rcases lt_or_eq_of_le hgm with hgm | hgm
  · obtain ⟨V, W, e, alpha, beta, hVact, hWact, hVe, hWe,
      hmean, hcost, _, hbounds⟩ :=
      gradient_block_scalar_minima_of_isLocalMinOn_transports_complex
        tau htau K Q U htrans hmin g hg0 hgm
    refine ⟨e, alpha, beta, ?_, ?_, hmean, hcost, hbounds⟩
    · intro i
      exact (hVact (e i)).symm.trans (congrArg (fun x : L => (x : E)) (hVe i))
    · intro i
      rw [← hWact, hWe]
      exact K.reflection.map_smul _ _
  · subst g
    let e := stdOrthonormalBasis ℂ L
    let c := smoothedCriticalAngle tau
    have hc : c ∈ Ioo 0 (Real.pi / 2) := smoothedCriticalAngle_mem tau htau
    obtain ⟨j, hj⟩ := gradient_eigenspace_pairing_of_isLocalMinOn_transports
      tau htau K Q U htrans hmin (((smoothingRadius tau)⁻¹ : ℝ) : ℂ)
    refine ⟨e, fun _ => c, fun _ => c, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [one_mul] using signed_critical_gradient_apply tau 1 htau (Or.inl rfl)
        U (e i) (by
          have hx := Module.End.mem_eigenspace_iff.mp (e i).property
          change smoothedUnitaryGradient tau (U : E →L[ℂ] E) (e i : E) =
            (((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • (e i : E) at hx
          simpa only [one_mul] using hx)
    · intro i
      have hx := Module.End.mem_eigenspace_iff.mp (j (e i)).property
      change smoothedUnitaryGradient tau (U : E →L[ℂ] E) (j (e i) : E) =
        -(((smoothingRadius tau)⁻¹ : ℝ) : ℂ) • (j (e i) : E) at hx
      have hneg := signed_critical_gradient_apply tau (-1) htau (Or.inr rfl) U (j (e i))
        (by simpa only [neg_one_mul, Complex.ofReal_neg] using hx)
      simpa only [neg_one_mul, hj] using hneg
    · intro i
      convert hc using 1; ring
    · intro i
      change (Real.sqrt (tau ^ 2 + ‖Complex.exp ((c : ℂ) * Complex.I) - 1‖ ^ 2) - tau) +
        (Real.sqrt (tau ^ 2 + ‖Complex.exp (((-c : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2) - tau) =
          smoothedPhaseMinimum tau ((c + c) / 2)
      rw [show (c + c) / 2 = c by ring, smoothed_eigenphase_cost_neg,
        smoothedPhaseMinimum_eq_canonical_of_le_critical tau c htau hc.1.le le_rfl, two_mul]
    · intro i
      exact ⟨⟨hc.1, by linarith [hc.2, Real.pi_pos]⟩,
        ⟨hc.1, by linarith [hc.2, Real.pi_pos]⟩⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
