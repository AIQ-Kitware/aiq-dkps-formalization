/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenUnitaryApproximation
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite

/-!
# Finite-rank updates inside an exact Schatten transport fiber

Two Schatten perturbations of identity transporting the same source
operator to the same target differ by a source-commuting unitary factor.
Truncate that factor while preserving its commutant and multiply by the
reference transporter. The resulting finite-rank updates stay in the
original fiber and converge in Schatten norm.

## Provenance

Classical restricted-unitary approximation and conjugacy, implemented
here for the DKPS infinite-dimensional optimization proof. The source
and target may be arbitrary bounded operators, and the ambient Hilbert
space may be nonseparable. All gauges are accepted Tau Ceti families.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped Topology ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Conjugation of a bounded operator by an isometric equivalence is
equivalent to its pointwise intertwining equation. -/
private theorem unitary_conjugate_iff_intertwines
    (U : E ≃ₗᵢ[𝕜] E) (P Q : E →L[𝕜] E) :
    (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q ↔
      ∀ x, U (P x) = Q (U x) := by
  have hstar : star (U : E →L[𝕜] E) = (U.symm : E →L[𝕜] E) := U.adjoint_eq_symm
  rw [hstar]
  constructor
  · intro h x
    have hx := congrArg (fun T : E →L[𝕜] E => T (U x)) h
    change U (P (U.symm (U x))) = Q (U x) at hx
    rwa [U.symm_apply_apply] at hx
  · intro h
    ext x
    change U (P (U.symm x)) = Q x
    rw [h, U.apply_symm_apply]

/-- Finite-rank updates of any feasible Schatten transporter are dense
in its exact transport fiber in Schatten norm. Every approximant has
the original target, rather than merely an approximating target. -/
theorem exists_schatten_transport_finite_update_sequence
    (p : ℝ) (hp : 1 ≤ p) (P Q : E →L[𝕜] E) (R U : E ≃ₗᵢ[𝕜] E)
    (hR : (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((R : E →L[𝕜] E) - 1) ≠ ∞)
    (hU : (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((U : E →L[𝕜] E) - 1) ≠ ∞)
    (hRP : (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E) = Q)
    (hUP : (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q) :
    ∃ V : ℕ → E ≃ₗᵢ[𝕜] E, ∃ N : ℕ → ℕ,
      (∀ n, (V n : E →L[𝕜] E) * P * star (V n : E →L[𝕜] E) = Q) ∧
      (∀ n, ((R : E →L[𝕜] E) - (V n : E →L[𝕜] E)).rank ≤ N n) ∧
      Tendsto (fun n => (V n : E →L[𝕜] E)) atTop (𝓝 (U : E →L[𝕜] E)) ∧
      Tendsto (fun n => (OperatorIdealFamily.schatten 𝕜 p hp).gauge
        ((V n : E →L[𝕜] E) - (U : E →L[𝕜] E))) atTop (𝓝 0) := by
  let Φ := OperatorIdealFamily.schatten 𝕜 p hp
  let Z := U.trans R.symm
  have hUR : Φ.gauge ((U : E →L[𝕜] E) - (R : E →L[𝕜] E)) < ∞ := by
    have hfac : (U : E →L[𝕜] E) - (R : E →L[𝕜] E) =
        ((U : E →L[𝕜] E) - 1) + -((R : E →L[𝕜] E) - 1) := by abel
    rw [hfac]
    exact (Φ.gauge_add_le _ _).trans_lt (by
      rw [Φ.gauge_neg]
      exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hU, lt_top_iff_ne_top.mpr hR⟩)
  have hZfac : (Z : E →L[𝕜] E) - 1 =
      (R.symm : E →L[𝕜] E) ∘L ((U : E →L[𝕜] E) - (R : E →L[𝕜] E)) := by
    ext x
    change R.symm (U x) - x = R.symm (U x - R x)
    rw [map_sub, R.symm_apply_apply]
  have hZ : Φ.gauge ((Z : E →L[𝕜] E) - 1) ≠ ∞ := by
    rw [hZfac, Φ.gauge_comp_linearIsometryEquiv_left]
    exact hUR.ne
  have hRP' := (unitary_conjugate_iff_intertwines R P Q).mp hRP
  have hUP' := (unitary_conjugate_iff_intertwines U P Q).mp hUP
  have hZP : Commute (Z : E →L[𝕜] E) P := by
    ext x
    change R.symm (U (P x)) = P (R.symm (U x))
    apply R.injective
    rw [R.apply_symm_apply, hUP', hRP', R.apply_symm_apply]
  obtain ⟨S, N, hN, hlim, hS, _, hcomm⟩ :=
    exists_schatten_finite_unitary_approximation_sequence p hp Z hZ
  let V (n : ℕ) := (S n).trans R
  have hVfac (n : ℕ) : (V n : E →L[𝕜] E) = (R : E →L[𝕜] E) * (S n : E →L[𝕜] E) := by
    ext x
    rfl
  have hRZ : (R : E →L[𝕜] E) * (Z : E →L[𝕜] E) = (U : E →L[𝕜] E) := by
    ext x
    exact R.apply_symm_apply (U x)
  have herror (n : ℕ) : (V n : E →L[𝕜] E) - (U : E →L[𝕜] E) =
      (R : E →L[𝕜] E) ∘L ((S n : E →L[𝕜] E) - (Z : E →L[𝕜] E)) := by
    ext x
    change R (S n x) - U x = R (S n x - R.symm (U x))
    rw [map_sub, R.apply_symm_apply]
  refine ⟨V, N, ?_, ?_, ?_, ?_⟩
  · intro n
    apply (unitary_conjugate_iff_intertwines (V n) P Q).mpr
    intro x
    have hScomm := congrArg (fun T : E →L[𝕜] E => T x) (hcomm n P hZP).eq
    change S n (P x) = P (S n x) at hScomm
    change R (S n (P x)) = Q (R (S n x))
    rw [hScomm, hRP']
  · intro n
    have hfac : (R : E →L[𝕜] E) - (V n : E →L[𝕜] E) =
        (R : E →L[𝕜] E) ∘L (1 - (S n : E →L[𝕜] E)) := by
      ext x
      change R x - R (S n x) = R (x - S n x)
      rw [map_sub]
    rw [hfac]
    have h := LinearMap.lift_rank_comp_le_right
      (1 - (S n : E →L[𝕜] E)).toLinearMap (R : E →L[𝕜] E).toLinearMap
    have h' : ((R : E →L[𝕜] E) ∘L (1 - (S n : E →L[𝕜] E))).rank ≤
        (1 - (S n : E →L[𝕜] E)).rank := by
      simpa only [Cardinal.lift_id, ContinuousLinearMap.toLinearMap_comp] using h
    exact h'.trans (hN n)
  · simp_rw [hVfac]
    rw [← hRZ]
    exact hlim.const_mul (R : E →L[𝕜] E)
  · change Tendsto (fun n => Φ.gauge ((V n : E →L[𝕜] E) - (U : E →L[𝕜] E)))
      atTop (𝓝 0)
    simp_rw [herror, Φ.gauge_comp_linearIsometryEquiv_left]
    exact hS

/-- A lower bound on an exact Schatten transport fiber can be checked
on finite-rank updates of one feasible Schatten reference. Competitors
of infinite cost are included in the unrestricted conclusion. -/
theorem schatten_transport_lower_bound_iff_finite_updates
    (p : ℝ) (hp : 1 ≤ p) (P Q : E →L[𝕜] E) (R : E ≃ₗᵢ[𝕜] E)
    (hR : (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((R : E →L[𝕜] E) - 1) ≠ ∞)
    (hRP : (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E) = Q) (c : ℝ≥0∞) :
    (∀ U : E ≃ₗᵢ[𝕜] E,
      (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q →
      c ≤ (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((U : E →L[𝕜] E) - 1)) ↔
    (∀ U : E ≃ₗᵢ[𝕜] E,
      (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q →
      (∃ n : ℕ, ((R : E →L[𝕜] E) - (U : E →L[𝕜] E)).rank ≤ n) →
      c ≤ (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((U : E →L[𝕜] E) - 1)) := by
  constructor
  · intro h U hU _
    exact h U hU
  · intro h U hUP
    let Φ := OperatorIdealFamily.schatten 𝕜 p hp
    by_cases hU : Φ.gauge ((U : E →L[𝕜] E) - 1) = ∞
    · exact hU ▸ le_top
    obtain ⟨V, N, hVP, hN, _, hlim⟩ :=
      exists_schatten_transport_finite_update_sequence p hp P Q R U hR hU hRP hUP
    have hbound (n : ℕ) : c ≤ Φ.gauge ((U : E →L[𝕜] E) - 1) +
        Φ.gauge ((V n : E →L[𝕜] E) - (U : E →L[𝕜] E)) := by
      have hcost := h (V n) (hVP n) ⟨N n, hN n⟩
      have hfac : (V n : E →L[𝕜] E) - 1 = ((U : E →L[𝕜] E) - 1) +
          ((V n : E →L[𝕜] E) - (U : E →L[𝕜] E)) := by abel
      exact hcost.trans (hfac ▸ Φ.gauge_add_le _ _)
    have hsum := hlim.const_add (Φ.gauge ((U : E →L[𝕜] E) - 1))
    rw [add_zero] at hsum
    exact ge_of_tendsto' hsum hbound

/-- If a transport fiber contains a finite-rank perturbation of identity,
every Schatten lower bound can be checked on finite-rank perturbations
of identity. The unrestricted conclusion covers all ambient competitors. -/
theorem schatten_transport_lower_bound_iff_finite_rank
    (p : ℝ) (hp : 1 ≤ p) (P Q : E →L[𝕜] E) (R : E ≃ₗᵢ[𝕜] E)
    (n : ℕ) (hR : (1 - R.toLinearMap).rank ≤ n)
    (hRP : (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E) = Q) (c : ℝ≥0∞) :
    (∀ U : E ≃ₗᵢ[𝕜] E,
      (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q →
      c ≤ (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((U : E →L[𝕜] E) - 1)) ↔
    (∀ U : E ≃ₗᵢ[𝕜] E,
      (U : E →L[𝕜] E) * P * star (U : E →L[𝕜] E) = Q →
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) →
      c ≤ (OperatorIdealFamily.schatten 𝕜 p hp).gauge ((U : E →L[𝕜] E) - 1)) := by
  constructor
  · intro h U hU _
    exact h U hU
  · intro h
    let Φ := OperatorIdealFamily.schatten 𝕜 p hp
    have hRfinite : Φ.gauge ((R : E →L[𝕜] E) - 1) ≠ ∞ := by
      rw [← neg_sub 1 (R : E →L[𝕜] E), Φ.gauge_neg]
      exact OperatorIdealFamily.gauge_schatten_ne_top_of_rank_le p hp
        (1 - (R : E →L[𝕜] E)) n hR
    apply (schatten_transport_lower_bound_iff_finite_updates p hp P Q R hRfinite hRP c).mpr
    intro U hUP ⟨m, hm⟩
    apply h U hUP
    refine ⟨n + m, ?_⟩
    have hfac : 1 - U.toLinearMap = (1 - R.toLinearMap) +
        ((R : E →L[𝕜] E) - (U : E →L[𝕜] E)).toLinearMap := by
      ext x
      change x - U x = (x - R x) + (R x - U x)
      abel
    rw [hfac]
    exact (LinearMap.rank_add_le _ _).trans (by
      simpa only [Nat.cast_add] using add_le_add hR hm)

end TauCeti
