/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenNuclearEndpoint
public import DavisKahan.Geometry.Polar.NuclearSignedPhases

/-!
# The complete nuclear uniqueness threshold

An arbitrary orthogonally complemented complex projection pair has a
unique global nuclear transporter exactly when the subspaces agree.
For finite optimum cost, opposite common phases force a positive
optimizer separation whenever the projection gap is nonzero. If the
optimum is infinite, negating a transporter rules out uniqueness except
on the zero space. No ideal membership, balance or feasibility hypothesis
is imposed in the criterion.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Exact nuclear uniqueness criterion.** The unrestricted native
extended nuclear problem has a unique global optimizer precisely for
identical subspaces. The statement includes noncompact pairs, empty
transport fibers and infinite-cost feasible fibers. -/
theorem nuclear_transport_unique_minimizer_iff_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∃! U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (T : E →L[ℂ] E))) ↔
      K = L := by
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  constructor
  · rintro ⟨U, hU, huni⟩
    by_cases hfinite : Φ.gauge (1 - (U : E →L[ℂ] E)) ≠ ∞
    · obtain ⟨hKL, hbalance⟩ := (schatten_transport_iff_projection_sub_ne_top_and_defect_balance
        1 (by norm_num) K L).mp ⟨U, hU.1, hfinite⟩
      have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
        1 (by norm_num) (K.starProjection - L.starProjection) hKL
      obtain ⟨D⟩ := crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq
        K L hcompact hbalance
      have hplus := huni (nuclearPhaseRotation_complex K L D)
        ⟨nuclearPhaseRotation_map_complex K L D, nuclearPhaseRotation_isMin_complex K L D⟩
      have hminus := huni (negativeNuclearPhaseRotation_complex K L D)
        ⟨negativeNuclearPhaseRotation_map_complex K L D,
          negativeNuclearPhaseRotation_isMin_complex K L D⟩
      have heq := hplus.trans hminus.symm
      have hgap := norm_nuclearPhaseRotation_sub_negative_complex K L D
      rw [heq, sub_self, norm_zero] at hgap
      apply Submodule.starProjection_inj.mp
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (K.starProjection - L.starProjection)]
    · have htop : Φ.gauge (1 - (U : E →L[ℂ] E)) = ∞ := not_ne_iff.mp hfinite
      let V := U.trans (LinearIsometryEquiv.neg ℂ)
      have hVmap : K.map V.toLinearMap = L := by
        apply (K.map_eq_iff_intertwines_reflection L V).mpr
        intro x
        change -(U (K.reflection x)) = L.reflection (-(U x))
        rw [map_neg, (K.map_eq_iff_intertwines_reflection L U).mp hU.1 x]
      have hVmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
          Φ.gauge (1 - (V : E →L[ℂ] E)) ≤ Φ.gauge (1 - (T : E →L[ℂ] E)) := by
        intro T hT
        have hTtop : Φ.gauge (1 - (T : E →L[ℂ] E)) = ∞ := by
          apply top_le_iff.mp
          have h := hU.2 T hT
          change Φ.gauge (1 - (U : E →L[ℂ] E)) ≤ Φ.gauge (1 - (T : E →L[ℂ] E)) at h
          rwa [htop] at h
        rw [hTtop]
        exact le_top
      have heq : V = U := huni V ⟨hVmap, hVmin⟩
      have hzero (x : E) : x = 0 := by
        have hx := congrArg (fun T : E ≃ₗᵢ[ℂ] E => T (U.symm x)) heq
        change -(U (U.symm x)) = U (U.symm x) at hx
        rw [U.apply_symm_apply] at hx
        have htwo : (2 : ℂ) • x = 0 := by
          rw [two_smul]
          exact add_eq_zero_iff_eq_neg.mpr hx.symm
        exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      apply Submodule.starProjection_inj.mp
      ext x
      rw [hzero (K.starProjection x), hzero (L.starProjection x)]
  · rintro rfl
    let I := LinearIsometryEquiv.refl ℂ E
    have hImap : K.map I.toLinearMap = K := by simp [I]
    have hIcost : Φ.gauge (1 - (I : E →L[ℂ] E)) = 0 := by
      change Φ.gauge (1 - 1) = 0
      rw [sub_self, Φ.gauge_zero]
    refine ⟨I, ⟨hImap, ?_⟩, ?_⟩
    · intro T _
      rw [hIcost]
      exact bot_le
    · intro V hV
      have hcost : Φ.gauge (1 - (V : E →L[ℂ] E)) = 0 := by
        apply le_antisymm _ bot_le
        have h := hV.2 I hImap
        change Φ.gauge (1 - (V : E →L[ℂ] E)) ≤ Φ.gauge (1 - (I : E →L[ℂ] E)) at h
        rwa [hIcost] at h
      have hdisp := (Φ.gauge_eq_zero_iff _).mp hcost
      have hVeq : (V : E →L[ℂ] E) = 1 := (sub_eq_zero.mp hdisp).symm
      ext x
      exact congrArg (fun T : E →L[ℂ] E => T x) hVeq

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
