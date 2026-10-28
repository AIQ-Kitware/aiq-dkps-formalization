/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerGlobalAttainment

/-!
# The zero-smoothing boundary of the common transport theorem

Continuity of finite spectral costs and compact scalar minimum values passes
the common ambient lower bound to zero smoothing. The independent canonical
phase construction attains that boundary value directly. This argument does
not pass a claim about whole optimizer sets through the limit and does not
invoke the older Schatten/nuclear global minimum theorems.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set Filter
open scoped BigOperators Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The actual finite unitary spectral cost varies continuously with
smoothing, including at zero. This is a value statement. -/
theorem continuous_displacementCost_smoothing (p : ℝ) (hp : 0 ≤ p)
    (U : unitary (E →L[ℂ] E)) :
    Continuous (fun tau => displacementCost p tau (U : E →L[ℂ] E)) := by
  let := isStarNormal_of_mem_unitary U.property
  have heq (tau : ℝ) : displacementCost p tau (U : E →L[ℂ] E) =
      ∑ i : Fin (Module.finrank ℂ E),
        penalty p tau ((LinearMap.id - (U : E →L[ℂ] E).toLinearMap).singularValues i) :=
    normalDisplacementSpectralCost_eq_sum_singularValues (penalty p tau) (U : E →L[ℂ] E)
  simp_rw [heq]
  apply continuous_finsetSum
  intro i _
  unfold penalty
  exact (((continuous_id.pow 2).add continuous_const).rpow_const
    (fun _ => Or.inr (by linarith : 0 ≤ p / 2))).sub
      (continuous_id.rpow_const (fun _ => Or.inr hp))

/-- The common unrestricted lower bound at zero smoothing, obtained by
continuity of values rather than convergence of optimizer sets. -/
theorem sum_phaseMinimum_zero_le_transport
    (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L) :
    (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p 0 (K.principalAngles L i)) ≤
      displacementCost p 0 (U : E →L[ℂ] E) := by
  have hf : Continuous (fun tau =>
      ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_phaseMinimum_smoothing p _ (by linarith)
  have hg := continuous_displacementCost_smoothing p (by linarith) U
  have hevent : ∀ᶠ tau in 𝓝[>] (0 : ℝ),
      (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ≤
        displacementCost p tau (U : E →L[ℂ] E) := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    exact sum_phaseMinimum_le_transport p tau hp hp2 htau K L U hmap
  exact le_of_tendsto_of_tendsto
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent

/-- **The exact common minimum for the full closed family.** Let `1<=p<=2`
and `tau>=0`. On every finite complex transport fiber of equal-rank
subspaces, the minimum is the sum of the attained planar minima over the
accepted principal angles. Every ambient unitary competitor is included.
This does not classify every optimizer or assert the full C2 phase law. -/
theorem exists_unitary_minimizing_transport_principalAngles_of_nonneg
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      displacementCost p tau (W : E →L[ℂ] E) =
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ≤
          displacementCost p tau (T : E →L[ℂ] E) := by
  obtain ⟨W, hW, hcost⟩ := exists_unitary_attaining_principalAngles p tau (by linarith) htau K L hKL
  refine ⟨W, hW, hcost, ?_⟩
  intro T hT
  let U := Unitary.linearIsometryEquiv.symm T
  have hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L := by
    simpa only [U, MulEquiv.apply_symm_apply] using hT
  by_cases hz : tau = 0
  · subst tau
    exact sum_phaseMinimum_zero_le_transport p hp hp2 K L U hmap
  · exact sum_phaseMinimum_le_transport p tau hp hp2 (lt_of_le_of_ne htau (Ne.symm hz)) K L U hmap

/-- The boundary penalty is the usual positive power on nonnegative
singular values. The normalization at zero is included. -/
theorem penalty_zero_smoothing (p s : ℝ) (hp : 0 < p) (hs : 0 ≤ s) :
    penalty p 0 s = s ^ p := by
  simp only [penalty, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    Real.zero_rpow hp.ne', sub_zero]
  rw [← Real.rpow_natCast_mul hs]
  congr 1
  ring

/-- At zero smoothing the common literal objective is exactly the native
Schatten power, including the nuclear and quadratic endpoints. -/
theorem displacementCost_zero_smoothing (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (U : unitary (E →L[ℂ] E)) :
    displacementCost p.toReal 0 (U : E →L[ℂ] E) =
      UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal := by
  let := isStarNormal_of_mem_unitary U.property
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  change normalDisplacementSpectralCost (penalty p.toReal 0) (U : E →L[ℂ] E) = _
  rw [normalDisplacementSpectralCost_eq_sum_singularValues]
  have hcost := schatten_rpow_eq_sum_singularValue p hp (1 - (U : E →L[ℂ] E))
  change UnitarilyInvariantSeminorm.schatten ℂ E E p
    (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal = _ at hcost
  rw [hcost]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
  exact penalty_zero_smoothing p.toReal _ hp0
    ((LinearMap.id - (U : E →L[ℂ] E).toLinearMap).singularValues_nonneg i)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
