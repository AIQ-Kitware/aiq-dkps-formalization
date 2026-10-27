/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified) (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierGradientHilbert
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Locally uniform convergence of Charbonnier phase-gradient pairings

A convergent unitary sequence and any continuous unitary variation give
uniformly convergent gradient pairings on compact time intervals. This
provides the derivative-limit input for finite-rank variation arguments
without assuming uniform continuity on the whole unitary group.
-/

public section

namespace TauCeti

open Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Operator-norm convergence of unitaries gives uniform convergence
of their phase-gradient pairings along a fixed unitary curve on every
compact real interval, including passages through identity. -/
theorem tendstoUniformlyOn_smoothed_gradient_pairing_mul_curve
    (tau : ℝ) (hτ : 0 < tau)
    (U : unitary (E →L[ℂ] E)) (Uₙ : ℕ → unitary (E →L[ℂ] E))
    (hU : Tendsto Uₙ atTop (𝓝 U))
    (V : ℝ → unitary (E →L[ℂ] E)) (hV : Continuous V)
    (x : E) (a b : ℝ) :
    TendstoUniformlyOn
      (fun n t => (inner ℂ x (smoothedUnitaryGradient tau ((Uₙ n * V t :
        unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)).re)
      (fun t => (inner ℂ x (smoothedUnitaryGradient tau ((U * V t :
        unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)).re) atTop (Set.Icc a b) := by
  let D (W : unitary (E →L[ℂ] E)) (t : ℝ) :=
    (inner ℂ x (smoothedUnitaryGradient tau ((W * V t :
      unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)).re
  have hD : Continuous (fun z : unitary (E →L[ℂ] E) × ℝ => D z.1 z.2) := by
    have hmul : Continuous (fun z : unitary (E →L[ℂ] E) × ℝ => z.1 * V z.2) :=
      continuous_fst.mul (hV.comp continuous_snd)
    have hgrad := (continuous_smoothedUnitaryGradient_unitary tau hτ).comp hmul
    exact Complex.continuous_re.comp (continuous_const.inner (hgrad.clm_apply continuous_const))
  let C := insert U (Set.range Uₙ)
  have hcompact : IsCompact C := hU.isCompact_insert_range
  have hunif : UniformContinuousOn (fun z => D z.1 z.2) (C ×ˢ Set.Icc a b) :=
    (hcompact.prod isCompact_Icc).uniformContinuousOn_of_continuous hD.continuousOn
  have hwithin : Tendsto Uₙ atTop (𝓝[C] U) :=
    tendsto_nhdsWithin_iff.mpr ⟨hU, Eventually.of_forall fun n =>
      Set.mem_insert_of_mem _ ⟨n, rfl⟩⟩
  have hlim := UniformContinuousOn.tendstoUniformlyOn (F := D) hunif
    (Set.mem_insert U (Set.range Uₙ))
  intro s hs
  exact hwithin.eventually (hlim s hs)

end TauCeti
