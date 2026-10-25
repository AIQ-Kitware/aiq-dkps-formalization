/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourPrincipalAngles
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseClipping

/-!
# Exact unrestricted real four-dimensional Schatten power minimum

The positive branch uses the unique scalar phase clipped at half the
principal-angle difference. The negative branch reflects the larger-angle
plane. Both the literal power sum and an attaining orthogonal transporter
are compared with the full ambient fiber, including all endpoint cases.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open SchattenPhaseTransition

theorem four_schatten_edgeCost (p h delta : ℝ) (hh : h ≤ Real.pi / 2)
    (hdelta : delta ∈ Set.Icc 0 h) :
    fourEdgeCost (fun s => s ^ p) h delta = 2*phasePower p h delta := by
  rw [fourEdgeCost, fourPhasePenalty, fourPhasePenalty,
    sqrt_displacement_chord_eq_two_sin_half _
      ⟨by linarith [hdelta.1, hdelta.2], by linarith [hdelta.2]⟩,
    sqrt_displacement_chord_eq_two_sin_half _
      ⟨by linarith [hdelta.2], by linarith [hdelta.1, Real.pi_pos]⟩]
  rfl

private theorem four_schatten_edge_minimizer_eq
    (p h d delta : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hd : 0 ≤ d) (hdh : d ≤ h) (hh : h ≤ Real.pi / 2)
    (hdelta : delta ∈ Set.Icc d h)
    (hmin : IsMinOn (fourEdgeCost (fun s => s ^ p) h) (Set.Icc d h) delta) :
    delta = max d (optimalPhase p h) := by
  apply (phasePower_isMinOn_truncated_iff p h d delta hp1 hp2 hd hdh hh hdelta).mp
  intro eta heta
  have hle := hmin heta
  change fourEdgeCost (fun s => s^p) h delta ≤ fourEdgeCost (fun s => s^p) h eta at hle
  change phasePower p h delta ≤ phasePower p h eta
  rw [four_schatten_edgeCost p h delta hh ⟨hd.trans hdelta.1, hdelta.2⟩,
    four_schatten_edgeCost p h eta hh ⟨hd.trans heta.1, heta.2⟩] at hle
  linarith

/-- Closed two-branch Schatten power formula in the full real four-dimensional
model. The attaining parameter is determined by the unique scalar root and clipping. -/
theorem exists_minimizing_four_schatten_transport
    (p h d : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2) :
    ∃ W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
      W.transpose * W = 1 ∧
      W * fourSourceProjection * W.transpose =
        fourCSRotation ![h+d, h-d] * fourSourceProjection *
          (fourCSRotation ![h+d, h-d]).transpose ∧
      fourDisplacementCost (fun s => s ^ p) W =
        min (2*phasePower p h (max d (optimalPhase p h)))
          ((2 : ℝ)^p + 2*phaseChord (h-d)^p) ∧
      IsMinOn (fourDisplacementCost (fun s => s ^ p))
        {X | X.transpose * X = 1 ∧
          X * fourSourceProjection * X.transpose =
            fourCSRotation ![h+d, h-d] * fourSourceProjection *
              (fourCSRotation ![h+d, h-d]).transpose} W := by
  have hp : 0 < p := by linarith
  obtain ⟨delta, hdelta, hscalar, W, hW, htrans, hcost, hmin⟩ :=
    exists_minimizing_four_transport h d hd hdh hhd (fun s => s^p)
      (fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hp.le)
      (Real.continuous_rpow_const hp.le).continuousOn (Real.zero_rpow hp.ne')
  have hh : h ≤ Real.pi / 2 := by linarith
  have heq := four_schatten_edge_minimizer_eq p h d delta hp1 hp2 hd hdh hh hdelta hscalar
  refine ⟨W, hW, htrans, ?_, hmin⟩
  rw [hcost, four_schatten_edgeCost p h delta hh ⟨hd.trans hdelta.1, hdelta.2⟩, heq,
    fourPhasePenalty, sqrt_displacement_chord_eq_two_sin_half _
      ⟨by linarith, by linarith [Real.pi_pos]⟩]
  rfl

/-- Sharp real four-dimensional Schatten canonical-optimality test. Pairing
does not improve precisely when the unconstrained phase lies below `d`;
the independent reflection test only involves the larger angle `h+d`. -/
theorem fourCSRotation_schatten_isMinOn_iff
    (p h d : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hd : 0 ≤ d) (hdh : d ≤ h) (hhd : h+d ≤ Real.pi / 2) :
    IsMinOn (fourDisplacementCost (fun s => s^p))
      {X | X.transpose * X = 1 ∧
        X * fourSourceProjection * X.transpose =
          fourCSRotation ![h+d, h-d] * fourSourceProjection *
            (fourCSRotation ![h+d, h-d]).transpose}
      (fourCSRotation ![h+d, h-d]) ↔
      optimalPhase p h ≤ d ∧ 2*phaseChord (h+d)^p ≤ (2 : ℝ)^p := by
  have hp : 0 < p := by linarith
  have hh : h ≤ Real.pi / 2 := by linarith
  rw [fourCSRotation_isMinOn_iff h d hd hdh hhd (fun s => s^p)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hp.le)
    (Real.continuous_rpow_const hp.le).continuousOn (Real.zero_rpow hp.ne')]
  have hphase : fourPhasePenalty (fun s => s^p) (h+d) = phaseChord (h+d)^p := by
    rw [fourPhasePenalty, sqrt_displacement_chord_eq_two_sin_half _
      ⟨by linarith, by linarith [Real.pi_pos]⟩]
    rfl
  rw [hphase]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro hmin
    have heq := four_schatten_edge_minimizer_eq p h d d hp1 hp2 hd hdh hh
      ⟨le_rfl, hdh⟩ hmin
    rw [heq]
    exact le_max_right _ _
  · intro hopt
    have hphaseMin := (phasePower_clipped_optimalPhase p h d hp1 hp2 hd hdh hh).2
    rw [max_eq_left hopt] at hphaseMin
    intro eta heta
    change fourEdgeCost (fun s => s^p) h d ≤ fourEdgeCost (fun s => s^p) h eta
    rw [four_schatten_edgeCost p h d hh ⟨hd, hdh⟩,
      four_schatten_edgeCost p h eta hh ⟨hd.trans heta.1, heta.2⟩]
    exact mul_le_mul_of_nonneg_left (hphaseMin heta) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exact Schatten power minimum for arbitrary real rank-two subspaces
in ambient dimension four. All ambient orthogonal transporters are compared;
the two angle parameters are the actual accepted principal angles. -/
theorem exists_minimizing_real_four_schatten_transport_principalAngles
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (hL : Module.finrank ℝ L = 2) :
    let h := (K.principalAngles L 0 + K.principalAngles L 1)/2
    let d := (K.principalAngles L 0 - K.principalAngles L 1)/2
    ∃ A : E →ₗ[ℝ] E,
      A.adjoint ∘ₗ A = LinearMap.id ∧
      A ∘ₗ K.starProjection.toLinearMap ∘ₗ A.adjoint = L.starProjection.toLinearMap ∧
      realSpectralDisplacementCost (fun s => s^p) A =
        min (2*phasePower p h (max d (optimalPhase p h)))
          ((2 : ℝ)^p + 2*phaseChord (K.principalAngles L 1)^p) ∧
      IsMinOn (realSpectralDisplacementCost (fun s => s^p))
        {B | B.adjoint ∘ₗ B = LinearMap.id ∧
          B ∘ₗ K.starProjection.toLinearMap ∘ₗ B.adjoint = L.starProjection.toLinearMap} A := by
  classical
  dsimp only
  let h := (K.principalAngles L 0 + K.principalAngles L 1)/2
  let d := (K.principalAngles L 0 - K.principalAngles L 1)/2
  have ht : h+d = K.principalAngles L 0 := by dsimp [h, d]; ring
  have hu : h-d = K.principalAngles L 1 := by dsimp [h, d]; ring
  have hd : 0 ≤ d := by
    have ho := K.principalAngles_antitone L (show 0 ≤ (1 : ℕ) by omega)
    dsimp [d]
    linarith
  have hdh : d ≤ h := by linarith [K.principalAngles_nonneg L 1]
  have hh : h ≤ Real.pi / 2 := by linarith [K.principalAngles_le_pi_div_two L 0]
  have hp : 0 < p := by linarith
  obtain ⟨delta, hdelta, hscalar, A, hA, htrans, hcost, hmin⟩ :=
    exists_minimizing_real_four_transport_principalAngles K L hE hK hL (fun s => s^p)
      (fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hp.le)
      (Real.continuous_rpow_const hp.le).continuousOn (Real.zero_rpow hp.ne')
  have heq := four_schatten_edge_minimizer_eq p h d delta hp1 hp2 hd hdh hh hdelta hscalar
  refine ⟨A, hA, htrans, ?_, hmin⟩
  rw [hcost, four_schatten_edgeCost p h delta hh ⟨hd.trans hdelta.1, hdelta.2⟩, heq,
    fourPhasePenalty, sqrt_displacement_chord_eq_two_sin_half _
      ⟨K.principalAngles_nonneg L 1, (K.principalAngles_le_pi_div_two L 1).trans
        (by linarith [Real.pi_pos])⟩]
  rfl

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
