/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerBoundary
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerPhaseEndpoints

/-!
# The common unrestricted canonical-rotation criterion

The ambient value theorem C1 and the scalar law C2 imply that canonical
rotation is globally optimal exactly when every principal angle lies in
the common closed canonical regime. Zero and right angles and zero smoothing
are included. This is a complex-field theorem, not a real matching assertion.

The canonical geometry and quadratic case are classical (Davis 1958;
Bolotnikov--Li--Rodman 2001). The full family criterion is a transport
extension whose exact historical priority remains unresolved; the scalar
penalty itself is established prior art. See the maintained provenance map.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Canonical rotation's literal family cost is its scalar canonical-angle
sum, including crossed defects and unused common directions. -/
theorem nonacuteDirectRotation_displacementCost_eq_sum (p tau : ℝ) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    displacementCost p tau (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)) =
      ∑ i : Fin (Module.finrank ℂ K), phaseCost p tau (K.principalAngles L i) 0 := by
  classical
  let D := finiteCrossedDefectEquiv K L hKL
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, _⟩ :=
    SmoothedPhaseTransition.exists_subspace_paired_rotation_reflection_basis_complex K L hKL
  have hZp (r i) : (LinearIsometryEquiv.refl ℂ E) (e (.inl (r, i))) =
      Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • e (.inl (r, i)) := by simp
  have hZf (j) : (LinearIsometryEquiv.refl ℂ E) (e (.inr j)) = e (.inr j) := rfl
  have hcost := paired_phase_transport_cost p tau htau e theta (fun _ => 0)
    R (LinearIsometryEquiv.refl ℂ E) hR0 hR1 hRf hZp hZf
  change displacementCost p tau (nonacuteDirectRotation K L D) = _ at hcost
  have hsum := SmoothedPhaseTransition.sum_principalAngles_eq_paired_sum K L e theta hθ
    hC0 hC1 hCf hJ0 (fun t => phaseCost p tau t 0) (phaseCost_zero_angle p tau htau)
  exact hcost.trans hsum.symm

/-- **The common unrestricted canonical-rotation criterion.** On every
finite complex equal-rank transport fiber, canonical rotation minimizes the
literal cost for the full closed family exactly when all principal-angle
cosines lie above the critical surface. This concerns minimum values;
quadratic right-angle ties and other optimizer freedoms are retained. -/
theorem nonacuteDirectRotation_isMin_iff_principalAngles_critical
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    IsMinOn (displacementCost p tau)
        {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
        (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)) ↔
      ∀ i : Fin (Module.finrank ℂ K),
        smoothedPowerCriticalCosine p tau ≤ Real.cos (K.principalAngles L i) := by
  classical
  have hcost := nonacuteDirectRotation_displacementCost_eq_sum p tau htau K L hKL
  have hθ (i : Fin (Module.finrank ℂ K)) : K.principalAngles L i ∈ Icc 0 (Real.pi / 2) :=
    ⟨K.principalAngles_nonneg L i, K.principalAngles_le_pi_div_two L i⟩
  have hle (i : Fin (Module.finrank ℂ K)) :
      phaseMinimum p tau (K.principalAngles L i) ≤ phaseCost p tau (K.principalAngles L i) 0 :=
    phaseMinimum_le_cost p tau _ 0 (by linarith) htau ⟨le_rfl, (hθ i).1⟩
  obtain ⟨V, hVmap, hVcost, hbound⟩ :=
    exists_unitary_minimizing_transport_principalAngles_of_nonneg p tau hp hp2 htau K L hKL
  constructor
  · intro hm
    have hVunit : (V : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
      (Unitary.linearIsometryEquiv.symm V).property
    have hVtrans := (K.map_eq_iff_conjugate_starProjection L V).mp hVmap
    have hsum := hm ⟨hVunit, hVtrans⟩
    change displacementCost p tau (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)) ≤
      displacementCost p tau (V : E →L[ℂ] E) at hsum
    rw [hcost, hVcost] at hsum
    have heq := le_antisymm (Finset.sum_le_sum fun i _ => hle i) hsum
    intro i
    have hi := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp heq i (Finset.mem_univ i)
    exact (phaseMinimum_eq_canonical_iff p tau _ hp hp2 htau (hθ i)).mp hi
  · intro hc W hW
    change displacementCost p tau (nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL)) ≤
      displacementCost p tau W
    let U : unitary (E →L[ℂ] E) := ⟨W, hW.1⟩
    let T := Unitary.linearIsometryEquiv U
    have hTmap : K.map T.toLinearMap = L :=
      (K.map_eq_iff_conjugate_starProjection L T).mpr hW.2
    rw [hcost]
    have hsum : (∑ i : Fin (Module.finrank ℂ K), phaseCost p tau (K.principalAngles L i) 0) =
        ∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ((phaseMinimum_eq_canonical_iff p tau _ hp hp2 htau (hθ i)).mpr (hc i)).symm
    rw [hsum]
    exact hbound T hTmap

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
