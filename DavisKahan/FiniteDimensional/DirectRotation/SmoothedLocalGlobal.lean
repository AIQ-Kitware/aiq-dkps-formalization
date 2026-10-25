/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralDecomposition
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedReflectionOptimality
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalLowerBound
import ForTauCeti.Analysis.InnerProductSpace.InvariantKernel

/-!
# Every complex Charbonnier transport local minimum is global

The positive gradient pairs attain their exact scalar minima. The actual
kernel is a balanced reflection whose fixed/right principal-angle trace
equals its literal cost. Adding the two traces gives the unrestricted
angle sum and therefore compares the local minimum with every competitor.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every actual local Charbonnier transport minimum attains the exact
unrestricted principal-angle value. Zero, critical and right angles,
repeated phases, fixed spaces and arbitrary ranks are included. -/
theorem smoothed_transport_cost_eq_sum_of_isLocalMinOn_complex
    (tau : ℝ) (htau : 0 < tau) (K L : Submodule ℂ E)
    (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    smoothedDisplacementCost tau (U : E →L[ℂ] E).toLinearMap =
      ∑ i : Fin (Module.finrank ℂ K), smoothedPhaseMinimum tau (K.principalAngles L i) := by
  let G := smoothedUnitaryGradient tau (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  have ht := (SchattenPhaseTransition.map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨n, e, alpha, beta, V, W, R, d, hV, hW, hR, _, hd, _, hVe, hWe,
    hmean, hcost, _⟩ := smoothed_transport_spectral_decomposition_of_isLocalMinOn_complex
      tau htau K L.starProjection U ht hmin
  have hG : G.toLinearMap.IsSymmetric :=
    (isSelfAdjoint_smoothedUnitaryGradient tau (U : E →L[ℂ] E)).isSymmetric
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    tau htau K L.starProjection U ht hmin
  have hkerinv (P : E →L[ℂ] E) (hP : Commute P (G * G)) :
      ∀ x ∈ Z, P x ∈ Z :=
    hG.mapsTo_ker_of_commute_square
      (show Commute P.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hP.eq)
  have hK := hkerinv K.starProjection hPK
  have hL := hkerinv L.starProjection hPL
  have hUfunc (x : E) : (Unitary.linearIsometryEquiv U) x = (U : E →L[ℂ] E) x := by
    simpa only [LinearIsometryEquiv.coe_coe''] using
      congrArg (fun T : E →L[ℂ] E => T x) (Unitary.coe_linearIsometryEquiv_apply U)
  have hRmap : K₀.map R.toLinearMap = L₀ :=
    Submodule.map_comap_subtype_of_isometry_restriction K L Z
      (Unitary.linearIsometryEquiv U) R hmap (fun z => (hR z).trans (hUfunc z).symm)
  have hRcost : smoothedDisplacementCost tau R.toLinearMap =
      ∑ i : Fin (Module.finrank ℂ K₀), smoothedPhaseMinimum tau (K₀.principalAngles L₀ i) := by
    obtain ⟨R₀, A, P₀, hA, _, hR₀, hP₀act, hRrepr, hbalance, _⟩ :=
      gradient_kernel_local_reflection_restriction_complex tau htau K L.starProjection U ht hmin
    have hRR : R₀ = R := by
      apply LinearIsometryEquiv.ext
      intro z
      apply Subtype.ext
      exact (hR₀ z).trans (hR z).symm
    rw [hRR] at hRrepr
    have hP₀eq : P₀ = K₀.starProjection := by
      apply ContinuousLinearMap.ext
      intro z
      apply Subtype.ext
      exact (hP₀act z).trans
        (Submodule.starProjection_comap_subtype_apply_of_invariant K Z hK z).symm
    have hbalance' : (2 : ℂ) • (A * K₀.starProjection * A) = A := by
      rw [← hP₀eq]
      exact hbalance
    exact balanced_reflection_cost_eq_sum_principalAngles_complex tau htau K₀ L₀ A hA
      hbalance' R hRrepr hRmap
  have hu (i) : (Unitary.linearIsometryEquiv U) (e i : E) =
      Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E) := by
    rw [hUfunc, ← hV, hVe, Submodule.coe_smul]
  have hw (i) : (Unitary.linearIsometryEquiv U) (K.reflection (e i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
    rw [hUfunc, ← hW, hWe, Submodule.coe_smul, map_smul]
  have hangles := Submodule.sum_principalAngles_eq_paired_phases_add_comap_complex
    K L H Z (Unitary.linearIsometryEquiv U) hmap e alpha beta hu hw
    (fun i => ⟨(hmean i).1.le, (hmean i).2.le⟩) d hd hK hL
    (smoothedPhaseMinimum tau) (smoothedPhaseMinimum_zero_angle tau htau)
  exact hcost.trans ((congrArg (fun t : ℝ =>
    (∑ i, smoothedPhaseMinimum tau ((alpha i + beta i) / 2)) + t) hRcost).trans hangles.symm)

/-- Every local minimum is global over all finite-dimensional complex
unitary transports for positive Charbonnier smoothing. No spectral or
principal-angle endpoint is excluded. -/
theorem isMinOn_of_isLocalMinOn_transports_complex
    (tau : ℝ) (htau : 0 < tau) (K L : Submodule ℂ E)
    (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    IsMinOn (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
  have hatt := smoothed_transport_cost_eq_sum_of_isLocalMinOn_complex tau htau K L U hmap hmin
  have hKL : Module.finrank ℂ K = Module.finrank ℂ L := by
    rw [← hmap]
    exact ((Unitary.linearIsometryEquiv U).toLinearEquiv.finrank_map_eq K).symm
  obtain ⟨_, _, _, hbound⟩ :=
    exists_unitary_minimizing_smoothed_transport_principalAngles tau htau K L hKL
  intro W hW
  let T : unitary (E →L[ℂ] E) := ⟨W, hW.1⟩
  have hTmap := (SchattenPhaseTransition.map_eq_iff_conjugate_starProjection_complex K L T).mpr hW.2
  have hb := hbound (Unitary.linearIsometryEquiv T) hTmap
  have hTlin : (Unitary.linearIsometryEquiv T).toLinearMap = W.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (Unitary.coe_linearIsometryEquiv_apply T)
  rw [hTlin] at hb
  change smoothedDisplacementCost tau (U : E →L[ℂ] E).toLinearMap ≤
    smoothedDisplacementCost tau W.toLinearMap
  rw [hatt]
  exact hb

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
