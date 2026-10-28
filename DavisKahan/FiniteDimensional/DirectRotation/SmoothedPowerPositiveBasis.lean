/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerGradientNoMixing
public import ForTauCeti.Analysis.InnerProductSpace.OrthogonalProjectionPhases
public import ForTauCeti.Analysis.InnerProductSpace.PositiveSpectralBasis

/-!
# Simultaneous phase coordinates for a local smoothed-power minimum

Actual no-overlap gives a joint phase basis at each positive submaximal
gradient level. The maximal level is scalar. Collecting these bases gives
a basis of the whole positive gradient space paired by the source reflection.

Unlike the earlier penalty-specific scalar-minimum proofs, this structural
step requires no classification of scalar minimizing phases. It retains
all phase pairs in `(0,pi)` and proves their means lie in `(0,pi/2]`.
The exact angle-cost assembly and global minimum formula remain subsequent
obligations.
Classical eigenspace/basis assembly adapts `SmoothedPositiveBasis`.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set

private theorem abs_phaseSlope_le_peak (p tau t : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (ht : |t| ≤ Real.pi) :
    |smoothedPowerPhaseSlope p tau t| ≤ peakSlope p tau := by
  have hc := criticalAngle_mem p tau hp hp2 htau
  have hb (x : ℝ) (hx : x ∈ Icc 0 Real.pi) :
      0 ≤ smoothedPowerPhaseSlope p tau x ∧ smoothedPowerPhaseSlope p tau x ≤ peakSlope p tau := by
    constructor
    · exact mul_nonneg (mul_nonneg (by linarith)
        (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)) (Real.rpow_nonneg (smoothedPowerPhase_radicand_pos tau x htau).le _)
    · rcases le_total x (criticalAngle p tau) with h | h
      · exact (smoothedPowerPhaseSlope_strictMonoOn p tau hp hp2 htau).monotoneOn
          ⟨hx.1, h⟩ ⟨hc.1.le, le_rfl⟩ h
      · exact (smoothedPowerPhaseSlope_strictAntiOn p tau hp hp2 htau).antitoneOn
          ⟨le_rfl, hc.2.le⟩ ⟨h, hx.2⟩ h
  by_cases ht0 : 0 ≤ t
  · have h := hb t ⟨ht0, (le_abs_self t).trans ht⟩
    simpa only [abs_of_nonneg h.1] using h.2
  · have h := hb (-t) ⟨by linarith, (neg_le_abs t).trans ht⟩
    calc
      _ = |smoothedPowerPhaseSlope p tau (-t)| := by rw [phaseSlope_odd, abs_neg]
      _ = smoothedPowerPhaseSlope p tau (-t) := abs_of_nonneg h.1
      _ ≤ _ := h.2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

private theorem positive_gradient_spectrum_le_max (p tau g : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau) (hg0 : 0 < g)
    (U : unitary (E →L[ℂ] E))
    (hg : (g : ℂ) ∈ spectrum ℂ
      (unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E))) :
    g ≤ peakSlope p tau := by
  have hf : ContinuousOn (fun z : ℂ => (smoothedPowerPhaseDerivative p tau z : ℂ))
      (spectrum ℂ (U : E →L[ℂ] E)) :=
    ((U : E →L[ℂ] E).finite_spectrum ℂ).continuousOn _
  change (g : ℂ) ∈ spectrum ℂ
    (cfc (fun z => (smoothedPowerPhaseDerivative p tau z : ℂ)) (U : E →L[ℂ] E)) at hg
  rw [cfc_map_spectrum (R := ℂ) (a := (U : E →L[ℂ] E))
    (f := fun z : ℂ => (smoothedPowerPhaseDerivative p tau z : ℂ)) (by infer_instance) hf] at hg
  obtain ⟨z, hz, hzg⟩ := hg
  have hreal : smoothedPowerPhaseDerivative p tau z = g := Complex.ofReal_injective hzg
  have hnorm := spectrum.norm_eq_one_of_unitary U.property hz
  have hphase : Complex.exp (((z.arg : ℝ) : ℂ) * Complex.I) = z := by
    simpa only [hnorm, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z
  have hs := smoothedPowerPhaseDerivative_exp p tau z.arg
  rw [hphase, hreal] at hs
  have hbound := abs_phaseSlope_le_peak p tau z.arg hp hp2 htau (Complex.abs_arg_le_pi z)
  rwa [← hs, abs_of_pos hg0] at hbound

private theorem signed_critical_gradient_apply
    (p tau s : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (hs : s = 1 ∨ s = -1) (U : unitary (E →L[ℂ] E)) (x : E)
    (hx : unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E) x =
      ((s * peakSlope p tau : ℝ) : ℂ) • x) :
    (U : E →L[ℂ] E) x =
      Complex.exp (((s * criticalAngle p tau : ℝ) : ℂ) * Complex.I) • x := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let D := Module.End.eigenspace G.toLinearMap ((s * peakSlope p tau : ℝ) : ℂ)
  let x' : D := ⟨x, Module.End.mem_eigenspace_iff.mpr hx⟩
  obtain ⟨V, hVact, hV⟩ :=
    signed_critical_gradient_eigenspace_representation p tau s hp hp2 htau hs U
  calc
    _ = (V x' : E) := (hVact x').symm
    _ = _ := congrArg (fun T : D →L[ℂ] D => (T x' : E)) hV

/-- Every actual positive gradient eigenspace at an ambient local minimum
has a source-reflection-paired phase basis, including the maximal level.
No prescribed invariant principal-plane decomposition is assumed. -/
theorem gradient_eigenspace_phase_basis_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q} (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g)
    (hg : (g : ℂ) ∈ spectrum ℂ
      (unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E))) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ L)) ℂ L)
      (alpha beta : Fin (Module.finrank ℂ L) → ℝ),
      (∀ i, (U : E →L[ℂ] E) (e i : E) = Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i)) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioc 0 (Real.pi / 2)) ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
  have hgm := positive_gradient_spectrum_le_max p tau g hp hp2 htau hg0 U hg
  rcases lt_or_eq_of_le hgm with hgm | hgm
  · obtain ⟨a, ha, b, hb, hga, hgb, V, W, A, B, hA, hB, hAB, hVact, hWact, hV, hW⟩ :=
      gradient_block_no_overlap_of_isLocalMinOn_transports p tau hp hp2 htau K Q U htrans hmin
        g hg0 hgm
    obtain ⟨e, alpha, beta, hpair, hVe, hWe⟩ :=
      exists_orthogonal_two_phase_basis_complex a b V W A B hA hB hAB hV hW
    have hc := criticalAngle_mem p tau hp hp2 htau
    have haPi : a ∈ Ioo 0 Real.pi := ⟨ha.1, ha.2.trans hc.2⟩
    have hbPi : b ∈ Ioo 0 Real.pi := ⟨hc.1.trans hb.1, hb.2⟩
    have hC := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
    have hchalf : criticalAngle p tau ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hC.1
    have habsum := balanced_phase_sum_le_pi p tau a b hp hp2 htau ha hb
      (hga.trans hgb.symm)
    refine ⟨e, alpha, beta, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hVact (e i)).symm.trans (congrArg (fun x : L => (x : E)) (hVe i))
    · intro i
      rw [← hWact, hWe]
      exact K.reflection.map_smul _ _
    · intro i
      rcases hpair i with h | h | h
      · rw [h.1, h.2]; exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
      · rw [h.1, h.2]; exact ⟨by linarith [haPi.1, hbPi.1], by linarith⟩
      · rw [h.1, h.2]; exact ⟨by linarith [haPi.1, hbPi.1], by linarith⟩
    · intro i
      rcases hpair i with h | h | h
      · rw [h.1, h.2]; exact ⟨haPi, haPi⟩
      · rw [h.1, h.2]; exact ⟨hbPi, haPi⟩
      · rw [h.1, h.2]; exact ⟨haPi, hbPi⟩
  · subst g
    let e := stdOrthonormalBasis ℂ L
    let c := criticalAngle p tau
    have hc : c ∈ Ioo 0 Real.pi := criticalAngle_mem p tau hp hp2 htau
    obtain ⟨j, hj⟩ := gradient_eigenspace_pairing_of_isLocalMinOn_transports
      p tau hp htau K Q U htrans hmin ((peakSlope p tau : ℝ) : ℂ)
    have hC := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
    have hchalf : c ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hC.1
    refine ⟨e, fun _ => c, fun _ => c, ?_, ?_, ?_, fun _ => ⟨hc, hc⟩⟩
    · intro i
      simpa only [one_mul] using
        signed_critical_gradient_apply p tau 1 hp hp2 htau (Or.inl rfl) U (e i)
          (by
            have hx := Module.End.mem_eigenspace_iff.mp (e i).property
            change G (e i : E) = (peakSlope p tau : ℂ) • (e i : E) at hx
            simpa only [G, one_mul] using hx)
    · intro i
      have hx := Module.End.mem_eigenspace_iff.mp (j (e i)).property
      change unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
        (j (e i) : E) = -(peakSlope p tau : ℂ) • (j (e i) : E) at hx
      have hneg := signed_critical_gradient_apply p tau (-1) hp hp2 htau (Or.inr rfl) U
        (j (e i)) (by simpa only [neg_one_mul, Complex.ofReal_neg] using hx)
      simpa only [neg_one_mul, hj] using hneg
    · intro i
      exact ⟨by linarith [hc.1], by linarith⟩

/-- The whole positive gradient space has an orthonormal phase basis,
paired by the actual source reflection. Zero positive rank is permitted. -/
theorem positive_gradient_phase_basis_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q} (U : E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
    ∃ n : ℕ, ∃ (e : OrthonormalBasis (Fin n) ℂ H) (g alpha beta : Fin n → ℝ),
      (∀ i, 0 < g i) ∧ (∀ i, G (e i : E) = (g i : ℂ) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (e i : E) = Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i)) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioc 0 (Real.pi / 2)) ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  classical
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let D (_ : ℝ) (x : E) : Prop := ∃ a b : ℝ,
    (U : E →L[ℂ] E) x = Complex.exp ((a : ℂ) * Complex.I) • x ∧
    (U : E →L[ℂ] E) (K.reflection x) =
      Complex.exp (((-b : ℝ) : ℂ) * Complex.I) • K.reflection x ∧
    (a + b) / 2 ∈ Ioc 0 (Real.pi / 2) ∧ a ∈ Ioo 0 Real.pi ∧ b ∈ Ioo 0 Real.pi
  have hG : G.toLinearMap.IsSymmetric := (isSelfAdjoint_unitaryPhaseGradient _ _).isSymmetric
  have hlevel (r : ℝ) (hr : 0 < r) (hs : Module.End.HasEigenvalue G.toLinearMap (r : ℂ)) :
      ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ
        (Module.End.eigenspace G.toLinearMap (r : ℂ)))) ℂ
          (Module.End.eigenspace G.toLinearMap (r : ℂ)), ∀ i, D r (b i : E) := by
    have hspec : (r : ℂ) ∈ spectrum ℂ G := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hs
    obtain ⟨b, alpha, beta, hu, hw, hmean, hbounds⟩ :=
      gradient_eigenspace_phase_basis_of_isLocalMinOn_transports p tau hp hp2 htau
        K Q U htrans hmin r hr hspec
    exact ⟨b, fun i => ⟨alpha i, beta i, hu i, hw i, hmean i, hbounds i⟩⟩
  obtain ⟨n, e, g, hg, hGe, hD⟩ := hG.exists_positive_spectral_basis_of_eigenspace_bases D hlevel
  choose alpha beta hu hw hmean hbounds using hD
  exact ⟨n, e, g, alpha, beta, hg, hGe, hu, hw, hmean, hbounds⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
