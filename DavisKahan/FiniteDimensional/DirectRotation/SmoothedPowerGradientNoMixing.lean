/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerGradientBlocks
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerFeasibleBlocks
public import ForTauCeti.Analysis.InnerProductSpace.PairedInvolutionDecomposition

/-!
# No mixing on actual paired smoothed-power gradient eigenspaces

The paired reflection coordinates are constructed from constrained stationarity.
The proof adapts `SmoothedGradientNoMixing` to the common family, consuming
the shared classical restriction and feasible-variation infrastructure.
The two unitary restrictions are then placed in the same positive-gradient
space using the source reflection. At a local minimum their large-phase
projections are orthogonal.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
/-- On every positive submaximal gradient level of a local transport
minimum, the two opposite unitary restrictions have orthogonal large-phase
spaces after identification by the actual source reflection. -/
theorem gradient_block_no_overlap_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g)
    (hgm : g < peakSlope p tau) :
    let L := Module.End.eigenspace
      (unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ a ∈ Ioo 0 (criticalAngle p tau), ∃ b ∈ Ioo (criticalAngle p tau) Real.pi,
      smoothedPowerPhaseSlope p tau a = g ∧
      smoothedPowerPhaseSlope p tau b = g ∧
      ∃ (V W : L ≃ₗᵢ[ℂ] L) (A B : L →L[ℂ] L),
        IsStarProjection A ∧ IsStarProjection B ∧ A * B = 0 ∧
        (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (∀ x : L, K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x)) ∧
        (V : L →L[ℂ] L) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
          (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A ∧
        (W : L →L[ℂ] L) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
          (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
  let J := K.reflection
  have hJ : (J : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  have hpair : ∃ j : L ≃ₗᵢ[ℂ] Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ),
      ∀ x : L, (j x : E) = J x := by
    have hneg : ((-g : ℝ) : ℂ) = -(g : ℂ) := Complex.ofReal_neg g
    rw [hneg]
    exact gradient_eigenspace_pairing_of_isLocalMinOn_transports
      p tau hp htau K Q U htrans hmin (g : ℂ)
  obtain ⟨j, hj⟩ := hpair
  have hne : (g : ℂ) ≠ ((-g : ℝ) : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re] at hr
    linarith
  have horth (x y : L) : ⟪(x : E), J y⟫_ℂ = 0 := by
    have hsym : G.toLinearMap.IsSymmetric :=
      (isSelfAdjoint_unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)).isSymmetric
    have h := hsym.orthogonalFamily_eigenspaces hne x (j y)
    change ⟪(x : E), (j y : E)⟫_ℂ = 0 at h
    rw [hj] at h
    exact h
  obtain ⟨a, ha, b, hb, hag, hbg, ⟨V, A, hA, hV, hVrepr⟩,
      ⟨Wminus, Bminus, hBminus, hWminus, hWrepr⟩⟩ :=
    opposite_gradient_eigenspaces_two_phase_representation p tau g hp hp2 htau hg0 hgm U
  let W := j.trans (Wminus.trans j.symm)
  let B := j.symm.conjStarAlgEquiv Bminus
  have hB : IsStarProjection B := hBminus.map j.symm.conjStarAlgEquiv.toStarAlgHom
  have hWconj : (W : L →L[ℂ] L) = j.symm.conjStarAlgEquiv (Wminus : _ →L[ℂ] _) := by
    ext x
    rfl
  have hWrepr' : (W : L →L[ℂ] L) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B := by
    rw [hWconj, hWrepr, map_add, map_smul, map_one, map_smul]
  have hWact (x : L) : (U : E →L[ℂ] E) (J x) = J (W x) := by
    calc
      _ = (U : E →L[ℂ] E) (j x : E) := congrArg (U : E →L[ℂ] E) (hj x).symm
      _ = (Wminus (j x) : E) := (hWminus (j x)).symm
      _ = (j (W x) : E) := by simp [W]
      _ = J (W x) := hj (W x)
  let S := (pairedInvolutionEmbedding L J horth).toLinearMap.range
  let e := pairedInvolutionDecomposition L J horth
  obtain ⟨Z, hZ, hUcoords⟩ := pairedInvolutionDecomposition_operator L J horth
    (Unitary.linearIsometryEquiv U) V W (fun x => (hV x).symm) hWact
  obtain ⟨J₀, hJ₀, _, hJcoords⟩ :=
    pairedInvolutionDecomposition_involution L J horth K.reflection_involutive
  have hUblock : (U : E →L[ℂ] E) = e.conjStarAlgEquiv
      (((V : L →L[ℂ] L).withLpProdMap 2 (W : L →L[ℂ] L)).withLpProdMap 2
        (Z : Sᗮ →L[ℂ] Sᗮ)) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply]
    have hUfunc (z : E) : (Unitary.linearIsometryEquiv U) z = (U : E →L[ℂ] E) z := by
      simpa only [LinearIsometryEquiv.coe_coe''] using
        congrArg (fun T : E →L[ℂ] E => T z) (Unitary.coe_linearIsometryEquiv_apply U)
    simpa only [e, ContinuousLinearMap.withLpProdMap_apply,
      LinearIsometryEquiv.coe_coe'', hUfunc] using hUcoords y
  let P₀ : Sᗮ →L[ℂ] Sᗮ := (1 / 2 : ℂ) • (1 + (J₀ : Sᗮ →L[ℂ] Sᗮ))
  have hPexpr : K.starProjection = (1 / 2 : ℂ) • (1 + (J : E →L[ℂ] E)) := by
    rw [hJ, smul_add, smul_sub, smul_smul]
    norm_num
  have hPblock : K.starProjection = e.conjStarAlgEquiv
      (((1 / 2 : ℂ) •
        (1 + (LinearIsometryEquiv.withLpProdComm 2 ℂ L L :
          WithLp 2 (L × L) →L[ℂ] WithLp 2 (L × L)))).withLpProdMap 2 P₀) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hPexpr]
    change (1 / 2 : ℂ) • (e y + J (e y)) = _
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply,
      hJcoords y, ← map_add, ← map_smul]
    apply congrArg e
    apply WithLp.ofLp_injective 2
    simp [ContinuousLinearMap.withLpProdMap_apply, P₀,
      LinearIsometryEquiv.withLpProdComm_apply]
    apply Prod.ext <;> rfl
  have hc := criticalAngle_mem p tau hp hp2 htau
  have hap : a ∈ Icc 0 Real.pi := ⟨ha.1.le, by linarith [ha.2, hc.2, Real.pi_pos]⟩
  have hbp : b ∈ Icc 0 Real.pi := ⟨by linarith [hb.1, hc.1], hb.2.le⟩
  have hab : Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I) := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at hre
    exact (ne_of_lt (lt_trans ha.2 hb.1)) (Real.strictAntiOn_cos.injOn hap hbp hre)
  have hbalance := hag.trans hbg.symm
  have hnegative : Real.cos b < smoothedPowerCriticalCosine p tau := by
    have hC := smoothedPowerCriticalCosine_mem p tau hp hp2 htau
    have hcosc : Real.cos (criticalAngle p tau) = smoothedPowerCriticalCosine p tau :=
      Real.cos_arccos (by linarith [hC.1]) hC.2.le
    rw [← hcosc]
    exact Real.strictAntiOn_cos ⟨hc.1.le, hc.2.le⟩ hbp hb.1
  have hAB : A * B = 0 := overlap_eq_zero_of_isLocalMinOn_block_transports
    p tau a b hp hp2 htau hab hbalance hnegative
    (Unitary.linearIsometryEquiv.symm V) (Unitary.linearIsometryEquiv.symm W)
    A B hA hB hVrepr hWrepr' (Unitary.linearIsometryEquiv.symm Z)
    e K.starProjection Q P₀ U hPblock hUblock htrans hmin
  exact ⟨a, ha, b, hb, hag, hbg, V, W, A, B, hA, hB, hAB, hV,
    (fun x => (hWact x).symm), hVrepr, hWrepr'⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
