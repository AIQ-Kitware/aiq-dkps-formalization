/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerPositiveBasis
public import ForTauCeti.Analysis.InnerProductSpace.PairedSpectralDecomposition

/-!
# A common ambient spectral decomposition for smoothed-power transport

Every local minimum on the full finite complex transport fiber is an actual
orthogonal sum of reflection-paired phase planes and a self-adjoint unitary
on the gradient kernel. The literal spectral trace splits into their costs.
No independent-plane assumption is imposed on the original transporter.

This is the ambient structural step in C1 for the entire positively smoothed
family. It does not yet identify the global minimum value: phase/kernel costs must still be compared with
the principal-angle scalar minima. The phase means lie in `(0,pi/2]`.
The proof adapts the classical spectral/reflection assembly used in
`SmoothedSpectralDecomposition`, now with one family-wide no-overlap mechanism.
Historical priority of the constrained transport extension remains unresolved.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

private theorem symbol_exp_eq_phaseCost (p tau t : ℝ) :
    smoothedPowerDisplacementSymbol p tau (Complex.exp ((t : ℂ) * Complex.I)) =
      smoothedPowerPhaseCost p tau t := by
  rw [smoothedPowerDisplacementSymbol, smoothedPowerPhaseCost,
    Complex.norm_sub_one_sq_eq_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I t),
    Complex.exp_ofReal_mul_I_re]
  rw [show tau ^ 2 + 2 * (1 - Real.cos t) = tau ^ 2 + 2 - 2 * Real.cos t by ring]

set_option maxHeartbeats 800000 in
/-- **The family-wide ambient structural decomposition.** Every actual
local constrained minimum has reflection-paired phase coordinates and a
self-adjoint kernel restriction, with exact spectral cost additivity.
Scalar optimality of the resulting phase pairs is not assumed or asserted. -/
theorem spectral_decomposition_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
    let Z := G.toLinearMap.ker
    ∃ n : ℕ, ∃ (e : OrthonormalBasis (Fin n) ℂ H) (alpha beta : Fin n → ℝ)
      (V W : H ≃ₗᵢ[ℂ] H) (R : Z ≃ₗᵢ[ℂ] Z)
      (d : WithLp 2 (WithLp 2 (H × H) × Z) ≃ₗᵢ[ℂ] E),
      (∀ x : H, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (∀ x : H, K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x)) ∧
      (∀ z : Z, (R z : E) = (U : E →L[ℂ] E) z) ∧
      IsSelfAdjoint (R : Z →L[ℂ] Z) ∧
      (∀ x, d x = (x.fst.fst : E) + K.reflection x.fst.snd + (x.snd : E)) ∧
      (U : E →L[ℂ] E) = d.conjStarAlgEquiv
        (((V : H →L[ℂ] H).withLpProdMap 2 (W : H →L[ℂ] H)).withLpProdMap 2
          (R : Z →L[ℂ] Z)) ∧
      (∀ i, V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i) ∧
      (∀ i, W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioc 0 (Real.pi / 2)) ∧
      displacementCost p tau (U : E →L[ℂ] E) =
        (∑ i, (smoothedPowerPhaseCost p tau (alpha i) + smoothedPowerPhaseCost p tau (beta i))) +
          displacementCost p tau (R : Z →L[ℂ] Z) ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  classical
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  let J := K.reflection
  have hG : G.toLinearMap.IsSymmetric :=
    (isSelfAdjoint_unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)).isSymmetric
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    p tau hp htau K.starProjection Q hP U htrans hmin
  have hJ : (J : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hJ] at hconj
  have hanti (x : E) : G.toLinearMap (J x) = -J (G.toLinearMap x) := by
    have h := congrArg (fun T : E →L[ℂ] E => T (J x)) hconj
    change J (G (J (J x))) = -G (J x) at h
    rw [K.reflection_reflection] at h
    change G (J x) = -J (G x)
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  obtain ⟨n, e, g, alpha, beta, _, _, hu, hw, hmean, hbounds⟩ :=
    positive_gradient_phase_basis_of_isLocalMinOn_transports p tau hp hp2 htau K Q U htrans hmin
  have hUH : ∀ x ∈ H, (U : E →L[ℂ] E) x ∈ H :=
    e.mapsTo_submodule_of_eigenvectors (U : E →L[ℂ] E).toLinearMap
      (fun i => Complex.exp ((alpha i : ℂ) * Complex.I)) hu
  let U' := J.trans ((Unitary.linearIsometryEquiv U).trans J)
  have hu' (i) : U' (e i : E) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • (e i : E) := by
    change J ((U : E →L[ℂ] E) (J (e i))) = _
    rw [hw, map_smul, K.reflection_reflection]
  have hU'H : ∀ x ∈ H, U' x ∈ H :=
    e.mapsTo_submodule_of_eigenvectors U'.toLinearMap
      (fun i => Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)) hu'
  let v : H →ₗᵢ[ℂ] H :=
    { (U : E →L[ℂ] E).toLinearMap.restrict hUH with
      norm_map' := fun x => ContinuousLinearMap.norm_map_of_mem_unitary U.2 x }
  let w : H →ₗᵢ[ℂ] H :=
    { U'.toLinearMap.restrict hU'H with norm_map' := fun x => U'.norm_map x }
  let V := v.toLinearIsometryEquiv rfl
  let W := w.toLinearIsometryEquiv rfl
  have hV (x : H) : (V x : E) = (U : E →L[ℂ] E) x := rfl
  have hW (x : H) : J (W x) = (U : E →L[ℂ] E) (J x) := by
    change J (J ((U : E →L[ℂ] E) (J x))) = _
    exact K.reflection_reflection _
  obtain ⟨R, hR, hRself⟩ := gradient_kernel_isSelfAdjoint_restriction p tau hp htau U
  let horth := positive_spectralSpace_orthogonal_involution G.toLinearMap hG J
    K.reflection_involutive hanti
  let S := (pairedInvolutionEmbedding H J horth).toLinearMap.range
  have hker : Sᗮ = Z := paired_positive_spectral_orthogonal_eq_ker G.toLinearMap hG J
    K.reflection_involutive hanti
  let riso : Sᗮ ≃ₗᵢ[ℂ] Z := LinearIsometryEquiv.ofEq _ _ hker
  let d₀ := pairedInvolutionDecomposition H J horth
  let d := (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℂ _) riso.symm).trans d₀
  have hd (x : WithLp 2 (WithLp 2 (H × H) × Z)) :
      d x = (x.fst.fst : E) + J x.fst.snd + (x.snd : E) := by
    change d₀ (WithLp.toLp 2 (x.fst, riso.symm x.snd)) = _
    rw [pairedInvolutionDecomposition_apply]
    congr 1
  have hUblock : (U : E →L[ℂ] E) = d.conjStarAlgEquiv
      (((V : H →L[ℂ] H).withLpProdMap 2 (W : H →L[ℂ] H)).withLpProdMap 2
        (R : Z →L[ℂ] Z)) := by
    ext x
    obtain ⟨y, rfl⟩ := d.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, d.symm_apply_apply, hd, hd]
    simp only [ContinuousLinearMap.withLpProdMap_apply, LinearIsometryEquiv.coe_coe'']
    change (U : E →L[ℂ] E) ((y.fst.fst : E) + J y.fst.snd + (y.snd : E)) =
      (V y.fst.fst : E) + J (W y.fst.snd) + (R y.snd : E)
    rw [map_add, map_add, hV, hW, hR]
  have hVe (i) : V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i := by
    apply Subtype.ext
    exact (hV (e i)).trans (hu i)
  have hWe (i) : W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i := by
    apply Subtype.ext
    exact hu' i
  let : IsStarNormal (V : H →L[ℂ] H) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm V).property
  let : IsStarNormal (W : H →L[ℂ] H) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm W).property
  have hcostV : displacementCost p tau (V : H →L[ℂ] H) =
      ∑ i, smoothedPowerDisplacementSymbol p tau (Complex.exp ((alpha i : ℂ) * Complex.I)) :=
    ContinuousLinearMap.re_trace_cfc_eq_sum (smoothedPowerDisplacementSymbol p tau)
      (V : H →L[ℂ] H) e _ hVe
  have hcostW : displacementCost p tau (W : H →L[ℂ] H) =
      ∑ i, smoothedPowerDisplacementSymbol p tau (Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)) :=
    ContinuousLinearMap.re_trace_cfc_eq_sum (smoothedPowerDisplacementSymbol p tau)
      (W : H →L[ℂ] H) e _ hWe
  have hcost : displacementCost p tau (V : H →L[ℂ] H) +
      displacementCost p tau (W : H →L[ℂ] H) =
        ∑ i, (smoothedPowerPhaseCost p tau (alpha i) + smoothedPowerPhaseCost p tau (beta i)) := by
    rw [hcostV, hcostW, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [symbol_exp_eq_phaseCost, symbol_exp_eq_phaseCost]
    simp only [smoothedPowerPhaseCost, Real.cos_neg]
  refine ⟨n, e, alpha, beta, V, W, R, d, hV, hW, hR, hRself, hd,
    hUblock, hVe, hWe, hmean, ?_, hbounds⟩
  let v := Unitary.linearIsometryEquiv.symm V
  let w := Unitary.linearIsometryEquiv.symm W
  let r := Unitary.linearIsometryEquiv.symm R
  let vw : unitary (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :=
    ⟨(V : H →L[ℂ] H).withLpProdMap 2 (W : H →L[ℂ] H),
      ContinuousLinearMap.withLpProdMap_mem_unitary v.2 w.2⟩
  let vwr : unitary (WithLp 2 (WithLp 2 (H × H) × Z) →L[ℂ]
      WithLp 2 (WithLp 2 (H × H) × Z)) :=
    ⟨(vw : _ →L[ℂ] _).withLpProdMap 2 (R : Z →L[ℂ] Z),
      ContinuousLinearMap.withLpProdMap_mem_unitary vw.2 r.2⟩
  let rho := fun s : ℝ => (tau ^ 2 + s ^ 2) ^ (p / 2) - tau ^ p
  have hblockcost : displacementCost p tau (U : E →L[ℂ] E) =
      displacementCost p tau (V : H →L[ℂ] H) + displacementCost p tau (W : H →L[ℂ] H) +
        displacementCost p tau (R : Z →L[ℂ] Z) := by
    change normalDisplacementSpectralCost rho (U : E →L[ℂ] E) =
      normalDisplacementSpectralCost rho (v : H →L[ℂ] H) +
        normalDisplacementSpectralCost rho (w : H →L[ℂ] H) +
          normalDisplacementSpectralCost rho (r : Z →L[ℂ] Z)
    have hc := normalDisplacementSpectralCost_conj rho d vwr
    have hp := normalDisplacementSpectralCost_withLpProdMap rho vw r
    have hvw := normalDisplacementSpectralCost_withLpProdMap rho v w
    dsimp only [vwr, vw, v, w, r] at hc hp hvw
    simp only [Unitary.coe_symm_linearIsometryEquiv_apply] at hc hp hvw
    calc
      _ = normalDisplacementSpectralCost rho (d.conjStarAlgEquiv
          (((V : H →L[ℂ] H).withLpProdMap 2 (W : H →L[ℂ] H)).withLpProdMap 2
            (R : Z →L[ℂ] Z))) := congrArg (normalDisplacementSpectralCost rho) hUblock
      _ = _ := by
        rw [hc, hp, hvw]
        simp only [v, w, r, Unitary.coe_symm_linearIsometryEquiv_apply]
  rw [hblockcost, hcost]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
