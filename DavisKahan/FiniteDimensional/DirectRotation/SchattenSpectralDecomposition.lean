/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPositiveBasis
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientKernel
import ForTauCeti.Analysis.InnerProductSpace.PairedSpectralDecomposition

/-!
# Orthogonal spectral decomposition of a local Schatten transport minimum

Pair the complete positive-gradient phase basis by the source reflection.
The orthogonal remainder is exactly the gradient kernel. The transporter
is the orthogonal sum of its two phase restrictions and a self-adjoint
kernel restriction, and its literal Schatten power is the sum of the
attained scalar plane costs and the kernel cost.

The coordinate equivalence acts by `x + J y + z`. Consequently it retains
the original source reflection, rather than only the spectrum of the
transporter. This is the decomposition needed to identify the principal
angles of the original subspace pair. Empty positive or kernel spaces are
included. The global principal-angle lower bound is downstream of this
decomposition and the separate kernel inequality.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 800000 in
/-- A local constrained minimum is an actual orthogonal sum of paired
scalar optimizers and a self-adjoint gradient-kernel restriction. The
ambient Schatten power splits exactly into their costs. -/
theorem schatten_transport_spectral_decomposition_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
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
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ^ p.toReal =
        (∑ i, phaseMinimum p.toReal ((alpha i + beta i) / 2)) +
          UnitarilyInvariantSeminorm.schatten ℂ Z Z p
            (LinearMap.id - R.toLinearMap) ^ p.toReal ∧
      (∀ i, alpha i ∈ Ioo 0 Real.pi ∧ beta i ∈ Ioo 0 Real.pi) := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  let J := K.reflection
  have hG : G.toLinearMap.IsSymmetric :=
    (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).isSymmetric
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    p hp hp1 K.starProjection Q hP U htrans hmin
  have hJ : (J : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hJ] at hconj
  have hanti (x : E) : G.toLinearMap (J x) = -J (G.toLinearMap x) := by
    have h := congrArg (fun T : E →L[ℂ] E => T (J x)) hconj
    change J (G (J (J x))) = -G (J x) at h
    rw [K.reflection_reflection] at h
    change G (J x) = -J (G x)
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  obtain ⟨n, e, g, alpha, beta, _, _, hu, hw, hmean, hscalar, hbounds⟩ :=
    positive_gradient_phase_basis_of_isLocalMinOn_transports_complex p hp hp1 hp2 K Q U htrans hmin
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
  obtain ⟨R, hR, hRself, _, _⟩ := gradient_kernel_principalAngle_lower_bound p hp
    K (K.map (Unitary.linearIsometryEquiv U).toLinearMap) U rfl
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
    change (U : E →L[ℂ] E) ((y.fst.fst : E) + J y.fst.snd + (y.snd : E)) =
      (V y.fst.fst : E) + J (W y.fst.snd) + (R y.snd : E)
    rw [map_add, map_add, hV, hW, hR]
  have hVe (i) : V (e i) = Complex.exp ((alpha i : ℂ) * Complex.I) • e i := by
    apply Subtype.ext
    exact (hV (e i)).trans (hu i)
  have hWe (i) : W (e i) = Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • e i := by
    apply Subtype.ext
    exact hu' i
  have hcost : UnitarilyInvariantSeminorm.schatten ℂ H H p
      (LinearMap.id - V.toLinearMap) ^ p.toReal +
      UnitarilyInvariantSeminorm.schatten ℂ H H p
        (LinearMap.id - W.toLinearMap) ^ p.toReal =
        ∑ i, phaseMinimum p.toReal ((alpha i + beta i) / 2) := by
    have hVdisp (i : Fin n) : ((LinearMap.id : H →ₗ[ℂ] H) - V.toLinearMap) (e i) =
        (1 - Complex.exp ((alpha i : ℂ) * Complex.I)) • e i := by
      change e i - V (e i) = _
      rw [hVe, sub_smul, one_smul]
    have hWdisp (i : Fin n) : ((LinearMap.id : H →ₗ[ℂ] H) - W.toLinearMap) (e i) =
        (1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)) • e i := by
      change e i - W (e i) = _
      rw [hWe, sub_smul, one_smul]
    rw [schatten_rpow_eq_sum_norm_eigenvalues e _ _ hVdisp p hp,
      schatten_rpow_eq_sum_norm_eigenvalues e _ _ hWdisp p hp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hscalar i)
  refine ⟨n, e, alpha, beta, V, W, R, d, hV, hW, hR, hRself, hd,
    hUblock, hVe, hWe, hmean, ?_, hbounds⟩
  calc
    _ = UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - (d.conjStarAlgEquiv
          (((V : H →L[ℂ] H).withLpProdMap 2 (W : H →L[ℂ] H)).withLpProdMap 2
            (R : Z →L[ℂ] Z))).toLinearMap) ^ p.toReal :=
      congrArg (fun A : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - A.toLinearMap) ^ p.toReal) hUblock
    _ = _ := by
      rw [schatten_displacement_conj_linearIsometryEquiv d _ p hp,
        schatten_displacement_rpow_withLpProdMap _ _ p hp,
        schatten_displacement_rpow_withLpProdMap _ _ p hp]
      exact congrArg (fun t : ℝ => t + UnitarilyInvariantSeminorm.schatten ℂ Z Z p
        (LinearMap.id - R.toLinearMap) ^ p.toReal) hcost

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
