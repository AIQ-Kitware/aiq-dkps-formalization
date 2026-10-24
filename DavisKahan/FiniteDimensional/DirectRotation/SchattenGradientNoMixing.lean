/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientBlocks
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientPairing
import DavisKahan.FiniteDimensional.DirectRotation.SchattenFeasibleBlocks
import ForTauCeti.Analysis.InnerProductSpace.PairedInvolutionDecomposition

/-!
# No mixing on actual paired Schatten-gradient eigenspaces

The paired reflection coordinates are constructed from constrained stationarity.
The two unitary restrictions are then placed in the same positive-gradient
space using the source reflection. At a local minimum their large-phase
projections are orthogonal.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
/-- On every positive submaximal gradient level of a local transport
minimum, the two opposite unitary restrictions have orthogonal large-phase
spaces after identification by the actual source reflection. -/
theorem gradient_block_no_overlap_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E))
    (g : ℝ) (hg0 : 0 < g)
    (hgm : g < p.toReal * phaseAmplitude p.toReal (criticalAngle p.toReal)) :
    let L := Module.End.eigenspace
      (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap (g : ℂ)
    ∃ a ∈ Ioo 0 (criticalAngle p.toReal), ∃ b ∈ Ioo (criticalAngle p.toReal) Real.pi,
      phaseAmplitude p.toReal a = phaseAmplitude p.toReal b ∧
      ∃ (V W : L ≃ₗᵢ[ℂ] L) (A B : L →L[ℂ] L),
        IsStarProjection A ∧ IsStarProjection B ∧ A * B = 0 ∧
        (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
        (∀ x : L, K.reflection (W x) = (U : E →L[ℂ] E) (K.reflection x)) ∧
        (V : L →L[ℂ] L) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
          (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A ∧
        (W : L →L[ℂ] L) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
          (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let L := Module.End.eigenspace G.toLinearMap (g : ℂ)
  let J := K.reflection
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    p hp hp1 K.starProjection Q hP U htrans hmin
  have hJ : (J : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hJ] at hconj
  have hanti (x : E) : G (J x) = -J (G x) := by
    have h := congrArg (fun A : E →L[ℂ] E => A (J x)) hconj
    change J (G (J (J x))) = -G (J x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  let j : L ≃ₗᵢ[ℂ] Module.End.eigenspace G.toLinearMap ((-g : ℝ) : ℂ) :=
    (eigenspaceNegEquivOfInvolution J K.reflection_involutive G.toLinearMap hanti (g : ℂ)).trans
      (LinearIsometryEquiv.ofEq _ _ (by rw [Complex.ofReal_neg]))
  have hj (x : L) : (j x : E) = J x := by rfl
  have hne : (g : ℂ) ≠ ((-g : ℝ) : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re] at hr
    linarith
  have horth (x y : L) : ⟪(x : E), J y⟫_ℂ = 0 := by
    have hsym : G.toLinearMap.IsSymmetric :=
      (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).isSymmetric
    have h := hsym.orthogonalFamily_eigenspaces hne x (j y)
    change ⟪(x : E), (j y : E)⟫_ℂ = 0 at h
    rw [hj] at h
    exact h
  obtain ⟨a, ha, b, hb, hbalance, ⟨V, A, hA, hV, hVrepr⟩,
      ⟨Wminus, Bminus, hBminus, hWminus, hWrepr⟩⟩ :=
    opposite_gradient_eigenspaces_two_phase_representation p.toReal g hp1 hp2 hg0 hgm U
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
    exact hUcoords y
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
    rfl
  have hAB : A * B = 0 := overlap_eq_zero_of_isLocalMinOn_block_transports
    p hp hp1 hp2 a b ha hb hbalance
    (Unitary.linearIsometryEquiv.symm V) (Unitary.linearIsometryEquiv.symm W)
    A B hA hB hVrepr hWrepr' (Unitary.linearIsometryEquiv.symm Z)
    e K.starProjection Q P₀ U hPblock hUblock htrans hmin
  exact ⟨a, ha, b, hb, hbalance, V, W, A, B, hA, hB, hAB, hV,
    (fun x => (hWact x).symm), hVrepr, hWrepr'⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
