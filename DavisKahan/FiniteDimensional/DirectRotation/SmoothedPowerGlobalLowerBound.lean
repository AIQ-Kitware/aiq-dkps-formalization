/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerSpectralDecomposition
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerReflectionBound
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenTransportExistence
public import ForTauCeti.Analysis.InnerProductSpace.Projection.PairedPhaseTrace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport
public import ForTauCeti.Analysis.InnerProductSpace.InvariantKernel

/-!
# The unrestricted family principal-angle lower bound

The actual ambient local-minimum decomposition, the paired angle trace,
and the common reflection comparison imply a lower bound at every local
minimum. Classical compact attainment then transfers it to every competitor
on the full complex transport fiber. No principal-plane invariance is
assumed of that competitor. This is the lower-bound part of C1b.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The gradient square reduces both projections at an ambient local
minimum. This uses the common first variation, independently of C2. -/
theorem gradient_square_reduces_projections_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 < tau)
    (K : Submodule ℂ E) (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
    Commute K.starProjection (G * G) ∧ Commute Q (G * G) := by
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_transports
    p tau hp htau K.starProjection Q hP U htrans hmin
  have hJ : (K.reflection : E →L[ℂ] E) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hJ] at hconj
  have hsource : Commute K.starProjection (G * G) :=
    commute_square_of_reflection_conjugate_eq_neg G K hconj
  refine ⟨hsource, ?_⟩
  have hGU : Commute G (U : E →L[ℂ] E) := commute_unitaryPhaseGradient _ _
  have hG : IsSelfAdjoint G := isSelfAdjoint_unitaryPhaseGradient _ _
  have hGUstar : Commute G (star (U : E →L[ℂ] E)) := by
    simpa only [hG.star_eq] using hGU.star_star
  rw [← htrans]
  exact ((hGU.mul_left hGU).symm.mul_left hsource).mul_left
    (hGUstar.mul_left hGUstar).symm

set_option maxHeartbeats 800000 in
-- The complete ambient decomposition carries several dependent spectral spaces.
/-- Every local minimum dominates the principal-angle scalar minimum sum.
The positive phase pairs need not yet be classified as scalar optimizers. -/
theorem sum_phaseMinimum_le_of_isLocalMinOn_transports
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn (displacementCost p tau)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ≤
      displacementCost p tau (U : E →L[ℂ] E) := by
  classical
  let G := unitaryPhaseGradient (smoothedPowerDisplacementGradient p tau) (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  have ht := (K.map_eq_iff_conjugate_starProjection L (Unitary.linearIsometryEquiv U)).mp hmap
  obtain ⟨n, e, alpha, beta, V, W, R, d, hV, hW, hR, hself, hd, _, hVe, hWe,
      hmean, hcost, hbounds⟩ := spectral_decomposition_of_isLocalMinOn_transports
        p tau hp hp2 htau K L.starProjection U ht hmin
  have hG : IsSelfAdjoint G := isSelfAdjoint_unitaryPhaseGradient _ _
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    p tau hp htau K L.starProjection U ht hmin
  have hK : ∀ x ∈ Z, K.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPK.eq)
  have hL : ∀ x ∈ Z, L.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute L.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPL.eq)
  have hu (i) : (Unitary.linearIsometryEquiv U) (e i : E) =
      Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E) := by
    change (U : E →L[ℂ] E) (e i : E) = _
    rw [← hV, hVe]
    rfl
  have hw (i) : (Unitary.linearIsometryEquiv U) (K.reflection (e i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
    change (U : E →L[ℂ] E) (K.reflection (e i)) = _
    rw [← hW, hWe, Submodule.coe_smul, map_smul]
  have hangles := Submodule.sum_principalAngles_eq_paired_phases_add_comap_complex
    K L H Z (Unitary.linearIsometryEquiv U) hmap e alpha beta hu hw
    (fun i => ⟨(hmean i).1.le, (hmean i).2⟩) d hd hK hL
    (phaseMinimum p tau) (phaseMinimum_zero p tau htau.le)
  have hmapR := K.map_comap_subtype_of_isometry_restriction L Z
    (Unitary.linearIsometryEquiv U) R hmap hR
  have hkernel := sum_phaseMinimum_le_selfAdjoint_transport p tau hp htau.le _ _ R hself hmapR
  have hpairs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    phaseMinimum_mean_le_sum p tau (alpha i) (beta i) (by linarith) htau.le
      (hbounds i).1.1.le (hbounds i).2.1.le
  rw [hangles, hcost]
  exact add_le_add hpairs hkernel

/-- The literal family cost is continuous on the unitary group. The
finite singular-value sum supplies continuity even at spectral collisions. -/
theorem continuousOn_displacementCost_unitary (p tau : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (displacementCost (E := E) p tau) (unitary (E →L[ℂ] E)) := by
  let f := fun W : E →L[ℂ] E =>
    ∑ i : Fin (Module.finrank ℂ E), penalty p tau ((1 - W).singularValue i : ℝ)
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro i _
    have hs : Continuous (fun W : E →L[ℂ] E => ((1 - W).singularValue i : ℝ)) :=
      (NNReal.continuous_coe.comp (ContinuousLinearMap.continuous_singularValue i)).comp
        (continuous_const.sub continuous_id)
    exact (((continuous_const.add (hs.pow 2)).rpow_const
      (fun _ => Or.inr (by linarith : 0 ≤ p / 2))).sub continuous_const)
  apply hf.continuousOn.congr
  intro W hW
  let := isStarNormal_of_mem_unitary hW
  symm
  change (∑ i : Fin (Module.finrank ℂ E), penalty p tau ((1 - W).singularValue i : ℝ)) =
    normalDisplacementSpectralCost (penalty p tau) W
  rw [normalDisplacementSpectralCost_eq_sum_singularValues]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
  rfl

/-- Classical compact attainment for the family cost on any nonempty
finite complex transport fiber, including arbitrary transported operators. -/
theorem exists_transport_minimizer (p tau : ℝ) (hp : 0 ≤ p)
    (P Q : E →L[ℂ] E) (U₀ : unitary (E →L[ℂ] E))
    (h₀ : (U₀ : E →L[ℂ] E) * P * star (U₀ : E →L[ℂ] E) = Q) :
    ∃ U : unitary (E →L[ℂ] E),
      (U : E →L[ℂ] E) * P * star (U : E →L[ℂ] E) = Q ∧
      IsMinOn (displacementCost p tau)
        {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = Q} (U : E →L[ℂ] E) := by
  obtain ⟨W, hW, hmin⟩ := (SchattenPhaseTransition.isCompact_unitary_transport_fiber P Q).exists_isMinOn
    ⟨(U₀ : E →L[ℂ] E), U₀.2, h₀⟩
    ((continuousOn_displacementCost_unitary p tau hp).mono fun _ h => h.1)
  exact ⟨⟨W, hW.1⟩, hW.2, hmin⟩

/-- **Unrestricted lower bound for the entire positively smoothed family.**
The competitor is any complex unitary transporter, without a plane hypothesis. -/
theorem sum_phaseMinimum_le_transport
    (p tau : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 < tau)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L) :
    (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ≤
      displacementCost p tau (U : E →L[ℂ] E) := by
  have ht := (K.map_eq_iff_conjugate_starProjection L (Unitary.linearIsometryEquiv U)).mp hmap
  obtain ⟨V, hV, hmin⟩ := exists_transport_minimizer p tau (by linarith)
    K.starProjection L.starProjection U ht
  have hmapV := (K.map_eq_iff_conjugate_starProjection L (Unitary.linearIsometryEquiv V)).mpr hV
  exact (sum_phaseMinimum_le_of_isLocalMinOn_transports p tau hp hp2 htau K L V hmapV
    hmin.isLocalMinOn).trans (hmin ⟨U.property, ht⟩)

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
