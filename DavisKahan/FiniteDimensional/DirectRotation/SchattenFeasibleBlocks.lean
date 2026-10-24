/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenNoMixing
import ForTauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Feasible variations of paired gradient blocks

A common right unitary on two paired spaces commutes with their swapping
reflection. Its orthogonal extension therefore preserves the source projection,
and a local minimum of the ambient transport cost induces a local minimum
of the actual paired cost.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal Topology

variable {E R F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] [CompleteSpace R]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ R] in
private theorem unitary_withLpProdMap
    {A : E →L[ℂ] E} {B : R →L[ℂ] R}
    (hA : A ∈ unitary (E →L[ℂ] E)) (hB : B ∈ unitary (R →L[ℂ] R)) :
    A.withLpProdMap 2 B ∈ unitary (WithLp 2 (E × R) →L[ℂ] WithLp 2 (E × R)) := by
  let e := LinearIsometryEquiv.withLpProdCongr 2
    (Unitary.linearIsometryEquiv ⟨A, hA⟩) (Unitary.linearIsometryEquiv ⟨B, hB⟩)
  have h := (Unitary.linearIsometryEquiv.symm e).property
  convert h using 1
  ext x
  simp [ContinuousLinearMap.withLpProdMap_apply, e]
  exact ⟨rfl, rfl⟩

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- The block unitary with the same operator on each component commutes
with swapping the paired spaces. -/
theorem paired_block_commute_swap (A : E →L[ℂ] E) :
    Commute (A.withLpProdMap 2 A)
      (LinearIsometryEquiv.withLpProdComm 2 ℂ E E : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) := by
  ext x
  apply WithLp.ofLp_injective 2
  rfl

/-- A local minimum of an ambient transport cost induces a local minimum
on every paired reflection block, with the remaining unitary block fixed.
The coordinate equivalence may change the ambient carrier type. -/
theorem isLocalMin_paired_cost_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (U V : unitary (E →L[ℂ] E)) (Z : unitary (R →L[ℂ] R))
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (e : WithLp 2 (WithLp 2 (E × E) × R) ≃ₗᵢ[ℂ] F)
    (P Q : F →L[ℂ] F) (P₀ : R →L[ℂ] R) (W : unitary (F →L[ℂ] F))
    (hP : P = e.conjStarAlgEquiv
      (((1 / 2 : ℂ) •
        (1 + (LinearIsometryEquiv.withLpProdComm 2 ℂ E E :
          WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)))).withLpProdMap 2 P₀))
    (hW : (W : F →L[ℂ] F) = e.conjStarAlgEquiv
      (((U : E →L[ℂ] E).withLpProdMap 2 (V : E →L[ℂ] E)).withLpProdMap 2
        (Z : R →L[ℂ] R)))
    (htrans : (W : F →L[ℂ] F) * P * star (W : F →L[ℂ] F) = Q)
    (hmin : IsLocalMinOn
      (fun T : F →L[ℂ] F => UnitarilyInvariantSeminorm.schatten ℂ F F p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) :
    IsLocalMin (pairedSchattenCost p U V H) 0 := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  let B : ℝ → E →L[ℂ] E := fun t => NormedSpace.exp (t • (Complex.I • H))
  let D := fun t => ((B t).withLpProdMap 2 (B t)).withLpProdMap 2 (1 : R →L[ℂ] R)
  let C := fun t => e.conjStarAlgEquiv (D t)
  let T := fun t => e.conjStarAlgEquiv
    ((((U : E →L[ℂ] E) * B t).withLpProdMap 2 ((V : E →L[ℂ] E) * B t)).withLpProdMap 2
      (Z : R →L[ℂ] R))
  have hBunit (t : ℝ) : B t ∈ unitary (E →L[ℂ] E) := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [star_smul, hH.star_eq]
  have hCunit (t : ℝ) : C t ∈ unitary (F →L[ℂ] F) := by
    have hD : D t ∈ unitary (WithLp 2 (WithLp 2 (E × E) × R) →L[ℂ]
        WithLp 2 (WithLp 2 (E × E) × R)) :=
      unitary_withLpProdMap (unitary_withLpProdMap (hBunit t) (hBunit t)) (one_mem _)
    let d := Unitary.linearIsometryEquiv ⟨D t, hD⟩
    let c := e.symm.trans (d.trans e)
    have hc := (Unitary.linearIsometryEquiv.symm c).property
    convert hc using 1
    ext x
    change e (D t (e.symm x)) = e (d (e.symm x))
    rfl
  have hCP (t : ℝ) : Commute (C t) P := by
    rw [hP]
    apply Commute.map
    have hpair := ((Commute.one_right ((B t).withLpProdMap 2 (B t))).add_right
      (paired_block_commute_swap (B t))).smul_right (1 / 2 : ℂ)
    ext x
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact DFunLike.congr_fun hpair.eq x.fst
    · simp [D]
  have hT (t : ℝ) : T t = (W : F →L[ℂ] F) * C t := by
    rw [hW]
    change e.conjStarAlgEquiv _ = e.conjStarAlgEquiv _ * e.conjStarAlgEquiv _
    rw [← map_mul]
    apply congrArg e.conjStarAlgEquiv
    ext x
    simp [D, ContinuousLinearMap.withLpProdMap_apply]
  have hT0 : T 0 = (W : F →L[ℂ] F) := by
    simpa only [T, B, zero_smul, NormedSpace.exp_zero, mul_one] using hW.symm
  have hfeasible (t : ℝ) : T t ∈
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q} := by
    rw [hT t]
    refine ⟨mul_mem W.2 (hCunit t), ?_⟩
    rw [star_mul]
    calc
      _ = (W : F →L[ℂ] F) * (C t * P) * star (C t) * star (W : F →L[ℂ] F) := by
        simp only [mul_assoc]
      _ = (W : F →L[ℂ] F) * (P * C t) * star (C t) * star (W : F →L[ℂ] F) := by
        rw [(hCP t).eq]
      _ = (W : F →L[ℂ] F) * P * (C t * star (C t)) * star (W : F →L[ℂ] F) := by
        simp only [mul_assoc]
      _ = Q := by rw [(Unitary.mem_iff.mp (hCunit t)).2, mul_one, htrans]
  have hBcont : Continuous B := by dsimp [B]; fun_prop
  have hTcont : Continuous T := by
    have hUcont : Continuous (fun t => (U : E →L[ℂ] E) * B t) :=
      continuous_const.mul hBcont
    have hVcont : Continuous (fun t => (V : E →L[ℂ] E) * B t) :=
      continuous_const.mul hBcont
    have hpair : Continuous (fun t => ((U : E →L[ℂ] E) * B t).withLpProdMap 2
        ((V : E →L[ℂ] E) * B t)) := hUcont.withLpProdMap hVcont
    have hblocks : Continuous (fun t =>
        (((U : E →L[ℂ] E) * B t).withLpProdMap 2 ((V : E →L[ℂ] E) * B t)).withLpProdMap 2
          (Z : R →L[ℂ] R)) := hpair.withLpProdMap continuous_const
    change Continuous (fun t => (e : _ →L[ℂ] F) ∘L
      ((((U : E →L[ℂ] E) * B t).withLpProdMap 2 ((V : E →L[ℂ] E) * B t)).withLpProdMap 2
        (Z : R →L[ℂ] R)) ∘L (e.symm : F →L[ℂ] _))
    exact (hblocks.clm_comp_const (e.symm : F →L[ℂ] _)).const_clm_comp (e : _ →L[ℂ] F)
  have hcost (t : ℝ) : UnitarilyInvariantSeminorm.schatten ℂ F F p
      (LinearMap.id - (T t).toLinearMap) ^ p.toReal =
      pairedSchattenCost p U V H t + UnitarilyInvariantSeminorm.schatten ℂ R R p
        (LinearMap.id - (Z : R →L[ℂ] R).toLinearMap) ^ p.toReal := by
    dsimp only [T]
    rw [schatten_displacement_conj_linearIsometryEquiv e _ p hp,
      schatten_displacement_rpow_withLpProdMap _ _ p hp,
      ← pairedSchattenCost_eq_block_displacement p hp U V H t]
  rw [← hT0] at hmin
  have hcurve := hmin.comp_continuousOn (s := Set.univ)
    (fun t _ => hfeasible t) hTcont.continuousOn (Set.mem_univ 0)
  rw [isLocalMinOn_univ_iff] at hcurve
  change ∀ᶠ t in 𝓝 0, _ ≤ _ at hcurve ⊢
  filter_upwards [hcurve] with t ht
  simpa only [Function.comp_apply, hcost, add_le_add_iff_right] using ht

/-- At an ambient transport minimum, the large-phase subspaces on a
paired reflection block are orthogonal. The complementary block is arbitrary. -/
theorem overlap_eq_zero_of_isLocalMinOn_block_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (a b : ℝ) (ha : a ∈ Set.Ioo 0 (criticalAngle p.toReal))
    (hb : b ∈ Set.Ioo (criticalAngle p.toReal) Real.pi)
    (hbalance : phaseAmplitude p.toReal a = phaseAmplitude p.toReal b)
    (U V : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E)
    (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hU : (U : E →L[ℂ] E) = Complex.exp ((a : ℂ) * Complex.I) • 1 +
      (Complex.exp ((b : ℂ) * Complex.I) - Complex.exp ((a : ℂ) * Complex.I)) • A)
    (hV : (V : E →L[ℂ] E) = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) • 1 +
      (Complex.exp (((-b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-a : ℝ) : ℂ) * Complex.I)) • B)
    (Z : unitary (R →L[ℂ] R))
    (e : WithLp 2 (WithLp 2 (E × E) × R) ≃ₗᵢ[ℂ] F)
    (P Q : F →L[ℂ] F) (P₀ : R →L[ℂ] R) (W : unitary (F →L[ℂ] F))
    (hP : P = e.conjStarAlgEquiv
      (((1 / 2 : ℂ) •
        (1 + (LinearIsometryEquiv.withLpProdComm 2 ℂ E E :
          WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)))).withLpProdMap 2 P₀))
    (hW : (W : F →L[ℂ] F) = e.conjStarAlgEquiv
      (((U : E →L[ℂ] E).withLpProdMap 2 (V : E →L[ℂ] E)).withLpProdMap 2
        (Z : R →L[ℂ] R)))
    (htrans : (W : F →L[ℂ] F) * P * star (W : F →L[ℂ] F) = Q)
    (hmin : IsLocalMinOn
      (fun T : F →L[ℂ] F => UnitarilyInvariantSeminorm.schatten ℂ F F p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) : A * B = 0 := by
  apply overlap_eq_zero_of_isLocalMin_paired_cost p hp hp1 hp2 a b ha hb hbalance
    U V A B hA hB hU hV
  exact isLocalMin_paired_cost_of_isLocalMinOn_transports p hp U V Z (A * B + B * A)
    (isSelfAdjoint_projection_overlap hA.isSelfAdjoint hB.isSelfAdjoint)
    e P Q P₀ W hP hW htrans hmin

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
