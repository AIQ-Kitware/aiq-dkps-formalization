/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction
public import ForTauCeti.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Feasible paired variations for an arbitrary unitary transport cost

A common Hermitian right exponential on two reflection-paired spaces
extends continuously to a feasible ambient transporter. A cost splitting
then transfers local minimality to the paired curve. The geometry allows
arbitrary complete complex Hilbert spaces and arbitrary real-valued costs.
-/

public section

noncomputable section

namespace TauCeti

open scoped Topology

variable {E R F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The block unitary with the same operator on each component commutes
with swapping the paired spaces. -/
theorem paired_block_commute_swap
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (A : V →L[𝕜] V) :
    Commute (A.withLpProdMap 2 A)
      (LinearIsometryEquiv.withLpProdComm 2 𝕜 V V : WithLp 2 (V × V) →L[𝕜] WithLp 2 (V × V)) := by
  ext x
  apply WithLp.ofLp_injective 2
  change (A.withLpProdMap 2 A (LinearIsometryEquiv.withLpProdComm 2 𝕜 V V x)).ofLp =
    (LinearIsometryEquiv.withLpProdComm 2 𝕜 V V (A.withLpProdMap 2 A x)).ofLp
  simp [ContinuousLinearMap.withLpProdMap_apply, LinearIsometryEquiv.withLpProdComm_apply]

/-- An additive cost splitting transfers an actual ambient local minimum
to the common Hermitian variation of a reflection-paired unitary block. -/
theorem isLocalMin_paired_variation_of_isLocalMinOn_transports_complex
    (cost : (F →L[ℂ] F) → ℝ) (curveCost : ℝ → ℝ) (k : ℝ)
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
    (hcost : ∀ t : ℝ, cost (e.conjStarAlgEquiv
      ((((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))).withLpProdMap 2
        ((V : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H)))).withLpProdMap 2
          (Z : R →L[ℂ] R))) = curveCost t + k)
    (hmin : IsLocalMinOn cost
      {T | T ∈ unitary (F →L[ℂ] F) ∧ T * P * star T = Q}
      (W : F →L[ℂ] F)) :
    IsLocalMin curveCost 0 := by
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
      ContinuousLinearMap.withLpProdMap_mem_unitary
        (ContinuousLinearMap.withLpProdMap_mem_unitary (hBunit t) (hBunit t)) (one_mem _)
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
    change D t * _ = _ * D t
    dsimp only [D]
    rw [ContinuousLinearMap.mul_withLpProdMap, ContinuousLinearMap.mul_withLpProdMap,
      hpair.eq, one_mul, mul_one]
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
  have hcostT (t : ℝ) : cost (T t) = curveCost t + k := hcost t
  rw [← hT0] at hmin
  have hcurve := hmin.comp_continuousOn (s := Set.univ)
    (fun t _ => hfeasible t) hTcont.continuousOn (Set.mem_univ 0)
  rw [isLocalMinOn_univ_iff] at hcurve
  change ∀ᶠ t in 𝓝 0, _ ≤ _ at hcurve ⊢
  filter_upwards [hcurve] with t ht
  simpa only [Function.comp_apply, hcostT, add_le_add_iff_right] using ht

end TauCeti
