/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierFiniteRankVariation
public import ForTauCeti.Analysis.InnerProductSpace.CharbonnierGradientUniform
public import ForTauCeti.Analysis.InnerProductSpace.SchattenRankOneVariation
public import ForTauCeti.Analysis.OperatorIdeal.CharbonnierConvergence

/-!
# Native Hilbert-space Charbonnier rank-one first variations

Fixed finite-rank perturbations preserve a Hilbert--Schmidt singular-value
tail bound. This controls the infinite trace while finite unitary
truncations and their phase derivatives pass to the limit.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem phase_mem_unitary (x : E) (s : ℝ) :
    NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x)) ∈
      unitary (E →L[ℂ] E) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  have hH : IsSelfAdjoint (InnerProductSpace.rankOne ℂ x x) :=
    InnerProductSpace.adjoint_rankOne x x
  rw [skewAdjoint.mem_iff]
  simp [star_smul, hH.star_eq]

/-- A rank-one phase stays inside the finite Charbonnier cost domain,
which is precisely the native Hilbert--Schmidt restricted unitary group. -/
theorem charbonnier_unitary_rankOne_variation_ne_top
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E)
    (hU : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (x : E) (hx : ‖x‖ = 1) (s : ℝ) :
    (1 - (U : E →L[ℂ] E) *
      NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x))).charbonnierCost tau
        ≠ ∞ := by
  apply (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mpr
  exact schatten_unitary_rankOne_variation_ne_top 2 (by norm_num) U
    ((ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hU) x hx s

/-- **Native infinite-dimensional smoothed first variation.** Finite
Charbonnier cost and positive smoothing suffice at every real time,
including zero displacement and repeated spectrum. -/
theorem hasDerivAt_charbonnier_unitary_rankOne_variation
    (tau : ℝ) (hτ : 0 < tau) (U : E ≃ₗᵢ[ℂ] E)
    (hU : (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≠ ∞)
    (x : E) (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (1 - (U : E →L[ℂ] E) *
        NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x))).charbonnierCost tau
        |>.toReal)
      (inner ℂ x (smoothedUnitaryGradient tau
        ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • InnerProductSpace.rankOne ℂ x x))) x)).re t := by
  let H := InnerProductSpace.rankOne ℂ x x
  have hSp := (ContinuousLinearMap.charbonnierCost_ne_top_iff_schatten_two tau hτ _).mp hU
  have hUcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (1 - (U : E →L[ℂ] E)) hSp
  have hcompact : IsCompactOperator (((U : E →L[ℂ] E) - 1) : E →L[ℂ] E) := by
    rw [← neg_sub 1 (U : E →L[ℂ] E)]
    exact hUcompact.neg
  obtain ⟨Uₙ, N, hN, hlim, _, _, hdom, _⟩ :=
    exists_finite_unitary_approximation_sequence U hcompact
  let V (s : ℝ) : unitary (E →L[ℂ] E) :=
    ⟨NormedSpace.exp (s • (Complex.I • H)), phase_mem_unitary x s⟩
  have hV : Continuous V :=
    (differentiable_exp_smul_const ℝ (Complex.I • H)).continuous |>.subtype_mk _
  let u := Unitary.linearIsometryEquiv.symm U
  let uₙ (n : ℕ) := Unitary.linearIsometryEquiv.symm (Uₙ n)
  have hlu : Tendsto uₙ atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    simpa only [uₙ, u, Unitary.coe_symm_linearIsometryEquiv_apply] using hlim
  have hderivlim := tendstoUniformlyOn_smoothed_gradient_pairing_mul_curve tau hτ
    u uₙ hlu V hV x (t - 1) (t + 1)
  let A (s : ℝ) := 1 - (U : E →L[ℂ] E) * (V s : E →L[ℂ] E)
  let Aₙ (n : ℕ) (s : ℝ) := 1 - (Uₙ n : E →L[ℂ] E) * (V s : E →L[ℂ] E)
  have hCrank (s : ℝ) : (1 - (V s : E →L[ℂ] E)).rank ≤ 1 := by
    have hdisp : 1 - (V s : E →L[ℂ] E) =
        (1 - Complex.exp ((s : ℂ) * Complex.I)) • H := by
      change 1 - NormedSpace.exp (s • (Complex.I • H)) = _
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
        InnerProductSpace.exp_smul_rankOne_of_norm_eq_one x hx]
      module
    have hrange : (1 - (V s : E →L[ℂ] E)).range ≤ ℂ ∙ x := by
      rintro y ⟨z, rfl⟩
      rw [hdisp]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
    change Module.rank ℂ ((1 - (V s : E →L[ℂ] E)).range) ≤ 1
    have hNx : Module.rank ℂ (ℂ ∙ x) = 1 := by
      rw [← Module.finrank_eq_rank, finrank_span_singleton]
      · norm_num
      · intro hx0
        simp [hx0] at hx
    exact (Submodule.rank_mono hrange).trans_eq hNx
  have hpoint (s : ℝ) : Tendsto (fun n => ((Aₙ n s).charbonnierCost tau).toReal)
      atTop (𝓝 ((A s).charbonnierCost tau).toReal) := by
    have hAn : Tendsto (fun n => Aₙ n s) atTop (𝓝 (A s)) :=
      tendsto_const_nhds.sub (hlim.mul_const _)
    have htail (n k : ℕ) : (Aₙ n s).singularValue (k + 1) ≤
        (1 - (U : E →L[ℂ] E)).singularValue k := by
      have hfactor : Aₙ n s =
          (1 - (Uₙ n : E →L[ℂ] E)) * (V s : E →L[ℂ] E) +
            (1 - (V s : E →L[ℂ] E)) := by dsimp only [Aₙ]; noncomm_ring
      rw [hfactor]
      calc
        _ ≤ ((1 - (Uₙ n : E →L[ℂ] E)) * (V s : E →L[ℂ] E)).singularValue k +
            (1 - (V s : E →L[ℂ] E)).singularValue 1 :=
          ContinuousLinearMap.singularValue_add_index_le _ _ _ _
        _ = ((1 - (Uₙ n : E →L[ℂ] E)) * (V s : E →L[ℂ] E)).singularValue k := by
          rw [ContinuousLinearMap.singularValue_eq_zero_of_rank_le (hCrank s), add_zero]
        _ ≤ (1 - (Uₙ n : E →L[ℂ] E)).singularValue k * ‖(V s : E →L[ℂ] E)‖₊ :=
          ContinuousLinearMap.singularValue_comp_le_right _ _ k
        _ ≤ (1 - (Uₙ n : E →L[ℂ] E)).singularValue k * 1 := by
          gcongr
          exact_mod_cast
            (Unitary.linearIsometryEquiv (V s)).toLinearIsometry.norm_toContinuousLinearMap_le
        _ ≤ _ := by simpa only [mul_one] using hdom n k
    have hcost := ContinuousLinearMap.tendsto_charbonnierCost_of_singularValue_tail_le
      tau hτ (1 - (U : E →L[ℂ] E)) hSp (fun n => Aₙ n s) (A s) hAn 1 htail
    exact (ENNReal.tendsto_toReal
      (charbonnier_unitary_rankOne_variation_ne_top tau hτ U hU x hx s)).comp hcost
  apply hasDerivAt_of_tendstoUniformlyOn (s := Set.Ioo (t - 1) (t + 1)) isOpen_Ioo
    (hderivlim.mono Set.Ioo_subset_Icc_self)
    (Eventually.of_forall fun n s _ =>
      hasDerivAt_charbonnier_finite_rank_unitary_rankOne_variation tau hτ (Uₙ n) (N n) (hN n)
        x hx s)
    (fun s _ => hpoint s) (by constructor <;> linarith)

end TauCeti
