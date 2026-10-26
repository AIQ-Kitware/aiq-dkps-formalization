/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenFiniteRankVariation
public import ForTauCeti.Analysis.InnerProductSpace.SchattenGradientUniform
public import ForTauCeti.Analysis.InnerProductSpace.SchattenUnitaryApproximation
public import ForTauCeti.Analysis.OperatorIdeal.Family.GaugeContinuity
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Rank-one first variations in the Schatten restricted unitary group

Finite-rank unitary approximations converge in the native Schatten
gauge. Their rank-one phase derivatives converge locally uniformly by
continuous functional calculus on compact parameter sets. Passing
derivatives to the limit justifies constrained stationarity in arbitrary
Hilbert dimension, including at vanishing displacement singular values.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ENNReal Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem rankOne_phase_mem_unitary (x : E) (s : ℝ) :
    NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x)) ∈
      unitary (E →L[ℂ] E) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  have hH : IsSelfAdjoint (InnerProductSpace.rankOne ℂ x x) :=
    InnerProductSpace.adjoint_rankOne x x
  rw [skewAdjoint.mem_iff]
  simp [star_smul, hH.star_eq]

/-- A rank-one phase variation stays in the same Schatten restricted
unitary group. The statement is about the native ambient ideal cost. -/
theorem schatten_unitary_rankOne_variation_ne_top
    (p : ℝ) (hp : 1 ≤ p) (U : E ≃ₗᵢ[ℂ] E)
    (hU : (OperatorIdealFamily.schatten ℂ p hp).gauge (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (x : E) (hx : ‖x‖ = 1) (s : ℝ) :
    (OperatorIdealFamily.schatten ℂ p hp).gauge
      (1 - (U : E →L[ℂ] E) *
        NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x))) ≠ ∞ := by
  let Φ := OperatorIdealFamily.schatten ℂ p hp
  let H := InnerProductSpace.rankOne ℂ x x
  let N := ℂ ∙ x
  have hP : H = N.starProjection := by
    ext y
    exact (Submodule.starProjection_unit_singleton ℂ hx y).symm
  have hHrank : H.rank ≤ Module.finrank ℂ N := by
    rw [hP, LinearMap.rank, Submodule.range_starProjection, ← Module.finrank_eq_rank]
  have hHfinite : Φ.gauge H ≠ ∞ :=
    OperatorIdealFamily.gauge_schatten_ne_top_of_rank_le p hp H (Module.finrank ℂ N) hHrank
  let V := Unitary.linearIsometryEquiv
    (⟨NormedSpace.exp (s • (Complex.I • H)), rankOne_phase_mem_unitary x s⟩ :
      unitary (E →L[ℂ] E))
  have hVdisp : 1 - (V : E →L[ℂ] E) =
      (1 - Complex.exp ((s : ℂ) * Complex.I)) • H := by
    change 1 - NormedSpace.exp (s • (Complex.I • H)) = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
      InnerProductSpace.exp_smul_rankOne_of_norm_eq_one x hx]
    module
  have hVfinite : Φ.gauge (1 - (V : E →L[ℂ] E)) ≠ ∞ := by
    rw [hVdisp, Φ.gauge_smul]
    exact (ENNReal.mul_lt_top enorm_lt_top (lt_top_iff_ne_top.mpr hHfinite)).ne
  have hfactor : 1 - (U : E →L[ℂ] E) * (V : E →L[ℂ] E) =
      (1 - (U : E →L[ℂ] E)) ∘L (V : E →L[ℂ] E) + (1 - (V : E →L[ℂ] E)) := by
    ext y
    change y - U (V y) = (V y - U (V y)) + (y - V y)
    abel
  change Φ.gauge (1 - (U : E →L[ℂ] E) * (V : E →L[ℂ] E)) ≠ ∞
  rw [hfactor]
  apply ne_top_of_le_ne_top _ (Φ.gauge_add_le _ _)
  rw [Φ.gauge_comp_linearIsometryEquiv_right]
  exact ENNReal.add_ne_top.mpr ⟨hU, hVfinite⟩

/-- **Hilbert-space Schatten first variation in a rank-one direction.**
Finite cost and `p>1` suffice, without finite rank or separability.
The derivative holds at every real time, including spectral crossings
through identity. -/
theorem hasDerivAt_schatten_unitary_rankOne_variation
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (U : E ≃ₗᵢ[ℂ] E)
    (hU : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
      (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (x : E) (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - (U : E →L[ℂ] E) *
          NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x)))) ^
            p.toReal |>.toReal)
      (inner ℂ x (schattenUnitaryGradient p.toReal
        ((U : E →L[ℂ] E) *
          NormedSpace.exp (t • (Complex.I • InnerProductSpace.rankOne ℂ x x))) x)).re t := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  have hp0 : 0 < p.toReal := zero_lt_one.trans hp1
  have hU' : Φ.gauge ((U : E →L[ℂ] E) - 1) ≠ ∞ := by
    rw [← neg_sub 1 (U : E →L[ℂ] E), Φ.gauge_neg]
    exact hU
  obtain ⟨Uₙ, N, hN, hlim, hlimSp, _, _⟩ :=
    exists_schatten_finite_unitary_approximation_sequence p.toReal hp1.le U hU'
  let V (s : ℝ) : unitary (E →L[ℂ] E) :=
    ⟨NormedSpace.exp (s • (Complex.I • InnerProductSpace.rankOne ℂ x x)),
      rankOne_phase_mem_unitary x s⟩
  have hV : Continuous V :=
    (differentiable_exp_smul_const ℝ (Complex.I • InnerProductSpace.rankOne ℂ x x)).continuous
      |>.subtype_mk _
  let u := Unitary.linearIsometryEquiv.symm U
  let uₙ (n : ℕ) := Unitary.linearIsometryEquiv.symm (Uₙ n)
  have hlu : Tendsto uₙ atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    simpa only [uₙ, u, Unitary.coe_symm_linearIsometryEquiv_apply] using hlim
  have hderivlim := tendstoUniformlyOn_schatten_gradient_pairing_mul_curve p.toReal hp1
    u uₙ hlu V hV x (t - 1) (t + 1)
  let A (s : ℝ) := 1 - (U : E →L[ℂ] E) * (V s : E →L[ℂ] E)
  let Aₙ (n : ℕ) (s : ℝ) := 1 - (Uₙ n : E →L[ℂ] E) * (V s : E →L[ℂ] E)
  have hpoint (s : ℝ) : Tendsto (fun n => (Φ.gauge (Aₙ n s) ^ p.toReal).toReal)
      atTop (𝓝 ((Φ.gauge (A s) ^ p.toReal).toReal)) := by
    let W := Unitary.linearIsometryEquiv (V s)
    have herr (n : ℕ) : Φ.gauge (Aₙ n s - A s) =
        Φ.gauge ((Uₙ n : E →L[ℂ] E) - (U : E →L[ℂ] E)) := by
      have hfactor : Aₙ n s - A s =
          -(((Uₙ n : E →L[ℂ] E) - (U : E →L[ℂ] E)) ∘L (W : E →L[ℂ] E)) := by
        ext y
        change (y - Uₙ n (W y)) - (y - U (W y)) = -(Uₙ n (W y) - U (W y))
        abel
      rw [hfactor, Φ.gauge_neg, Φ.gauge_comp_linearIsometryEquiv_right]
    have herror : Tendsto (fun n => Φ.gauge (Aₙ n s - A s)) atTop (𝓝 0) := by
      simpa only [herr] using hlimSp
    have hcost := Φ.tendsto_gauge_of_tendsto_gauge_sub_zero (A s) (fun n => Aₙ n s) herror
    have hpow := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto
      (Φ.gauge (A s)) |>.comp hcost
    exact (ENNReal.tendsto_toReal (ENNReal.rpow_ne_top_of_nonneg hp0.le
      (schatten_unitary_rankOne_variation_ne_top p.toReal hp1.le U hU x hx s))).comp hpow
  apply hasDerivAt_of_tendstoUniformlyOn (s := Set.Ioo (t - 1) (t + 1)) isOpen_Ioo
    (hderivlim.mono Set.Ioo_subset_Icc_self)
    (Eventually.of_forall fun n s _ =>
      hasDerivAt_schatten_finite_rank_unitary_rankOne_variation p hp hp1 (Uₙ n) (N n) (hN n)
        x hx s)
    (fun s _ => hpoint s) (by constructor <;> linarith)

end TauCeti
