/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidtConjugation

/-!
# Strong continuity of a conjugation flow on the Hilbert–Schmidt space

The Sylvester flow `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` is a one-parameter unitary
group on the Hilbert–Schmidt operators.  Unitarity is
`HilbertSchmidtConjugation`; this module supplies the analytic half, strong
continuity, whose whole content is the estimate proved here:

`tendsto_energy_sub_comp` — for a Hilbert–Schmidt `S` and a strongly continuous
family of isometries `W` with `W 0 = 1`, the Hilbert–Schmidt energy of
`(W t - 1) ∘ S` tends to `0`.

Strong continuity of a *bounded* operator flow would be immediate; it is
Hilbert–Schmidt convergence that has content, because the columns must go to
zero **together**.  The argument is the usual `ε`-split: a finite set of columns
carries all but `ε/5` of the energy, the remaining columns are controlled
uniformly in `t` by `‖W t x - x‖ ≤ 2 ‖x‖`, and the finite part is a finite sum
of continuous functions vanishing at `t = 0`.

It is carried out in `ℝ≥0∞` rather than in `ℝ` on purpose: there the sum splits
unconditionally (`ENNReal.sum_add_tsum_compl`) and the tail estimate
(`ENNReal.tendsto_tsum_compl_atTop_zero`) needs no summability side condition,
so no part of the bookkeeping is spent on convergence hypotheses.

## Provenance

*New.*  The donor obtains strong continuity from the tensor-product functor
applied to the two factor groups; nothing of that is used.
-/

open scoped ENNReal NNReal
open Filter Topology

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A displacement by an isometry is at most twice the vector. -/
theorem enorm_sub_sq_le (W : E →L[𝕜] E) (hW : ∀ x : E, ‖W x‖ = ‖x‖) (x : E) :
    ‖W x - x‖ₑ ^ 2 ≤ 4 * ‖x‖ₑ ^ 2 := by
  have hle : ‖W x - x‖ₑ ≤ 2 * ‖x‖ₑ := by
    refine le_trans enorm_sub_le ?_
    have : ‖W x‖ₑ = ‖x‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact congrArg _ (NNReal.coe_injective (hW x))
    rw [this, two_mul]
  calc ‖W x - x‖ₑ ^ 2 ≤ (2 * ‖x‖ₑ) ^ 2 := by gcongr
    _ = 4 * ‖x‖ₑ ^ 2 := by ring

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Hilbert–Schmidt energy of `(W t - 1) ∘ S` vanishes as `t → 0`.**

This is the estimate behind strong continuity of any conjugation flow on the
Hilbert–Schmidt space.  Note what is *not* assumed: `W` need not be a group, and
no relation between different `t` is used — only that each `W t` is an isometry,
that `t ↦ W t x` is continuous for each fixed `x`, and that `W 0 = 1`. -/
theorem tendsto_energy_sub_comp (b : HilbertBasis ι 𝕜 F) (S : F →L[𝕜] E)
    (hS : S.hilbertSchmidtEnergy b ≠ ⊤)
    (W : ℝ → (E →L[𝕜] E)) (hiso : ∀ (t : ℝ) (x : E), ‖W t x‖ = ‖x‖)
    (hcont : ∀ x : E, Continuous fun t : ℝ => W t x) (hzero : ∀ x : E, W 0 x = x) :
    Tendsto (fun t : ℝ => ∑' i, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hEdef : ∑' i, ‖S (b i)‖ₑ ^ 2 ≠ ⊤ := by
    rw [← ContinuousLinearMap.hilbertSchmidtEnergy_def]; exact hS
  set δ : ℝ≥0∞ := ε / 5 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact ENNReal.div_pos hε.ne' (by norm_num)
  -- A finite set of columns carrying all but `δ` of the energy.
  obtain ⟨s, hs⟩ :=
    ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero hEdef)).2 δ hδ).exists
  -- The tail is uniformly small in `t`.
  have htail : ∀ t : ℝ,
      ∑' i : ↥((s : Set ι))ᶜ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2 ≤ 4 * δ := by
    intro t
    calc ∑' i : ↥((s : Set ι))ᶜ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
        ≤ ∑' i : ↥((s : Set ι))ᶜ, 4 * ‖S (b i)‖ₑ ^ 2 :=
          ENNReal.tsum_le_tsum fun i => enorm_sub_sq_le (W t) (hiso t) _
      _ = 4 * ∑' i : ↥((s : Set ι))ᶜ, ‖S (b i)‖ₑ ^ 2 := ENNReal.tsum_mul_left
      _ ≤ 4 * δ := by gcongr; exact hs.le
  -- The finite part is a finite sum of continuous functions vanishing at `0`.
  have hfin : Tendsto (fun t : ℝ => ∑ i ∈ s, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
    have hterm : ∀ i ∈ s,
        Tendsto (fun t : ℝ => ‖W t (S (b i)) - S (b i)‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
      intro i _
      have heq : ∀ t : ℝ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
          = ENNReal.ofReal (‖W t (S (b i)) - S (b i)‖ ^ 2) := by
        intro t
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
      simp_rw [heq]
      have hc : Continuous fun t : ℝ => ENNReal.ofReal (‖W t (S (b i)) - S (b i)‖ ^ 2) :=
        ENNReal.continuous_ofReal.comp (((hcont _).sub continuous_const).norm.pow 2)
      have := hc.tendsto (0 : ℝ)
      simpa [hzero] using this
    simpa using tendsto_finsetSum s hterm
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hfin) δ hδ] with t ht
  calc ∑' i, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2
        + ∑' i : ↥((s : Set ι))ᶜ, ‖W t (S (b i)) - S (b i)‖ₑ ^ 2 :=
        (ENNReal.sum_add_tsum_compl s _).symm
    _ ≤ δ + 4 * δ := add_le_add ht (htail t)
    _ = 5 * δ := by ring
    _ = ε := by rw [hδdef, ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]

end HilbertSchmidt
end TauCeti
