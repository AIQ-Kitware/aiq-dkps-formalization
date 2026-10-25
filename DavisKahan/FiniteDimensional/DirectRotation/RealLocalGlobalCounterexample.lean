/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6.1 Sol
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenTransportExistence
import DavisKahan.FiniteDimensional.DirectRotation.RealTwoOptimization

/-!
# Unrestricted real local-to-global optimality is false

On the real line the orthogonal transport fiber of the full subspace to
itself consists of identity and minus identity. Each point is isolated.
Minus identity is therefore a constrained local minimum for every cost,
but its Schatten displacement is positive and identity has cost zero.
This holds for every accepted Schatten exponent at least one, including
one and infinity. Thus the complex local-to-global theorem cannot be
extended to the real field without additional component restrictions.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open scoped ENNReal Topology
open Filter
open TauCeti.Matrix (planeOrthogonal)

private theorem real_line_unitary_eq_one_or_neg_one
    (W : ℝ →L[ℝ] ℝ) (hW : W ∈ unitary (ℝ →L[ℝ] ℝ)) : W = 1 ∨ W = -1 := by
  have habs : |W 1| = 1 := by
    simpa only [Real.norm_eq_abs, norm_one] using
      ContinuousLinearMap.norm_map_of_mem_unitary hW (1 : ℝ)
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · left
    apply ContinuousLinearMap.ext
    intro x
    change W x = x
    simpa only [smul_eq_mul, mul_one, h] using W.map_smul x (1 : ℝ)
  · right
    apply ContinuousLinearMap.ext
    intro x
    change W x = -x
    simpa only [smul_eq_mul, mul_one, h, mul_neg_one] using W.map_smul x (1 : ℝ)

private theorem real_line_neg_one_localMin (f : (ℝ →L[ℝ] ℝ) → ℝ) :
    IsLocalMinOn f (unitary (ℝ →L[ℝ] ℝ) : Set (ℝ →L[ℝ] ℝ)) (-1) := by
  have hne : (-1 : ℝ →L[ℝ] ℝ) ≠ 1 := by
    intro h
    have hh := congrArg (fun W : ℝ →L[ℝ] ℝ => W 1) h
    norm_num at hh
  have hnb : ({(1 : ℝ →L[ℝ] ℝ)} : Set (ℝ →L[ℝ] ℝ))ᶜ ∈ 𝓝 (-1) :=
    isClosed_singleton.isOpen_compl.mem_nhds hne
  change ∀ᶠ W in 𝓝[↑(unitary (ℝ →L[ℝ] ℝ))] (-1), f (-1) ≤ f W
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnb] with W hW hnot
  rcases real_line_unitary_eq_one_or_neg_one W hW with h | h
  · exact (hnot h).elim
  · rw [h]

/-- A fully feasible, nonglobal local minimum of real orthogonal transport
for every Schatten exponent at least one. The actual source and target
are the full real line; their principal angle is zero. -/
theorem real_line_schatten_nonglobal_local_minimum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    let K : Submodule ℝ ℝ := ⊤
    let f := fun W : ℝ →L[ℝ] ℝ => UnitarilyInvariantSeminorm.schatten ℝ ℝ ℝ p
      (LinearMap.id - W.toLinearMap)
    let S := {W : ℝ →L[ℝ] ℝ | W ∈ unitary (ℝ →L[ℝ] ℝ) ∧
      W * K.starProjection * star W = K.starProjection}
    (-1 : ℝ →L[ℝ] ℝ) ∈ S ∧ IsLocalMinOn f S (-1) ∧ ¬IsMinOn f S (-1) := by
  dsimp only
  let f := fun W : ℝ →L[ℝ] ℝ => UnitarilyInvariantSeminorm.schatten ℝ ℝ ℝ p
    (LinearMap.id - W.toLinearMap)
  have hS : {W : ℝ →L[ℝ] ℝ | W ∈ unitary (ℝ →L[ℝ] ℝ) ∧
      W * (⊤ : Submodule ℝ ℝ).starProjection * star W =
        (⊤ : Submodule ℝ ℝ).starProjection} =
      (unitary (ℝ →L[ℝ] ℝ) : Set (ℝ →L[ℝ] ℝ)) := by
    ext W
    constructor
    · exact fun h => h.1
    · intro hW
      refine ⟨hW, ?_⟩
      rw [Submodule.starProjection_top]
      change W * 1 * star W = 1
      rw [mul_one]
      exact Unitary.mul_star_self_of_mem hW
  rw [hS]
  have hneg : (-1 : ℝ →L[ℝ] ℝ) ∈ unitary (ℝ →L[ℝ] ℝ) := by
    apply Unitary.mem_iff.mpr
    have hs : star (-1 : ℝ →L[ℝ] ℝ) = -1 := by rw [star_neg, star_one]
    have hm : (-1 : ℝ →L[ℝ] ℝ) * (-1) = 1 :=
      (neg_mul_neg (1 : ℝ →L[ℝ] ℝ) 1).trans (one_mul 1)
    constructor <;> rw [hs] <;> exact hm
  refine ⟨hneg, real_line_neg_one_localMin f, ?_⟩
  intro hglobal
  have hbound := hglobal (one_mem (unitary (ℝ →L[ℝ] ℝ)))
  have hzero : f 1 = 0 := by
    change UnitarilyInvariantSeminorm.schatten ℝ ℝ ℝ p (LinearMap.id - LinearMap.id) = 0
    rw [sub_self, map_zero]
  change f (-1) ≤ f 1 at hbound
  rw [hzero] at hbound
  have hcost : f (-1) = 0 := le_antisymm hbound (apply_nonneg _ _)
  have hmap : LinearMap.id - (-1 : ℝ →L[ℝ] ℝ).toLinearMap = 0 :=
    (UnitarilyInvariantSeminorm.schatten_apply_eq_zero_iff p).mp hcost
  have h := congrArg (fun A : ℝ →ₗ[ℝ] ℝ => A 1) hmap
  norm_num at h

/-- Every planar reflection is a constrained local minimum for every
spectral penalty: its negative-determinant component has constant cost.
The transported source line may have any principal angle. -/
theorem plane_reflection_isLocalMinOn (rho : ℝ → ℝ) (t : ℝ) :
    IsLocalMinOn (twoDisplacementCost rho)
      {W : Matrix (Fin 2) (Fin 2) ℝ | W.transpose * W = 1 ∧
        W * twoSourceProjection * W.transpose =
          planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose}
      (planeOrthogonal t (-1)) := by
  have hdet : Continuous (fun W : Matrix (Fin 2) (Fin 2) ℝ => W.det) := by
    simp_rw [Matrix.det_fin_two]
    fun_prop
  have hnb : {W : Matrix (Fin 2) (Fin 2) ℝ | W.det < 0} ∈ 𝓝 (planeOrthogonal t (-1)) := by
    apply (isOpen_lt hdet continuous_const).mem_nhds
    change (planeOrthogonal t (-1)).det < 0
    rw [TauCeti.Matrix.det_planeOrthogonal]
    norm_num
  change ∀ᶠ W in 𝓝[{W : Matrix (Fin 2) (Fin 2) ℝ | W.transpose * W = 1 ∧
    W * twoSourceProjection * W.transpose =
      planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose}]
      (planeOrthogonal t (-1)),
    twoDisplacementCost rho (planeOrthogonal t (-1)) ≤ twoDisplacementCost rho W
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnb] with W hW hneg
  obtain ⟨he, a, hform⟩ := TauCeti.Matrix.exists_planeOrthogonal_of_transpose_mul_eq_one W hW.1
  have hdetW : W.det = -1 := by
    rcases he with he | he
    · rw [he] at hneg
      norm_num at hneg
    · exact he
  rw [hform, hdetW, twoDisplacementCost_reflection, twoDisplacementCost_reflection]

/-- Even for a proper real line pair with positive acute angle `pi/3`,
every Schatten power `p>1` has a nonglobal constrained local minimum.
The reflection is locally minimizing at cost `2^p`, whereas the canonical
rotation has cost two. The two competitors lie in different open
orthogonal determinant components. -/
theorem plane_schatten_nonglobal_local_minimum (p : ℝ) (hp : 1 < p) :
    let t := Real.pi/3
    let S := {W : Matrix (Fin 2) (Fin 2) ℝ | W.transpose * W = 1 ∧
      W * twoSourceProjection * W.transpose =
        planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose}
    planeOrthogonal t (-1) ∈ S ∧
      IsLocalMinOn (twoDisplacementCost (fun s => s^p)) S (planeOrthogonal t (-1)) ∧
      ¬IsMinOn (twoDisplacementCost (fun s => s^p)) S (planeOrthogonal t (-1)) := by
  dsimp only
  refine ⟨planeOrthogonal_mem_transport_fiber _ _ (by norm_num),
    plane_reflection_isLocalMinOn _ _, ?_⟩
  intro hglobal
  have hbound := hglobal (planeOrthogonal_mem_transport_fiber (Real.pi/3) 1 (by norm_num))
  change twoDisplacementCost (fun s => s^p) (planeOrthogonal (Real.pi/3) (-1)) ≤
    twoDisplacementCost (fun s => s^p) (planeOrthogonal (Real.pi/3) 1) at hbound
  rw [twoDisplacementCost_reflection, twoDisplacementCost_rotation] at hbound
  norm_num [Real.cos_pi_div_three, Real.zero_rpow (show p ≠ 0 by linarith)] at hbound
  have hstrict := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
  rw [Real.rpow_one] at hstrict
  exact (not_lt_of_ge hbound) hstrict

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
