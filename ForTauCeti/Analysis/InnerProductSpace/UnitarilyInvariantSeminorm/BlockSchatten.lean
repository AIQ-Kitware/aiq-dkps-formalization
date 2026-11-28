/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.Polar.Unitary
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.Analysis.InnerProductSpace.BlockSum
import Mathlib.Data.Multiset.Filter

/-!
# Finite singular-value penalties on orthogonal blocks

Every finite sum of an arbitrary singular-value penalty is additive under
orthogonal block sums. TauCeti counts the nonzero singular values of
the two blocks. The source dimensions determine the number of zero
singular values in the finite lists. Finite Schatten powers are a specialization.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal
open Module (finrank)
open UnitarilyInvariantSeminorm

variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]

/-- Every finite singular-value penalty is additive on orthogonal block
sums, including zero singular values and penalties that do not vanish at zero.
No normality or invertibility hypothesis is needed. -/
theorem sum_singularValues_prodMap_withLpMap
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂)
    {M : Type*} [AddCommMonoid M] (f : ℝ → M) :
    (∑ i : Fin (Module.finrank 𝕜 (WithLp 2 (E₁ × E₂))),
      f (((A.prodMap B).withLpMap 2).singularValues i)) =
      (∑ i : Fin (Module.finrank 𝕜 E₁), f (A.singularValues i)) +
        ∑ i : Fin (Module.finrank 𝕜 E₂), f (B.singularValues i) := by
  classical
  let C := (A.prodMap B).withLpMap 2
  let vals (n : ℕ) (σ : ℕ →₀ ℝ) := (Finset.range n).val.map σ
  have count_vals (n : ℕ) (σ : ℕ →₀ ℝ) (hσ : ∀ i, n ≤ i → σ i = 0) {s : ℝ}
      (hs : s ≠ 0) : (vals n σ).count s = {i | σ i = s}.ncard := by
    rw [Multiset.count_map]
    change ((Finset.range n).filter fun i => s = σ i).card = _
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2.symm,
      fun h => ⟨lt_of_not_ge fun hi => hs (h.symm.trans (hσ i hi)), h.symm⟩⟩
  let a := vals (finrank 𝕜 E₁) A.singularValues
  let b := vals (finrank 𝕜 E₂) B.singularValues
  let c := vals (finrank 𝕜 (WithLp 2 (E₁ × E₂))) C.singularValues
  have hcount (s : ℝ) (hs : s ≠ 0) : c.count s = (a + b).count s := by
    dsimp only [c, a, b]
    rw [Multiset.count_add, count_vals _ _ (fun _ => C.singularValues_of_finrank_le) hs,
      count_vals _ _ (fun _ => A.singularValues_of_finrank_le) hs,
      count_vals _ _ (fun _ => B.singularValues_of_finrank_le) hs]
    exact LinearMap.ncard_ofPred_singularValues_prodMap_withLpMap A B
  have hcard : c.card = (a + b).card := by
    simp only [c, a, b, vals, Multiset.card_map, Finset.card_val, Finset.card_range,
      Multiset.card_add, ← Module.finrank_prod]
    exact (WithLp.linearEquiv 2 𝕜 (E₁ × E₂)).finrank_eq
  have hparts (m : Multiset ℝ) :
      m.card = m.count 0 + (m.filter (fun r => 0 ≠ r)).card := by
    rw [Multiset.count_eq_card_filter_eq, ← Multiset.card_add]
    exact congrArg Multiset.card (Multiset.filter_add_not (0 = ·) m).symm
  have hfilter : c.filter (fun r => 0 ≠ r) = (a + b).filter (fun r => 0 ≠ r) := by
    refine Multiset.ext.mpr fun s => ?_
    simp only [Multiset.count_filter]
    split_ifs with hs
    · exact hcount s hs.symm
    · rfl
  have hzero : c.count 0 = (a + b).count 0 := by
    rw [hparts c, hparts (a + b), hfilter] at hcard
    exact Nat.add_right_cancel hcard
  have hvals : c = a + b := by
    refine Multiset.ext.mpr fun s => ?_
    by_cases hs : s = 0
    · simpa only [hs] using hzero
    · exact hcount s hs
  rw [Fin.sum_univ_eq_sum_range (fun i => f (C.singularValues i)),
    Fin.sum_univ_eq_sum_range (fun i => f (A.singularValues i)),
    Fin.sum_univ_eq_sum_range (fun i => f (B.singularValues i))]
  simpa only [c, a, b, vals, C, Finset.sum,
    Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def]
    using congrArg (fun m : Multiset ℝ => (m.map f).sum) hvals

/-- The actual finite Schatten power is additive on orthogonal block
sums of endomorphisms over either real or complex scalars. -/
theorem schatten_rpow_prodMap_withLpMap
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    schatten 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)) p
        ((A.prodMap B).withLpMap 2) ^ p.toReal =
      schatten 𝕜 E₁ E₁ p A ^ p.toReal + schatten 𝕜 E₂ E₂ p B ^ p.toReal := by
  rw [schatten_rpow_eq_sum_singularValues _ p hp,
    schatten_rpow_eq_sum_singularValues A p hp, schatten_rpow_eq_sum_singularValues B p hp]
  exact sum_singularValues_prodMap_withLpMap A B (fun s : ℝ => s ^ p.toReal)

/-- Orthogonal unitary blocks contribute additively to the displacement
power. No unitarity hypothesis is needed for the identity itself. -/
theorem schatten_displacement_rpow_withLpProdMap
    (A : E₁ →L[𝕜] E₁) (B : E₂ →L[𝕜] E₂)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    schatten 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)) p
        (LinearMap.id - (A.withLpProdMap 2 B).toLinearMap) ^ p.toReal =
      schatten 𝕜 E₁ E₁ p (LinearMap.id - A.toLinearMap) ^ p.toReal +
        schatten 𝕜 E₂ E₂ p (LinearMap.id - B.toLinearMap) ^ p.toReal := by
  have hblock : LinearMap.id - (A.withLpProdMap 2 B).toLinearMap =
      ((LinearMap.id - A.toLinearMap).prodMap (LinearMap.id - B.toLinearMap)).withLpMap 2 := by
    rw [ContinuousLinearMap.coe_withLpProdMap]
    ext x
    apply WithLp.ofLp_injective 2
    rfl
  rw [hblock]
  exact schatten_rpow_prodMap_withLpMap _ _ p hp

section Reducing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A reducing subspace splits the actual Schatten power into the powers
of the two restrictions. Neither normality nor invertibility is needed. -/
theorem schatten_rpow_eq_add_restrict_of_isReducing
    (A : E →ₗ[𝕜] E) (N : Submodule 𝕜 E) (hN : N.IsReducing A)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    let h₁ := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
      hN.mem_invtSubmodule
    let h₂ := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
      hN.orthogonal_mem_invtSubmodule
    schatten 𝕜 E E p A ^ p.toReal =
      schatten 𝕜 N N p (A.restrict h₁) ^ p.toReal +
        schatten 𝕜 Nᗮ Nᗮ p (A.restrict h₂) ^ p.toReal := by
  let h₁ := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
    hN.mem_invtSubmodule
  let h₂ := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
    hN.orthogonal_mem_invtSubmodule
  let d := N.orthogonalDecomposition
  let B := ((A.restrict h₁).prodMap (A.restrict h₂)).withLpMap 2
  have hinter (x : WithLp 2 (N × Nᗮ)) : d.symm (B x) = A (d.symm x) := by
    simp only [d, Submodule.orthogonalDecomposition_symm_apply]
    change A (x.fst : E) + A (x.snd : E) = A ((x.fst : E) + (x.snd : E))
    exact (map_add A _ _).symm
  have hblock : B = d.toLinearMap ∘ₗ A ∘ₗ d.symm.toLinearMap := by
    ext x
    apply d.symm.injective
    change d.symm (B x) = d.symm (d (A (d.symm x)))
    rw [hinter, d.symm_apply_apply]
  calc
    _ = schatten 𝕜 (WithLp 2 (N × Nᗮ)) (WithLp 2 (N × Nᗮ)) p B ^ p.toReal := by
      rw [hblock]
      exact congrArg (fun r : ℝ => r ^ p.toReal)
        (schatten_congr_linearIsometryEquiv d d.symm A p hp).symm
    _ = _ := schatten_rpow_prodMap_withLpMap _ _ p hp

/-- Nuclear cost is additive on the actual restrictions of any reducing
subspace, including either summand of dimension zero. -/
theorem nuclear_eq_add_restrict_of_isReducing
    (A : E →ₗ[𝕜] E) (N : Submodule 𝕜 E) (hN : N.IsReducing A) :
    let h₁ := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
      hN.mem_invtSubmodule
    let h₂ := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp
      hN.orthogonal_mem_invtSubmodule
    nuclear 𝕜 E E A = nuclear 𝕜 N N (A.restrict h₁) +
      nuclear 𝕜 Nᗮ Nᗮ (A.restrict h₂) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, schatten_one] using
    schatten_rpow_eq_add_restrict_of_isReducing A N hN 1 ENNReal.one_ne_top

end Reducing

end TauCeti
