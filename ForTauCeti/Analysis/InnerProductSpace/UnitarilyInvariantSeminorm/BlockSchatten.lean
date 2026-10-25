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

/-!
# Finite Schatten power sums of orthogonal blocks

The `p`-th power of a finite Schatten norm is additive under orthogonal
block sums. The proof uses the accepted unitary polar decomposition and
orthonormal eigenbases of the two positive moduli. Their product basis
combines the power sums without sorting another singular-value list.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal
open UnitarilyInvariantSeminorm

variable {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]

private theorem schatten_rpow_prodMap_withLpMap_of_eigenbases
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : OrthonormalBasis ι₁ 𝕜 E₁) (b₂ : OrthonormalBasis ι₂ 𝕜 E₂)
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂)
    (mu₁ : ι₁ → 𝕜) (mu₂ : ι₂ → 𝕜)
    (hA : ∀ i, A (b₁ i) = mu₁ i • b₁ i) (hB : ∀ i, B (b₂ i) = mu₂ i • b₂ i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    schatten 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)) p
        ((A.prodMap B).withLpMap 2) ^ p.toReal =
      schatten 𝕜 E₁ E₁ p A ^ p.toReal + schatten 𝕜 E₂ E₂ p B ^ p.toReal := by
  classical
  let mu : ι₁ ⊕ ι₂ → 𝕜 := Sum.elim mu₁ mu₂
  have heigen (i : ι₁ ⊕ ι₂) :
      (A.prodMap B).withLpMap 2 ((b₁.prod b₂) i) = mu i • (b₁.prod b₂) i := by
    cases i with
    | inl i =>
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp [LinearMap.coe_withLpMap, WithLp.map, hA, mu]
    | inr i =>
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp [LinearMap.coe_withLpMap, WithLp.map, hB, mu]
  rw [schatten_rpow_eq_sum_norm_eigenvalues (b₁.prod b₂) _ mu heigen p hp,
    schatten_rpow_eq_sum_norm_eigenvalues b₁ A mu₁ hA p hp,
    schatten_rpow_eq_sum_norm_eigenvalues b₂ B mu₂ hB p hp,
    Fintype.sum_sum_type]
  rfl

/-- The actual finite Schatten power is additive on orthogonal block
sums of endomorphisms over either real or complex scalars. -/
theorem schatten_rpow_prodMap_withLpMap
    (A : E₁ →ₗ[𝕜] E₁) (B : E₂ →ₗ[𝕜] E₂)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    schatten 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)) p
        ((A.prodMap B).withLpMap 2) ^ p.toReal =
      schatten 𝕜 E₁ E₁ p A ^ p.toReal + schatten 𝕜 E₂ E₂ p B ^ p.toReal := by
  let b₁ := A.isSymmetric_operatorAbs.eigenvectorBasis rfl
  let b₂ := B.isSymmetric_operatorAbs.eigenvectorBasis rfl
  let mu₁ (i : Fin (Module.finrank 𝕜 E₁)) : 𝕜 :=
    A.isSymmetric_operatorAbs.eigenvalues rfl i
  let mu₂ (i : Fin (Module.finrank 𝕜 E₂)) : 𝕜 :=
    B.isSymmetric_operatorAbs.eigenvalues rfl i
  obtain ⟨UA, hUA⟩ := A.exists_linearIsometryEquiv_comp_operatorAbs_eq rfl
  obtain ⟨UB, hUB⟩ := B.exists_linearIsometryEquiv_comp_operatorAbs_eq rfl
  change UA.toLinearMap ∘ₗ A.operatorAbs = A at hUA
  change UB.toLinearMap ∘ₗ B.operatorAbs = B at hUB
  have hblock : (A.prodMap B).withLpMap 2 =
      (LinearIsometryEquiv.withLpProdCongr 2 UA UB).toLinearMap ∘ₗ
        (A.operatorAbs.prodMap B.operatorAbs).withLpMap 2 := by
    ext x
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact (LinearMap.congr_fun hUA x.fst).symm
    · exact (LinearMap.congr_fun hUB x.snd).symm
  calc
    _ = schatten 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)) p
        ((A.operatorAbs.prodMap B.operatorAbs).withLpMap 2) ^ p.toReal := by
      rw [hblock]
      exact congrArg (fun r : ℝ => r ^ p.toReal)
        ((schatten 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (E₁ × E₂)) p).map_linearIsometryEquiv_comp
          (LinearIsometryEquiv.withLpProdCongr 2 UA UB)
          ((A.operatorAbs.prodMap B.operatorAbs).withLpMap 2))
    _ = schatten 𝕜 E₁ E₁ p A.operatorAbs ^ p.toReal +
        schatten 𝕜 E₂ E₂ p B.operatorAbs ^ p.toReal :=
      schatten_rpow_prodMap_withLpMap_of_eigenbases b₁ b₂ A.operatorAbs B.operatorAbs
        mu₁ mu₂ (A.isSymmetric_operatorAbs.apply_eigenvectorBasis rfl)
        (B.isSymmetric_operatorAbs.apply_eigenvectorBasis rfl) p hp
    _ = _ := by rw [map_operatorAbs, map_operatorAbs]

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
