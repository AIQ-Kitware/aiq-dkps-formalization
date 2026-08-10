/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: unitary classification of compact self-adjoint operators.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compact self-adjoint operators are classified by their eigenspace dimensions

A compact self-adjoint operator with trivial kernel is determined, up to unitary
equivalence, by the function `μ ↦ dim ker(T - μ)`.  That is the coordinate-free
form of "the decreasing list of eigenvalues, with multiplicity, is a complete
invariant".

## The construction

Mathlib's spectral theorem for compact self-adjoint operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) says the
eigenspaces span densely, and
`ContinuousLinearMap.finite_dimensional_eigenspace` says each one attached to a
nonzero eigenvalue is finite-dimensional.  With trivial kernel *every* eigenspace
is finite-dimensional, so each is isometric to `EuclideanSpace 𝕜 (Fin d)` for
`d` its dimension.

The point of routing through the Euclidean model rather than through the
eigenspaces themselves is that it makes both operators Hilbert sums over the
*same* family of model spaces, so the two `IsHilbertSum.linearIsometryEquiv`s
land in a single `lp` space and compose directly.  Mathlib has no congruence
`lp G 2 ≃ₗᵢ lp G' 2` from a family of isometries `G i ≃ₗᵢ G' i`, and this
sidesteps needing one.

## Main results

* `TauCeti.euclideanSubmoduleEquiv`: a finite-dimensional subspace is isometric
  to the Euclidean space of its dimension.
* `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`:
  the classification.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

/-! ## A finite-dimensional subspace, in Euclidean coordinates -/

/-- A finite-dimensional subspace is isometric to the Euclidean space of its
dimension.  The dimension is passed as an equation so the model index can be
chosen by the caller — which is what lets two subspaces of *different* ambient
spaces share one model. -/
noncomputable def euclideanSubmoduleEquiv {𝕜 : Type*} [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (K : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 K] {n : ℕ} (hn : finrank 𝕜 K = n) :
    EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] K :=
  ((stdOrthonormalBasis 𝕜 K).reindex (finCongr hn)).repr.symm

/-! ## The classification -/

section Classification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- With trivial kernel, *every* eigenspace of a compact operator is
finite-dimensional: the nonzero eigenvalues by Mathlib's spectral theorem, and
`0` because its eigenspace is trivial. -/
theorem finiteDimensional_eigenspace_of_isCompactOperator {A : E →L[𝕜] E}
    (hAc : IsCompactOperator A) (hA0 : eigenspace A.toLinearMap 0 = ⊥) (μ : 𝕜) :
    FiniteDimensional 𝕜 (eigenspace A.toLinearMap μ) := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [hA0]
    infer_instance
  · exact ContinuousLinearMap.finite_dimensional_eigenspace hAc μ hμ

/-- **Compact self-adjoint operators with trivial kernel are classified by their
eigenspace dimensions.**

`dim ker(A - μ) = dim ker(B - μ)` for every `μ` is exactly "the eigenvalues
agree, with multiplicity"; the conclusion is a unitary intertwining the two
operators.  The trivial-kernel hypothesis is what makes the two spaces have the
same size — without it one could pad either side with an arbitrary kernel. -/
theorem exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (hA0 : eigenspace A.toLinearMap 0 = ⊥) (hB0 : eigenspace B.toLinearMap 0 = ⊥)
    (hdim : ∀ μ : 𝕜, finrank 𝕜 (eigenspace A.toLinearMap μ) =
      finrank 𝕜 (eigenspace B.toLinearMap μ)) :
    ∃ W : E ≃ₗᵢ[𝕜] F, ∀ x, W (A x) = B (W x) := by
  classical
  have hfA : ∀ μ : 𝕜, FiniteDimensional 𝕜 (eigenspace A.toLinearMap μ) :=
    finiteDimensional_eigenspace_of_isCompactOperator hAc hA0
  have hfB : ∀ μ : 𝕜, FiniteDimensional 𝕜 (eigenspace B.toLinearMap μ) :=
    finiteDimensional_eigenspace_of_isCompactOperator hBc hB0
  -- The common model family, indexed by `μ`.
  set G : 𝕜 → Type _ := fun μ =>
    EuclideanSpace 𝕜 (Fin (finrank 𝕜 (eigenspace A.toLinearMap μ))) with hG
  -- The two coordinatizations of the eigenspaces.
  set eA : ∀ μ : 𝕜, G μ ≃ₗᵢ[𝕜] eigenspace A.toLinearMap μ := fun μ =>
    euclideanSubmoduleEquiv _ rfl with heA
  set eB : ∀ μ : 𝕜, G μ ≃ₗᵢ[𝕜] eigenspace B.toLinearMap μ := fun μ =>
    euclideanSubmoduleEquiv _ (hdim μ).symm with heB
  set VA : ∀ μ : 𝕜, G μ →ₗᵢ[𝕜] E := fun μ =>
    (eigenspace A.toLinearMap μ).subtypeₗᵢ.comp (eA μ).toLinearIsometry with hVA
  set VB : ∀ μ : 𝕜, G μ →ₗᵢ[𝕜] F := fun μ =>
    (eigenspace B.toLinearMap μ).subtypeₗᵢ.comp (eB μ).toLinearIsometry with hVB
  -- Each model maps onto the corresponding eigenspace.
  have hrangeA : ∀ μ : 𝕜, LinearMap.range (VA μ).toLinearMap =
      eigenspace A.toLinearMap μ := by
    intro μ
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact (eA μ x).2
    · intro y hy
      exact ⟨(eA μ).symm ⟨y, hy⟩, by simp [hVA]⟩
  have hrangeB : ∀ μ : 𝕜, LinearMap.range (VB μ).toLinearMap =
      eigenspace B.toLinearMap μ := by
    intro μ
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact (eB μ x).2
    · intro y hy
      exact ⟨(eB μ).symm ⟨y, hy⟩, by simp [hVB]⟩
  -- Both are Hilbert sums over the same model family.
  have horthoA : OrthogonalFamily 𝕜 G VA := by
    intro i j hij v w
    exact hAs.isSymmetric.orthogonalFamily_eigenspaces hij (eA i v) (eA j w)
  have horthoB : OrthogonalFamily 𝕜 G VB := by
    intro i j hij v w
    exact hBs.isSymmetric.orthogonalFamily_eigenspaces hij (eB i v) (eB j w)
  have htotalA : ⊤ ≤ (⨆ μ : 𝕜, LinearMap.range (VA μ).toLinearMap).topologicalClosure := by
    simp only [hrangeA]
    exact le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc
        hAs.isSymmetric)).symm
  have htotalB : ⊤ ≤ (⨆ μ : 𝕜, LinearMap.range (VB μ).toLinearMap).topologicalClosure := by
    simp only [hrangeB]
    exact le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hBc
        hBs.isSymmetric)).symm
  have hsumA : IsHilbertSum 𝕜 G VA := IsHilbertSum.mk horthoA htotalA
  have hsumB : IsHilbertSum 𝕜 G VB := IsHilbertSum.mk horthoB htotalB
  refine ⟨hsumA.linearIsometryEquiv.trans hsumB.linearIsometryEquiv.symm, ?_⟩
  set W := hsumA.linearIsometryEquiv.trans hsumB.linearIsometryEquiv.symm with hWdef
  -- `W` sends the `μ`-model to the `μ`-model, hence eigenspace onto eigenspace.
  have hWmodel : ∀ (μ : 𝕜) (x : G μ), W (VA μ x) = VB μ x := by
    intro μ x
    have hA : hsumA.linearIsometryEquiv (VA μ x) = lp.single 2 μ x := by
      rw [← hsumA.linearIsometryEquiv_symm_apply_single x,
        LinearIsometryEquiv.apply_symm_apply]
    rw [hWdef]
    simp only [LinearIsometryEquiv.trans_apply, hA]
    exact hsumB.linearIsometryEquiv_symm_apply_single x
  have hWmaps : ∀ (μ : 𝕜), ∀ y ∈ eigenspace A.toLinearMap μ,
      W y ∈ eigenspace B.toLinearMap μ := by
    intro μ y hy
    obtain ⟨x, rfl⟩ := (hrangeA μ).ge hy
    rw [show (VA μ).toLinearMap x = VA μ x from rfl, hWmodel]
    exact (hrangeB μ).le ⟨x, rfl⟩
  -- On each eigenspace both maps are multiplication by `μ`; extend by density.
  have hEq : ∀ y ∈ (⨆ μ : 𝕜, eigenspace A.toLinearMap μ), W (A y) = B (W y) := by
    intro y hy
    refine Submodule.iSup_induction (motive := fun z => W (A z) = B (W z))
      (fun μ : 𝕜 => eigenspace A.toLinearMap μ) hy ?_ ?_ ?_
    · intro μ z hz
      have hAz : A z = μ • z := Module.End.mem_eigenspace_iff.mp hz
      have hBz : B (W z) = μ • W z :=
        Module.End.mem_eigenspace_iff.mp (hWmaps μ z hz)
      rw [hAz, map_smul, hBz]
    · simp
    · intro a b ha hb
      simp only [map_add, ha, hb]
  have hdense : Dense ((⨆ μ : 𝕜, eigenspace A.toLinearMap μ : Submodule 𝕜 E) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr
        (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc
          hAs.isSymmetric))
  have hcont₁ : Continuous fun x : E => W (A x) := W.continuous.comp A.continuous
  have hcont₂ : Continuous fun x : E => B (W x) := B.continuous.comp W.continuous
  exact fun x => congrFun (Continuous.ext_on hdense hcont₁ hcont₂ hEq) x

end Classification

end TauCeti
