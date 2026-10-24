/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import ForTauCeti.Analysis.InnerProductSpace.PairedInvolutionDecomposition
public import Mathlib.Logic.Equiv.Prod

/-!
# Paired spectral coordinates for an anticommuting involution

The positive and negative spaces of a symmetric operator are exchanged by
an anticommuting isometric involution. Their paired orthogonal complement
is exactly the kernel. The accepted point-spectral-subspace theory provides
the spectral selection and its orthogonal complement.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem map_positive_spectralSpace
    (B : Module.End 𝕜 E) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hanti : ∀ x, B (J x) = -J (B x)) :
    (B.pointSpectralSubspace (Set.Ioi 0)).map J.toLinearMap =
      B.pointSpectralSubspace (Set.Iio 0) := by
  rw [map_pointSpectralSubspace_involution_eq J hJ B hanti]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_Iio, neg_pos]

/-- The positive point-spectral space is orthogonal to its image under an
anticommuting involution. -/
theorem positive_spectralSpace_orthogonal_involution
    (B : Module.End 𝕜 E) (hB : B.IsSymmetric)
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hanti : ∀ x, B (J x) = -J (B x)) :
    ∀ x y : B.pointSpectralSubspace (Set.Ioi 0), ⟪(x : E), J y⟫_𝕜 = 0 := by
  intro x y
  have hdisj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio 0) := Set.disjoint_left.mpr (by
    intro r hr hs
    exact (lt_trans hs hr).false)
  have hy : J y ∈ B.pointSpectralSubspace (Set.Iio 0) := by
    rw [← map_positive_spectralSpace B J hJ hanti]
    exact Submodule.mem_map_of_mem y.property
  exact inner_eq_zero_symm.mp ((hB.isOrtho_pointSpectralSubspace hdisj) x.property (J y) hy)

/-- The orthogonal remainder of the positive-negative spectral pair is
precisely the kernel of the symmetric operator. -/
theorem paired_positive_spectral_orthogonal_eq_ker [FiniteDimensional 𝕜 E]
    (B : Module.End 𝕜 E) (hB : B.IsSymmetric)
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hanti : ∀ x, B (J x) = -J (B x)) :
    (pairedInvolutionEmbedding (B.pointSpectralSubspace (Set.Ioi 0)) J
      (positive_spectralSpace_orthogonal_involution B hB J hJ hanti)).toLinearMap.rangeᗮ =
      LinearMap.ker B := by
  rw [pairedInvolutionEmbedding_range, map_positive_spectralSpace B J hJ hanti,
    ← Module.End.pointSpectralSubspace_union]
  have hs : Set.Ioi (0 : ℝ) ∪ Set.Iio 0 = ({0} : Set ℝ)ᶜ := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h => by rcases h with h | h <;> linarith,
      fun h => lt_or_gt_of_ne (fun hr => h hr.symm)⟩
  rw [hs, hB.orthogonal_pointSpectralSubspace, compl_compl,
    Module.End.pointSpectralSubspace_eq_iSup]
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, RCLike.ofReal_zero,
    Module.End.eigenspace_zero]

private theorem positive_spectralSpace_eigenbasis [FiniteDimensional 𝕜 E]
    (B : Module.End 𝕜 E) (hB : B.IsSymmetric) :
    let K := B.pointSpectralSubspace (Set.Ioi 0)
    ∃ (e : OrthonormalBasis (Fin (Module.finrank 𝕜 K)) 𝕜 K)
      (mu : Fin (Module.finrank 𝕜 K) → ℝ),
      (∀ i, 0 < mu i) ∧ ∀ i, B (e i : E) = (mu i : 𝕜) • (e i : E) := by
  let K := B.pointSpectralSubspace (Set.Ioi 0)
  have hinv : ∀ x ∈ K, B x ∈ K := by
    intro x hx
    exact B.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hx)
  let hBK := hB.restrict_invariant hinv
  let e := hBK.eigenvectorBasis rfl
  let mu := hBK.eigenvalues rfl
  have heigen (i) : B (e i : E) = (mu i : 𝕜) • (e i : E) :=
    congrArg Subtype.val (hBK.apply_eigenvectorBasis rfl i)
  refine ⟨e, mu, ?_, heigen⟩
  intro i
  have hne : (e i : E) ≠ 0 := by
    intro h
    apply e.orthonormal.ne_zero i
    exact Subtype.ext h
  exact (Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp
    (B.pointSpectrumIn_pointSpectralSubspace (Set.Ioi 0)))
    (Module.End.mem_restrictedPointSpectrum (e i).property hne (heigen i))

set_option maxRecDepth 2048 in
/-- A symmetric operator reversed by an isometric involution has an
orthonormal eigenbasis in positive-negative pairs. The involution swaps
each pair and is diagonal on the kernel. The result permits empty positive
or kernel spaces and works over real or complex scalars. -/
theorem exists_paired_spectral_eigenbasis [FiniteDimensional 𝕜 E]
    (B : Module.End 𝕜 E) (hB : B.IsSymmetric)
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hanti : ∀ x, B (J x) = -J (B x)) :
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) 𝕜 E)
      (mu : Fin n → ℝ) (eps : Fin m → ℝ),
      (∀ i, 0 < mu i) ∧
      (∀ i, B (e (.inl (0, i))) = (mu i : 𝕜) • e (.inl (0, i))) ∧
      (∀ i, B (e (.inl (1, i))) = -(mu i : 𝕜) • e (.inl (1, i))) ∧
      (∀ j, B (e (.inr j)) = 0) ∧
      (∀ i, J (e (.inl (0, i))) = e (.inl (1, i))) ∧
      (∀ j, J (e (.inr j)) = (eps j : 𝕜) • e (.inr j)) := by
  classical
  let K := B.pointSpectralSubspace (Set.Ioi 0)
  let horth := positive_spectralSpace_orthogonal_involution B hB J hJ hanti
  let S := (pairedInvolutionEmbedding K J horth).toLinearMap.range
  let d := pairedInvolutionDecomposition K J horth
  obtain ⟨bp, mu, hmu, hbp⟩ := positive_spectralSpace_eigenbasis B hB
  obtain ⟨J₀, hJ₀map, hJ₀inv, _⟩ :=
    pairedInvolutionDecomposition_involution K J horth hJ
  have hJ₀sym : J₀.toLinearMap.IsSymmetric := by
    intro x y
    change ⟪J₀ x, y⟫_𝕜 = ⟪x, J₀ y⟫_𝕜
    have h := J₀.inner_map_map x (J₀ y)
    rw [hJ₀inv] at h
    exact h
  let bf := hJ₀sym.eigenvectorBasis rfl
  let eps := hJ₀sym.eigenvalues rfl
  let n := Module.finrank 𝕜 K
  let m := Module.finrank 𝕜 Sᗮ
  let pairIndex : Fin 2 × Fin n ≃ Fin n ⊕ Fin n :=
    (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n))).trans (Equiv.boolProdEquivSum (Fin n))
  let q := Equiv.sumCongr pairIndex.symm (Equiv.refl (Fin m))
  let e := (((bp.prod bp).prod bf).map d).reindex q
  have he0 (i : Fin n) : e (.inl (0, i)) = (bp i : E) := by
    dsimp only [e]
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
    have hq : q.symm (.inl (0, i)) = .inl (.inl i) := by rfl
    rw [hq]
    simp [d, OrthonormalBasis.prod_apply, pairedInvolutionDecomposition_apply]
  have he1 (i : Fin n) : e (.inl (1, i)) = J (bp i) := by
    dsimp only [e]
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
    have hq : q.symm (.inl (1, i)) = .inl (.inr i) := by rfl
    rw [hq]
    simp [d, OrthonormalBasis.prod_apply, pairedInvolutionDecomposition_apply]
  have hef (j : Fin m) : e (.inr j) = (bf j : E) := by
    dsimp only [e]
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
    have hq : q.symm (.inr j) = .inr j := by rfl
    rw [hq]
    simp [d, OrthonormalBasis.prod_apply, pairedInvolutionDecomposition_apply]
  refine ⟨n, m, e, mu, eps, hmu, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [he0]
    exact hbp i
  · intro i
    rw [he1, hanti, hbp, map_smul, neg_smul]
  · intro j
    rw [hef]
    have hmem : (bf j : E) ∈ LinearMap.ker B := by
      rw [← paired_positive_spectral_orthogonal_eq_ker B hB J hJ hanti]
      exact (bf j).property
    exact LinearMap.mem_ker.mp hmem
  · intro i
    rw [he0, he1]
  · intro j
    rw [hef, ← hJ₀map]
    exact congrArg Subtype.val (hJ₀sym.apply_eigenvectorBasis rfl j)

end TauCeti
