/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Collecting prescribed bases on positive eigenspaces

A symmetric operator has an orthogonal decomposition into eigenspaces.
Choosing a basis on each positive level with a prescribed vector property
therefore gives a basis on the whole positive point-spectral space with
that property. This retains information supplied on individual levels,
which an arbitrary spectral basis need not preserve.
-/

public section

noncomputable section

namespace LinearMap.IsSymmetric

open Set

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Prescribed orthonormal bases on the positive eigenspaces assemble into
an orthonormal basis of the positive point-spectral space. Every supplied
vector property is retained, and the positive space may be empty. -/
theorem exists_positive_spectral_basis_of_eigenspace_bases
    {B : Module.End 𝕜 E} (hB : B.IsSymmetric) (D : ℝ → E → Prop)
    (hlevel : ∀ r : ℝ, 0 < r → Module.End.HasEigenvalue B (r : 𝕜) →
      ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 (Module.End.eigenspace B (r : 𝕜))))
        𝕜 (Module.End.eigenspace B (r : 𝕜)), ∀ i, D r (b i : E)) :
    let H := B.pointSpectralSubspace (Ioi 0)
    ∃ n : ℕ, ∃ (e : OrthonormalBasis (Fin n) 𝕜 H) (g : Fin n → ℝ),
      (∀ i, 0 < g i) ∧ (∀ i, B (e i : E) = (g i : 𝕜) • (e i : E)) ∧
      ∀ i, D (g i) (e i : E) := by
  classical
  let H := B.pointSpectralSubspace (Ioi 0)
  have hinv : ∀ x ∈ H, B x ∈ H := by
    intro x hx
    exact B.map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hx)
  let T := B.restrict hinv
  have hT : T.IsSymmetric := hB.restrict_invariant hinv
  let A (mu : Module.End.Eigenvalues T) := Module.End.eigenspace T mu.val
  let L (mu : Module.End.Eigenvalues T) := Module.End.eigenspace B (RCLike.re mu.val : 𝕜)
  have hlevel' (mu : Module.End.Eigenvalues T) :
      0 < RCLike.re mu.val ∧
      ∃ b : OrthonormalBasis (Fin (Module.finrank 𝕜 (L mu))) 𝕜 (A mu),
        ∀ i, D (RCLike.re mu.val) ((b i : H) : E) := by
    have hreal : (RCLike.re mu.val : 𝕜) = mu.val :=
      RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self mu.property)
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
      (show Module.End.HasEigenvalue T mu.val from mu.property)
    have hx0 : (x : E) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hxB : B (x : E) = (RCLike.re mu.val : 𝕜) • (x : E) := by
      have h := congrArg (fun y : H => (y : E)) hx.apply_eq_smul
      change B (x : E) = mu.val • (x : E) at h
      rwa [← hreal] at h
    have hpos : 0 < RCLike.re mu.val :=
      (Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp
        (B.pointSpectrumIn_pointSpectralSubspace (Ioi 0)))
        (Module.End.mem_restrictedPointSpectrum x.property hx0 hxB)
    have hLH : L mu ≤ H := Module.End.eigenspace_le_pointSpectralSubspace hpos
    let d : L mu ≃ₗᵢ[𝕜] A mu :=
      { toLinearEquiv :=
          { toFun := fun y => ⟨⟨y, hLH y.property⟩, by
              apply Module.End.mem_eigenspace_iff.mpr
              apply Subtype.ext
              change B (y : E) = mu.val • (y : E)
              rw [← hreal]
              exact Module.End.mem_eigenspace_iff.mp y.property⟩
            invFun := fun y => ⟨((y : H) : E), by
              apply Module.End.mem_eigenspace_iff.mpr
              have h := congrArg (fun z : H => (z : E))
                (Module.End.mem_eigenspace_iff.mp y.property)
              change B ((y : H) : E) = mu.val • ((y : H) : E) at h
              rwa [← hreal] at h⟩
            left_inv := by intro y; rfl
            right_inv := by intro y; rfl
            map_add' := by intro y z; rfl
            map_smul' := by intro c y; rfl }
        norm_map' := by intro y; rfl }
    have heigen : Module.End.HasEigenvalue B (RCLike.re mu.val : 𝕜) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hxB, hx0⟩
    obtain ⟨b, hb⟩ := hlevel (RCLike.re mu.val) hpos heigen
    refine ⟨hpos, b.map d, ?_⟩
    intro i
    change D (RCLike.re mu.val) (b i : E)
    exact hb i
  choose hpos b hb using hlevel'
  let I := (mu : Module.End.Eigenvalues T) × Fin (Module.finrank 𝕜 (L mu))
  let bp : OrthonormalBasis I 𝕜 H :=
    hT.direct_sum_isInternal.collectedOrthonormalBasis hT.orthogonalFamily_eigenspaces' b
  have hbp (i : I) : bp i = (b i.1 i.2 : H) := by
    have h := congrFun (hT.direct_sum_isInternal.collectedBasis_coe
      (fun mu => (b mu).toBasis)) i
    simpa only [bp, DirectSum.IsInternal.collectedOrthonormalBasis,
      Module.Basis.coe_toOrthonormalBasis, OrthonormalBasis.coe_toBasis] using h
  let q := Fintype.equivFin I
  let e := bp.reindex q
  let g (i : Fin (Fintype.card I)) := RCLike.re (q.symm i).1.val
  have he (i) : e i = (b (q.symm i).1 (q.symm i).2 : H) := by
    rw [OrthonormalBasis.reindex_apply]
    exact hbp _
  refine ⟨Fintype.card I, e, g, ?_, ?_, ?_⟩
  · intro i
    exact hpos _
  · intro i
    rw [he]
    have h := congrArg (fun y : H => (y : E))
      (Module.End.mem_eigenspace_iff.mp (b (q.symm i).1 (q.symm i).2).property)
    have hr : (RCLike.re (q.symm i).1.val : 𝕜) = (q.symm i).1.val :=
      RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self (q.symm i).1.property)
    change B ((b (q.symm i).1 (q.symm i).2 : H) : E) =
      (q.symm i).1.val • ((b (q.symm i).1 (q.symm i).2 : H) : E) at h
    rw [← hr] at h
    exact h
  · intro i
    rw [he]
    exact hb _ _

end LinearMap.IsSymmetric

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- A subspace with an orthonormal eigenbasis is invariant under the
ambient operator. The ambient space need not be finite-dimensional. -/
theorem mapsTo_submodule_of_eigenvectors
    {H : Submodule 𝕜 E} (e : OrthonormalBasis ι 𝕜 H)
    (T : E →ₗ[𝕜] E) (lam : ι → 𝕜)
    (he : ∀ i, T (e i : E) = lam i • (e i : E)) :
    ∀ x ∈ H, T x ∈ H := by
  classical
  intro x hx
  let x' : H := ⟨x, hx⟩
  have hrep := congrArg (fun y : H => (y : E)) (e.sum_repr x')
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
  change (∑ i, e.repr x' i • (e i : E)) = x at hrep
  rw [← hrep, map_sum]
  apply H.sum_mem
  intro i _
  rw [map_smul, he]
  exact H.smul_mem _ (H.smul_mem _ (e i).property)

end OrthonormalBasis
