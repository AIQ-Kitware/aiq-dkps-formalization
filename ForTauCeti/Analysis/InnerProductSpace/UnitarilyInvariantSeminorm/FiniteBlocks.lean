/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Spectral costs on a complete finite orthogonal block decomposition

Collect the singular bases of the actual restrictions, retaining every
zero column. Their right and left families are ambient orthonormal bases.
An ambient isometry identifies the left family with the right one, leaving
a diagonal operator whose singular-value sum is the sum of the individual
block sums. The penalty need not vanish at zero and the operator need not
be normal or invertible. This is classical finite spectral additivity.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [Fintype ι]

/-- A complete finite orthogonal invariant family splits every full
singular-value penalty exactly, including zeros and empty blocks. -/
theorem sum_singularValues_of_orthogonal_blocks
    (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤) (A : E →ₗ[𝕜] E)
    (hinv : ∀ i, ∀ x ∈ W i, A x ∈ W i)
    {M : Type*} [AddCommMonoid M] (f : ℝ → M) :
    (∑ j : Fin (Module.finrank 𝕜 E), f (A.singularValues j)) =
      ∑ i, ∑ j : Fin (Module.finrank 𝕜 (W i)),
        f ((A.restrict (hinv i)).singularValues j) := by
  classical
  have hi : DirectSum.IsInternal W := horth.isInternal_iff.mpr (by rw [hspan]; simp)
  let B (i : ι) := A.restrict (hinv i)
  choose U hU using fun i => (B i).exists_linearIsometryEquiv_comp_operatorAbs_eq rfl
  let b (i : ι) := (B i).isSymmetric_operatorAbs.eigenvectorBasis rfl
  let c (i : ι) := (b i).map (U i)
  let mu (i : ι) (j : Fin (Module.finrank 𝕜 (W i))) : 𝕜 :=
    (B i).isSymmetric_operatorAbs.eigenvalues rfl j
  have heigen (i j) : (B i).operatorAbs (b i j) = mu i j • b i j :=
    (B i).isSymmetric_operatorAbs.apply_eigenvectorBasis rfl j
  let J := (i : ι) × Fin (Module.finrank 𝕜 (W i))
  let br : OrthonormalBasis J 𝕜 E := hi.collectedOrthonormalBasis horth b
  let bl : OrthonormalBasis J 𝕜 E := hi.collectedOrthonormalBasis horth c
  have hbr (j : J) : br j = (b j.1 j.2 : E) := by
    have h := congrFun (hi.collectedBasis_coe (fun i => (b i).toBasis)) j
    simpa only [br, DirectSum.IsInternal.collectedOrthonormalBasis,
      Module.Basis.coe_toOrthonormalBasis, OrthonormalBasis.coe_toBasis] using h
  have hbl (j : J) : bl j = (c j.1 j.2 : E) := by
    have h := congrFun (hi.collectedBasis_coe (fun i => (c i).toBasis)) j
    simpa only [bl, DirectSum.IsInternal.collectedOrthonormalBasis,
      Module.Basis.coe_toOrthonormalBasis, OrthonormalBasis.coe_toBasis] using h
  have hA (j : J) : A (br j) = mu j.1 j.2 • bl j := by
    rw [hbr, hbl]
    have hlocal : B j.1 (b j.1 j.2) = mu j.1 j.2 • c j.1 j.2 := by
      rw [← hU j.1]
      change U j.1 ((B j.1).operatorAbs (b j.1 j.2)) =
        mu j.1 j.2 • U j.1 (b j.1 j.2)
      rw [heigen, map_smul]
    exact congrArg Subtype.val hlocal
  let Q := br.repr.trans bl.repr.symm
  have hQ (j : J) : Q.symm (bl j) = br j := by
    simp [Q]
  let D := Q.symm.toLinearMap ∘ₗ A
  have hD (j : J) : D (br j) = mu j.1 j.2 • br j := by
    change Q.symm (A (br j)) = _
    rw [hA, map_smul, hQ]
  have hsv : D.singularValues = A.singularValues := by
    change ((Q.symm : E →ₗ[𝕜] E) ∘ₗ A).singularValues = _
    exact LinearMap.singularValues_linearIsometryEquiv_comp Q.symm A
  calc
    _ = ∑ j : Fin (Module.finrank 𝕜 E), f (D.singularValues j) := by
      rw [hsv]
    _ = ∑ j : J, f ‖mu j.1 j.2‖ :=
      sum_singularValues_eq_sum_norm_eigenvalues br D _ hD f
    _ = ∑ i, ∑ j, f ‖mu i j‖ := Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      change (∑ j : Fin (Module.finrank 𝕜 (W i)), f ((B i).singularValues j)) = _
      rw [← LinearMap.singularValues_operatorAbs (B i)]
      exact sum_singularValues_eq_sum_norm_eigenvalues (b i) (B i).operatorAbs
        (mu i) (heigen i) f

/-- The accepted finite Schatten power is the sum of the actual
restriction powers on a complete orthogonal invariant family. -/
theorem schatten_rpow_of_orthogonal_blocks
    (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤) (A : E →ₗ[𝕜] E)
    (hinv : ∀ i, ∀ x ∈ W i, A x ∈ W i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 E E p A ^ p.toReal =
      ∑ i, UnitarilyInvariantSeminorm.schatten 𝕜 (W i) (W i) p
        (A.restrict (hinv i)) ^ p.toReal := by
  rw [schatten_rpow_eq_sum_singularValues A p hp,
    sum_singularValues_of_orthogonal_blocks W horth hspan A hinv (fun s => s^p.toReal)]
  apply Finset.sum_congr rfl
  intro i _
  exact (schatten_rpow_eq_sum_singularValues _ p hp).symm

/-- Displacement power is the sum of the actual compressed displacement
powers on any complete orthogonal invariant family. The compressions are
defined without choosing or bundling restricted unitary maps. -/
theorem schatten_displacement_rpow_of_orthogonal_blocks
    (W : ι → Submodule 𝕜 E)
    (horth : OrthogonalFamily 𝕜 (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (hspan : (⨆ i, W i) = ⊤) (T : E →L[𝕜] E)
    (hinv : ∀ i, ∀ x ∈ W i, T x ∈ W i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten 𝕜 E E p
      (LinearMap.id - T.toLinearMap) ^ p.toReal =
      ∑ i, UnitarilyInvariantSeminorm.schatten 𝕜 (W i) (W i) p
        (LinearMap.id - ((W i).orthogonalProjectionOnto.toLinearMap ∘ₗ
          T.toLinearMap ∘ₗ (W i).subtype)) ^ p.toReal := by
  have hsub : ∀ i, ∀ x ∈ W i,
      ((LinearMap.id : E →ₗ[𝕜] E) - T.toLinearMap) x ∈ W i :=
    fun i x hx => (W i).sub_mem hx (hinv i x hx)
  rw [schatten_rpow_of_orthogonal_blocks W horth hspan _ hsub p hp]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext x
  change (x : E) - T x = (x : E) - (W i).starProjection (T x)
  rw [(W i).starProjection_eq_self_iff.mpr (hinv i x x.property)]

end TauCeti
