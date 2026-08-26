/-
Growing-dimension foundations for the Acharyya2025 spectral pipeline.

The fixed-population aligned pipeline controls coordinates after choosing an
aligning isometry.  Downstream nearest-neighbor arguments need only pairwise
distances.  Pairwise distances are invariant under the aligning isometry, so a
finite CMDS perturbation bound immediately yields a choice-free distance
perturbation bound.  This file packages that reduction and the deterministic
rate certificate needed when the matrix size varies with the asymptotic stage.
-/

import Acharyya2025.AlignedPipeline

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix Topology
open Filter

namespace Acharyya2025.GrowingPipeline

open Acharyya2024
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.MatrixPerturbation
open Acharyya2025.GramRealization
open Acharyya2025.AlignedPipeline
open TauCeti.Matrix (opSym)

/-- Pairwise distances of two configurations differ by at most twice their
`ConfigError`.  The first configuration may first be transported by an
inner-product-preserving linear map; this does not change its distances. -/
theorem abs_pairwiseDistance_sub_le_two_configError
    {n d : Nat}
    (W : EuclideanSpace Real (Fin d) →ₗ[Real] EuclideanSpace Real (Fin d))
    (hW : ∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ)
    (zhat z : Config n d) (i j : Fin n) :
    |‖zhat i - zhat j‖ - ‖z i - z j‖| ≤
      2 * ConfigError (fun k => W (zhat k)) z := by
  have hnorm : ∀ x, ‖W x‖ = ‖x‖ := by
    intro x
    have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hW x x]
    nlinarith [norm_nonneg (W x), norm_nonneg x]
  have hdist : ‖zhat i - zhat j‖ = ‖W (zhat i) - W (zhat j)‖ := by
    rw [← map_sub, hnorm]
  rw [hdist]
  calc
    |‖W (zhat i) - W (zhat j)‖ - ‖z i - z j‖|
        ≤ ‖(W (zhat i) - W (zhat j)) - (z i - z j)‖ :=
          abs_norm_sub_norm_le _ _
    _ = ‖(W (zhat i) - z i) - (W (zhat j) - z j)‖ := by
          congr 1
          abel
    _ ≤ ‖W (zhat i) - z i‖ + ‖W (zhat j) - z j‖ := norm_sub_le _ _
    _ ≤ 2 * ConfigError (fun k => W (zhat k)) z := by
      have hi := norm_config_le_ConfigError (fun k => W (zhat k)) z i
      have hj := norm_config_le_ConfigError (fun k => W (zhat k)) z j
      linarith

/-- Pairwise distances are controlled directly by Frobenius configuration
error.  This is the growing-dimension route used by Quench: each individual row
error is bounded by `ConfigFrobError`, so no `sqrt n` conversion is needed. -/
theorem abs_pairwiseDistance_sub_le_two_configFrobError
    {n d : Nat}
    (W : EuclideanSpace Real (Fin d) →ₗ[Real] EuclideanSpace Real (Fin d))
    (hW : ∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ)
    (zhat z : Config n d) (i j : Fin n) :
    |‖zhat i - zhat j‖ - ‖z i - z j‖| ≤
      2 * ConfigFrobError (fun k => W (zhat k)) z := by
  have hnorm : ∀ x, ‖W x‖ = ‖x‖ := by
    intro x
    have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hW x x]
    nlinarith [norm_nonneg (W x), norm_nonneg x]
  have hdist : ‖zhat i - zhat j‖ = ‖W (zhat i) - W (zhat j)‖ := by
    rw [← map_sub, hnorm]
  rw [hdist]
  calc
    |‖W (zhat i) - W (zhat j)‖ - ‖z i - z j‖|
        ≤ ‖(W (zhat i) - W (zhat j)) - (z i - z j)‖ :=
          abs_norm_sub_norm_le _ _
    _ = ‖(W (zhat i) - z i) - (W (zhat j) - z j)‖ := by
          congr 1
          abel
    _ ≤ ‖W (zhat i) - z i‖ + ‖W (zhat j) - z j‖ := norm_sub_le _ _
    _ ≤ 2 * ConfigFrobError (fun k => W (zhat k)) z := by
      have hi := norm_config_le_ConfigFrobError (fun k => W (zhat k)) z i
      have hj := norm_config_le_ConfigFrobError (fun k => W (zhat k)) z j
      linarith

/-- Frobenius form of the pairwise spectral perturbation theorem.  Unlike the
legacy `configBound` result below, this theorem does not introduce the final
ambient `sqrt n` factor. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configFrobBound
    {n d : Nat} (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hBhat : Bhat.IsHermitian)
    (hrank : B.rank ≤ d)
    {α Λ η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : Nat) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ i : Fin (Fintype.card (Fin n)), hB.isHermitian.eigenvalues₀ i ≤ Λ)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (z : Config n d)
    (hz : ∀ i j, (∑ k, z i k * z j k) = B i j)
    (i j : Fin n) :
    |‖spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i -
          spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd j‖ -
        ‖z i - z j‖| ≤
      2 * configFrobBound d α Λ ((n : Real) * η) := by
  obtain ⟨W, hW, hconfig⟩ :=
    exists_isometry_configFrobError_le_of_entrywise_close hd B Bhat hB hBhat
      hrank hα_pos hη_nonneg hfloor hΛ hentry z hz
  exact (abs_pairwiseDistance_sub_le_two_configFrobError W hW
    (spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd) z i j).trans
      (mul_le_mul_of_nonneg_left hconfig (by norm_num))

/-- Entrywise CMDS closeness controls every pairwise distance in the raw sample
spectral configuration.  No aligning map appears in the conclusion because
pairwise distances are invariant under the map supplied by the deterministic
spectral theorem. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configBound
    {n d : Nat} (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hBhat : Bhat.IsHermitian)
    (hrank : B.rank ≤ d)
    {α Λ η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : Nat) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ i : Fin (Fintype.card (Fin n)), hB.isHermitian.eigenvalues₀ i ≤ Λ)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (z : Config n d)
    (hz : ∀ i j, (∑ k, z i k * z j k) = B i j)
    (i j : Fin n) :
    |‖spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i -
          spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd j‖ -
        ‖z i - z j‖| ≤
      2 * configBound n d α Λ ((n : Real) * η) := by
  obtain ⟨W, hW, hconfig⟩ :=
    exists_isometry_configError_le_of_entrywise_close hd B Bhat hB hBhat
      hrank hα_pos hη_nonneg hfloor hΛ hentry z hz
  exact (abs_pairwiseDistance_sub_le_two_configError W hW
    (spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd) z i j).trans
      (mul_le_mul_of_nonneg_left hconfig (by norm_num))

/-- Canonical-ceiling version of the pairwise-distance perturbation theorem. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configBound_topEigenvalue
    {n d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) Real)
    (hB : B.PosSemidef) (hBhat : Bhat.IsHermitian)
    (hrank : B.rank ≤ d)
    {α η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : Nat) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (z : Config n d)
    (hz : ∀ i j, (∑ k, z i k * z j k) = B i j)
    (i j : Fin n) :
    |‖spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i -
          spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd j‖ -
        ‖z i - z j‖| ≤
      2 * configBound n d α (topEigenvalue hn hB) ((n : Real) * η) := by
  exact abs_pairwiseDistance_spectralConfig_sub_le_two_configBound hd B Bhat
    hB hBhat hrank hα_pos hη_nonneg hfloor
    (eigenvalues₀_le_topEigenvalue hn hB) hentry z hz i j

/-- Canonical population-realization version. -/
theorem abs_pairwiseDistance_spectralConfig_sub_le_two_configBound_canonical
    {n d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Dhat D : DisMat n)
    (hBhat : (disMatToMatrix (classicalMDSMatrix Dhat)).IsHermitian)
    (hB : (disMatToMatrix (classicalMDSMatrix D)).PosSemidef)
    (hrank : (disMatToMatrix (classicalMDSMatrix D)).rank ≤ d)
    {α η : Real} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : Nat) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hentry : Acharyya2025.Bridge.EntrywiseClose
      (classicalMDSMatrix Dhat) (classicalMDSMatrix D) η)
    (i j : Fin n) :
    |‖spectralConfig
          (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix Dhat)))
          (opSym hBhat) hd i -
        spectralConfig
          (Matrix.toEuclideanLin (disMatToMatrix (classicalMDSMatrix Dhat)))
          (opSym hBhat) hd j‖ -
        ‖canonicalCMDSConfig D hB hrank i - canonicalCMDSConfig D hB hrank j‖| ≤
      2 * configBound n d α (topEigenvalue hn hB) ((n : Real) * η) := by
  apply abs_pairwiseDistance_spectralConfig_sub_le_two_configBound_topEigenvalue
    hn hd
    (disMatToMatrix (classicalMDSMatrix D))
    (disMatToMatrix (classicalMDSMatrix Dhat))
    hB hBhat hrank hα_pos hη_nonneg hfloor hentry
    (canonicalCMDSConfig D hB hrank)
    (canonicalCMDSConfig_gram_eq D hB hrank)

/-- A deterministic certificate for a varying matrix size.  The strengthened
finite spectral theorem no longer needs local `ε ≤ α/2` or polar-applicability
side conditions, so the growing certificate tracks only entrywise nonnegativity
and a vanishing Frobenius configuration envelope. -/
structure GrowingConfigControl
    (count : Nat → Nat) (d : Nat) (α : Real)
    (ceiling entryRate : Nat → Real) where
  entry_nonneg : ∀ u, 0 ≤ entryRate u
  bound : Nat → Real
  bound_nonneg : ∀ u, 0 ≤ bound u
  bound_zero : Tendsto bound atTop (𝓝 0)
  configFrobBound_le : ∀ᶠ u in atTop,
    configFrobBound d α (ceiling u)
      ((count u : Real) * entryRate u) ≤ bound u


/-- Build a growing control certificate from entrywise nonnegativity and a
vanishing exact Frobenius configuration bound. -/
noncomputable def GrowingConfigControl.of_tendsto
    {count : Nat → Nat} {d : Nat} {α : Real}
    {ceiling entryRate : Nat → Real}
    (hentry : ∀ u, 0 ≤ entryRate u)
    (hbound : Tendsto
      (fun u => configFrobBound d α (ceiling u)
        ((count u : Real) * entryRate u)) atTop (𝓝 0)) :
    GrowingConfigControl count d α ceiling entryRate where
  entry_nonneg := hentry
  bound := fun u => configFrobBound d α (ceiling u)
    ((count u : Real) * entryRate u)
  bound_nonneg := by
    intro u
    unfold configFrobBound
    positivity
  bound_zero := hbound
  configFrobBound_le := Filter.Eventually.of_forall fun _ => le_rfl

/-- The final error domination holds eventually. -/
theorem GrowingConfigControl.eventually_all
    {count : Nat → Nat} {d : Nat} {α : Real}
    {ceiling entryRate : Nat → Real}
    (H : GrowingConfigControl count d α ceiling entryRate) :
    ∀ᶠ u in atTop,
      configFrobBound d α (ceiling u)
        ((count u : Real) * entryRate u) ≤ H.bound u :=
  H.configFrobBound_le

/-- The augmented batch size `u + 1` eventually dominates every fixed embedding
dimension. -/
theorem eventually_dimension_le_succ (d : Nat) :
    ∀ᶠ u in atTop, d ≤ u + 1 := by
  exact eventually_atTop.2 ⟨d, fun u hu => by omega⟩

end Acharyya2025.GrowingPipeline
