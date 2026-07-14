/-
Population-geometry obligations for raw-response Quench.

Goal of this module:

  response distances equal true perspective distances
    -> centered augmented perspective configuration
    -> classical-MDS Gram identity
    -> radial identity used by nearest-neighbor Quench.

The final public theorem should ask for only the first line.  The current
production bridge asks callers to provide all three lines separately.
-/

import DkpsQuench2026.Core.Certificates

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

open Acharyya2024
open Acharyya2025.Deterministic

universe u v wr

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- Centering is a translation, so pairwise differences are unchanged. -/
theorem centerConfig_sub_centerConfig
    {n d : Nat} (z : Config n d) (i j : Fin n) :
    centerConfig z i - centerConfig z j = z i - z j := by
  simp only [centerConfig]
  abel

/-- Centering preserves every pairwise Euclidean distance. -/
theorem norm_centerConfig_sub_centerConfig
    {n d : Nat} (z : Config n d) (i j : Fin n) :
    ‖centerConfig z i - centerConfig z j‖ = ‖z i - z j‖ := by
  rw [centerConfig_sub_centerConfig]

/-- A centered finite configuration has coordinate sum zero.
-/
theorem sum_centerConfig_eq_zero
    {n d : Nat} (hn : 0 < n) (z : Config n d) :
    ∑ i, centerConfig z i = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [centerConfig, configCentroid]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn', one_smul, sub_self]

/-- Classical double centering of exact Euclidean distances recovers the Gram
matrix of the centered configuration.
-/
theorem classicalMDSMatrix_pairDist_eq_centered_gram
    {n d : Nat} (hn : 0 < n) (z : Config n d) (i j : Fin n) :
    classicalMDSMatrix (fun a b => ‖z a - z b‖) i j =
      ∑ k, centerConfig z i k * centerConfig z j k := by
  classical
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Squared distance expanded coordinatewise into Gram entries.
  have hgram : ∀ a b : Fin n, ‖z a - z b‖ ^ 2
      = (∑ k, z a k * z a k) - 2 * (∑ k, z a k * z b k) + (∑ k, z b k * z b k) := by
    intro a b
    rw [PiLp.norm_sq_eq_of_L2]
    have hk : ∀ k, ‖(z a - z b) k‖ ^ 2
        = z a k * z a k - 2 * (z a k * z b k) + z b k * z b k :=
      fun k => by rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]; ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Centroid coordinate.
  have hc : ∀ (a : Fin n) (k : Fin d),
      centerConfig z a k = z a k - (n : ℝ)⁻¹ * ∑ b, z b k := fun a k => by
    simp only [centerConfig, configCentroid, PiLp.sub_apply, PiLp.smul_apply,
      WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  -- Sum-swap helpers.
  have hswR : ∑ k, (∑ b, z b k) * z i k = ∑ b, ∑ k, z i k * z b k := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hswC : ∑ k, (∑ b, z b k) * z j k = ∑ a, ∑ k, z a k * z j k := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hswG : ∑ k, (∑ b, z b k) * (∑ b, z b k) = ∑ a, ∑ b, ∑ k, z a k * z b k := by
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  -- RHS as Gram atoms.
  have hRHS : ∑ k, centerConfig z i k * centerConfig z j k
      = (∑ k, z i k * z j k) - (n : ℝ)⁻¹ * (∑ b, ∑ k, z i k * z b k)
        - (n : ℝ)⁻¹ * (∑ a, ∑ k, z a k * z j k)
        + (n : ℝ)⁻¹ ^ 2 * (∑ a, ∑ b, ∑ k, z a k * z b k) := by
    simp only [hc]
    have hk : ∀ k,
        (z i k - (n : ℝ)⁻¹ * ∑ b, z b k) * (z j k - (n : ℝ)⁻¹ * ∑ b, z b k)
        = z i k * z j k - (n : ℝ)⁻¹ * ((∑ b, z b k) * z i k)
          - (n : ℝ)⁻¹ * ((∑ b, z b k) * z j k)
          + (n : ℝ)⁻¹ ^ 2 * ((∑ b, z b k) * (∑ b, z b k)) :=
      fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hswR, hswC, hswG]
  -- Mean expansions.
  have heRow : ∑ b, ((∑ k, z i k * z i k) - 2 * (∑ k, z i k * z b k)
        + (∑ k, z b k * z b k))
      = (n : ℝ) * (∑ k, z i k * z i k) - 2 * (∑ b, ∑ k, z i k * z b k)
        + (∑ b, ∑ k, z b k * z b k) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have heCol : ∑ a, ((∑ k, z a k * z a k) - 2 * (∑ k, z a k * z j k)
        + (∑ k, z j k * z j k))
      = (∑ a, ∑ k, z a k * z a k) - 2 * (∑ a, ∑ k, z a k * z j k)
        + (n : ℝ) * (∑ k, z j k * z j k) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have heGrand : ∑ a, ∑ b, ((∑ k, z a k * z a k) - 2 * (∑ k, z a k * z b k)
        + (∑ k, z b k * z b k))
      = (n : ℝ) * (∑ a, ∑ k, z a k * z a k) - 2 * (∑ a, ∑ b, ∑ k, z a k * z b k)
        + (n : ℝ) * (∑ b, ∑ k, z b k * z b k) := by
    have hrowa : ∀ a : Fin n,
        ∑ b, ((∑ k, z a k * z a k) - 2 * (∑ k, z a k * z b k) + (∑ k, z b k * z b k))
        = (n : ℝ) * (∑ k, z a k * z a k) - 2 * (∑ b, ∑ k, z a k * z b k)
          + (∑ b, ∑ k, z b k * z b k) := fun a => by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => hrowa a), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Assemble.
  simp only [classicalMDSMatrix, doubleCenter, rowMean, colMean, grandMean, hgram]
  rw [heRow, heCol, heGrand, hRHS]
  field_simp
  ring

/-- The centered target-augmented perspective configuration has the radial
identity needed by the Quench nearest-neighbor engine.
-/
theorem centeredAugmentedPerspectiveConfig_radial
    {Ωref : Type wr} {d : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (n : Nat) (ωref : Ωref) (f : Model Q X) (i : Fin n) :
    ‖centeredAugmentedPerspectiveConfig ψ f_ref n ωref f i.castSucc -
        centeredAugmentedPerspectiveConfig ψ f_ref n ωref f (Fin.last n)‖ =
      ‖ψ (f_ref n ωref i) - ψ f‖ := by
  simp only [centeredAugmentedPerspectiveConfig]
  rw [norm_centerConfig_sub_centerConfig]
  simp [augmentedPerspectiveConfig, augmentedModelAt, Fin.lastCases_castSucc,
    Fin.lastCases_last]

/-- A single population distance-realization assumption yields the exact Gram
identity currently supplied manually to the growing CMDS theorem.
-/
theorem centeredAugmentedPerspectiveConfig_gram_eq
    {Ωref : Type wr} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    (n : Nat) (ωref : Ωref) (f : Model Q X) (i j : Fin (n + 1)) :
    (∑ k,
      centeredAugmentedPerspectiveConfig ψ f_ref n ωref f i k *
      centeredAugmentedPerspectiveConfig ψ f_ref n ωref f j k) =
      classicalMDSMatrix (responseDist (μbar n ωref f)) i j := by
  have key := classicalMDSMatrix_pairDist_eq_centered_gram (n := n + 1) (by omega)
    (augmentedPerspectiveConfig ψ f_ref n ωref f) i j
  have hDeq : (fun a b => ‖augmentedPerspectiveConfig ψ f_ref n ωref f a -
      augmentedPerspectiveConfig ψ f_ref n ωref f b‖) = responseDist (μbar n ωref f) := by
    funext a b
    simp only [augmentedPerspectiveConfig]
    rw [hrealize n ωref f a b]
  simp only [centeredAugmentedPerspectiveConfig]
  rw [← key, hDeq]

/-- Construct all population geometry consumed by growing Quench from the one
paper-facing distance-realization hypothesis.

When the two preceding obligations are completed, every preferred public
capstone can delete the separate `z`, Gram, and radial hypotheses and use this
constructor instead. -/
noncomputable def populationGeometry_of_responseRealization
    {Ωref : Type wr} {d m p : Nat}
    (ψ : Model Q X → Vec d)
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (μbar : ∀ n, Ωref → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar) :
    AugmentedPopulationGeometry ψ f_ref μbar where
  config := centeredAugmentedPerspectiveConfig ψ f_ref
  gram_eq := centeredAugmentedPerspectiveConfig_gram_eq
    ψ f_ref μbar hrealize
  radial_eq := centeredAugmentedPerspectiveConfig_radial ψ f_ref

end DkpsQuench2026
