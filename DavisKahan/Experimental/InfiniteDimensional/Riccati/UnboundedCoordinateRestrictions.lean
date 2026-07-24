/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.UnboundedReductionTransport

/-!
# Coordinate domains of a reduced unbounded direct-sum operator

This leaf isolates the algebraic and domain decomposition needed before the two
closed diagonal restrictions are constructed.  For a closed operator reducing
the first coordinate summand, its domain splits exactly into coordinate-domain
pieces, and its action on each piece has no off-diagonal coordinate.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

abbrev DirectSumSpace := WithLp 2 (E0 × E1)

/-- The first-coordinate domain induced by a closed operator on the direct sum. -/
noncomputable def closedOperatorCoordinateDomain0
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1))) :
    Submodule ℂ E0 :=
  D.domain.comap
    (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)).toLinearMap

/-- The second-coordinate domain induced by a closed operator on the direct sum. -/
noncomputable def closedOperatorCoordinateDomain1
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1))) :
    Submodule ℂ E1 :=
  D.domain.comap
    (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)).toLinearMap

@[simp] theorem mem_closedOperatorCoordinateDomain0_iff
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (u : E0) :
    u ∈ closedOperatorCoordinateDomain0 D ↔
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u ∈ D.domain :=
  Iff.rfl

@[simp] theorem mem_closedOperatorCoordinateDomain1_iff
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (v : E1) :
    v ∈ closedOperatorCoordinateDomain1 D ↔
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v ∈ D.domain :=
  Iff.rfl

/-- Bundle a first-coordinate domain vector as an element of the ambient
operator domain. -/
noncomputable def closedOperatorCoordinateDomain0ToOriginal
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1))) :
    closedOperatorCoordinateDomain0 D →ₗ[ℂ] D.domain where
  toFun u :=
    ⟨blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (u : E0), u.property⟩
  map_add' x y := by
    apply Subtype.ext
    change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        ((x : E0) + (y : E0)) =
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (x : E0) +
        blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (y : E0)
    exact (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)).map_add (x : E0) (y : E0)
  map_smul' c x := by
    apply Subtype.ext
    change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (c • (x : E0)) =
      c • blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (x : E0)
    exact (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)).map_smul c (x : E0)

/-- Bundle a second-coordinate domain vector as an element of the ambient
operator domain. -/
noncomputable def closedOperatorCoordinateDomain1ToOriginal
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1))) :
    closedOperatorCoordinateDomain1 D →ₗ[ℂ] D.domain where
  toFun v :=
    ⟨blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (v : E1), v.property⟩
  map_add' x y := by
    apply Subtype.ext
    change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        ((x : E1) + (y : E1)) =
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (x : E1) +
        blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (y : E1)
    exact (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)).map_add (x : E1) (y : E1)
  map_smul' c x := by
    apply Subtype.ext
    change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (c • (x : E1)) =
      c • blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (x : E1)
    exact (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)).map_smul c (x : E1)

@[simp] theorem closedOperatorCoordinateDomain0ToOriginal_coe
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (u : closedOperatorCoordinateDomain0 D) :
    ((closedOperatorCoordinateDomain0ToOriginal D u : D.domain) :
        DirectSumSpace (E0 := E0) (E1 := E1)) =
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (u : E0) :=
  rfl

@[simp] theorem closedOperatorCoordinateDomain1ToOriginal_coe
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (v : closedOperatorCoordinateDomain1 D) :
    ((closedOperatorCoordinateDomain1ToOriginal D v : D.domain) :
        DirectSumSpace (E0 := E0) (E1 := E1)) =
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (v : E1) :=
  rfl

/-- The zero-graph projection keeps exactly the first coordinate. -/
theorem zeroUnboundedGraph_starProjection_apply
    (z : DirectSumSpace (E0 := E0) (E1 := E1)) :
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1)).starProjection z =
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (WithLp.fst z) := by
  simpa [unboundedBlockGraph, blockGraph] using
    (zeroGraph_starProjection_apply (𝕜 := ℂ) (E0 := E0) (E1 := E1) z)

/-- The orthogonal projection onto the second coordinate is the second
coordinate inclusion. -/
theorem zeroUnboundedGraph_orthogonalProjection_apply
    (z : DirectSumSpace (E0 := E0) (E1 := E1)) :
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))ᗮ.starProjection z =
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (WithLp.snd z) := by
  rw [Submodule.starProjection_orthogonal_apply]
  rw [zeroUnboundedGraph_starProjection_apply]
  let a := blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (WithLp.fst z)
  let b := blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (WithLp.snd z)
  change z - a = b
  have hrec : a + b = z :=
    blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ) z
  calc
    z - a = (a + b) - a := congrArg (fun w => w - a) hrec.symm
    _ = b := by abel

/-- Reduction by the first coordinate summand splits the operator domain
coordinatewise. -/
theorem mem_closedOperator_domain_iff_coordinate_domains
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (z : DirectSumSpace (E0 := E0) (E1 := E1)) :
    z ∈ D.domain ↔
      WithLp.fst z ∈ closedOperatorCoordinateDomain0 D ∧
      WithLp.snd z ∈ closedOperatorCoordinateDomain1 D := by
  constructor
  · intro hz
    let x : D.domain := ⟨z, hz⟩
    constructor
    · change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.fst z) ∈ D.domain
      have hproj := hred.1 x
      change (unboundedBlockGraph (0 : E0 →L[ℂ] E1)).starProjection z ∈ D.domain at hproj
      rw [zeroUnboundedGraph_starProjection_apply] at hproj
      exact hproj
    · change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.snd z) ∈ D.domain
      have hproj := hred.2.1 x
      change (unboundedBlockGraph (0 : E0 →L[ℂ] E1))ᗮ.starProjection z ∈ D.domain at hproj
      rw [zeroUnboundedGraph_orthogonalProjection_apply] at hproj
      exact hproj
  · rintro ⟨h0, h1⟩
    have hsum := blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ) z
    rw [← hsum]
    exact D.domain.add_mem h0 h1

/-- First coordinate of the ambient action on the first-coordinate domain. -/
noncomputable def closedOperatorCoordinateLinearMap0
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1))) :
    closedOperatorCoordinateDomain0 D →ₗ[ℂ] E0 :=
  (WithLp.fstL 2 ℂ E0 E1).toLinearMap.comp
    (D.toLinearMap.comp (closedOperatorCoordinateDomain0ToOriginal D))

/-- Second coordinate of the ambient action on the second-coordinate domain. -/
noncomputable def closedOperatorCoordinateLinearMap1
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1))) :
    closedOperatorCoordinateDomain1 D →ₗ[ℂ] E1 :=
  (WithLp.sndL 2 ℂ E0 E1).toLinearMap.comp
    (D.toLinearMap.comp (closedOperatorCoordinateDomain1ToOriginal D))

@[simp] theorem closedOperatorCoordinateLinearMap0_apply
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (u : closedOperatorCoordinateDomain0 D) :
    closedOperatorCoordinateLinearMap0 D u =
      WithLp.fst (D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u)) :=
  rfl

@[simp] theorem closedOperatorCoordinateLinearMap1_apply
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (v : closedOperatorCoordinateDomain1 D) :
    closedOperatorCoordinateLinearMap1 D v =
      WithLp.snd (D.toLinearMap (closedOperatorCoordinateDomain1ToOriginal D v)) :=
  rfl

/-- Reduction kills the second output coordinate on the first-coordinate
operator domain. -/
theorem closedOperatorCoordinate0_action_snd_eq_zero
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (u : closedOperatorCoordinateDomain0 D) :
    WithLp.snd (D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u)) = 0 := by
  have hmem0 :
      ((closedOperatorCoordinateDomain0ToOriginal D u : D.domain) :
          DirectSumSpace (E0 := E0) (E1 := E1)) ∈
        unboundedBlockGraph (0 : E0 →L[ℂ] E1) := by
    change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (u : E0) ∈
      blockGraph (0 : E0 →L[ℂ] E1)
    exact blockCoordinate0_mem_zeroGraph
      (𝕜 := ℂ) (E0 := E0) (E1 := E1) (u : E0)
  have hout := hred.2.2.1 (closedOperatorCoordinateDomain0ToOriginal D u) hmem0
  change D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u) ∈
    blockGraph (0 : E0 →L[ℂ] E1) at hout
  exact (mem_blockGraph_zero_iff_snd_eq_zero
    (𝕜 := ℂ) (E0 := E0) (E1 := E1)
    (D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u))).mp hout

/-- Reduction kills the first output coordinate on the second-coordinate
operator domain. -/
theorem closedOperatorCoordinate1_action_fst_eq_zero
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (v : closedOperatorCoordinateDomain1 D) :
    WithLp.fst (D.toLinearMap (closedOperatorCoordinateDomain1ToOriginal D v)) = 0 := by
  have hmem1 :
      ((closedOperatorCoordinateDomain1ToOriginal D v : D.domain) :
          DirectSumSpace (E0 := E0) (E1 := E1)) ∈
        (unboundedBlockGraph (0 : E0 →L[ℂ] E1))ᗮ := by
    change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) (v : E1) ∈
      (blockGraph (0 : E0 →L[ℂ] E1))ᗮ
    exact blockCoordinate1_mem_zeroGraph_orthogonal
      (𝕜 := ℂ) (E0 := E0) (E1 := E1) (v : E1)
  have hout := hred.2.2.2 (closedOperatorCoordinateDomain1ToOriginal D v) hmem1
  change D.toLinearMap (closedOperatorCoordinateDomain1ToOriginal D v) ∈
    (blockGraph (0 : E0 →L[ℂ] E1))ᗮ at hout
  exact fst_eq_zero_of_mem_zeroGraph_orthogonal
    (𝕜 := ℂ) (E0 := E0) (E1 := E1) hout

/-- On the first coordinate domain, the ambient action is exactly the first
coordinate compression embedded back into the direct sum. -/
theorem closedOperatorCoordinate0_action_eq
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (u : closedOperatorCoordinateDomain0 D) :
    D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u) =
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (closedOperatorCoordinateLinearMap0 D u) := by
  have hrec := blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ)
    (D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u))
  rw [closedOperatorCoordinate0_action_snd_eq_zero D hred u, map_zero, add_zero] at hrec
  exact hrec.symm

/-- On the second coordinate domain, the ambient action is exactly the second
coordinate compression embedded back into the direct sum. -/
theorem closedOperatorCoordinate1_action_eq
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (v : closedOperatorCoordinateDomain1 D) :
    D.toLinearMap (closedOperatorCoordinateDomain1ToOriginal D v) =
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (closedOperatorCoordinateLinearMap1 D v) := by
  have hrec := blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ)
    (D.toLinearMap (closedOperatorCoordinateDomain1ToOriginal D v))
  rw [closedOperatorCoordinate1_action_fst_eq_zero D hred v, map_zero, zero_add] at hrec
  exact hrec.symm

end DavisKahanExt
end TauCeti