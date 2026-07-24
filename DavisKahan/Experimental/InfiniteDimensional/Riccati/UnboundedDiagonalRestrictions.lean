/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.UnboundedCoordinateRestrictions

/-!
# Closed coordinate restrictions of a reduced unbounded direct-sum operator

A closed operator reducing the first coordinate summand induces densely defined
closed operators on both coordinates.  Their closed direct sum has the same
operator domain and action as the original reduced operator.  The final result
is stated as an identity-unitary equivalence so that both directions of domain
transport remain explicit.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

private theorem closedOperatorCoordinateDomain0_dense
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    Dense ((closedOperatorCoordinateDomain0 D : Submodule ℂ E0) : Set E0) := by
  rw [dense_iff_closure_eq]
  ext u
  simp only [Set.mem_univ, iff_true]
  have hu0 :
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u ∈
        closure (D.domain : Set (DirectSumSpace (E0 := E0) (E1 := E1))) := by
    rw [D.dense_domain.closure_eq]
    trivial
  obtain ⟨s, hs, hs_lim⟩ := mem_closure_iff_seq_limit.mp hu0
  refine mem_closure_iff_seq_limit.mpr
    ⟨fun n => WithLp.fst (s n), ?_, ?_⟩
  · intro n
    change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.fst (s n)) ∈ D.domain
    let x : D.domain := ⟨s n, hs n⟩
    have hx := hred.1 x
    change (unboundedBlockGraph (0 : E0 →L[ℂ] E1)).starProjection
        (s n) ∈ D.domain at hx
    rw [zeroUnboundedGraph_starProjection_apply] at hx
    exact hx
  · have hlim :=
      ((WithLp.fstL 2 ℂ E0 E1).continuous.tendsto
        (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u)).comp hs_lim
    change Filter.Tendsto (fun n => WithLp.fst (s n)) Filter.atTop
      (nhds (WithLp.fst
        (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) u))) at hlim
    simpa using hlim

private theorem closedOperatorCoordinateDomain1_dense
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    Dense ((closedOperatorCoordinateDomain1 D : Submodule ℂ E1) : Set E1) := by
  rw [dense_iff_closure_eq]
  ext v
  simp only [Set.mem_univ, iff_true]
  have hv1 :
      blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v ∈
        closure (D.domain : Set (DirectSumSpace (E0 := E0) (E1 := E1))) := by
    rw [D.dense_domain.closure_eq]
    trivial
  obtain ⟨s, hs, hs_lim⟩ := mem_closure_iff_seq_limit.mp hv1
  refine mem_closure_iff_seq_limit.mpr
    ⟨fun n => WithLp.snd (s n), ?_, ?_⟩
  · intro n
    change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
        (WithLp.snd (s n)) ∈ D.domain
    let x : D.domain := ⟨s n, hs n⟩
    have hx := hred.2.1 x
    change (unboundedBlockGraph (0 : E0 →L[ℂ] E1))ᗮ.starProjection
        (s n) ∈ D.domain at hx
    rw [zeroUnboundedGraph_orthogonalProjection_apply] at hx
    exact hx
  · have hlim :=
      ((WithLp.sndL 2 ℂ E0 E1).continuous.tendsto
        (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v)).comp hs_lim
    change Filter.Tendsto (fun n => WithLp.snd (s n)) Filter.atTop
      (nhds (WithLp.snd
        (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) v))) at hlim
    simpa using hlim

private theorem closedOperatorCoordinateLinearMap0_closedGraph
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    IsClosed (Set.range fun u : closedOperatorCoordinateDomain0 D =>
      ((u : E0), closedOperatorCoordinateLinearMap0 D u)) := by
  let coords : E0 × E0 →
      DirectSumSpace (E0 := E0) (E1 := E1) ×
        DirectSumSpace (E0 := E0) (E1 := E1) :=
    fun p =>
      (blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1,
       blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2)
  have hcoords : Continuous coords := by
    fun_prop
  rw [show Set.range (fun u : closedOperatorCoordinateDomain0 D =>
      ((u : E0), closedOperatorCoordinateLinearMap0 D u)) =
      coords ⁻¹' (Set.range fun x : D.domain =>
        (((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)),
          D.toLinearMap x)) by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨closedOperatorCoordinateDomain0ToOriginal D u, ?_⟩
      apply Prod.ext
      · rfl
      · exact closedOperatorCoordinate0_action_eq D hred u
    · rintro ⟨x, hx⟩
      have hfst :
          ((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)) =
            blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 :=
        congrArg Prod.fst hx
      have hsnd :
          D.toLinearMap x =
            blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2 :=
        congrArg Prod.snd hx
      have hp1 : p.1 ∈ closedOperatorCoordinateDomain0 D := by
        change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 ∈ D.domain
        rw [← hfst]
        exact x.property
      let u : closedOperatorCoordinateDomain0 D := ⟨p.1, hp1⟩
      have hux : closedOperatorCoordinateDomain0ToOriginal D u = x := by
        apply Subtype.ext
        exact hfst.symm
      refine ⟨u, Prod.ext rfl ?_⟩
      have hact := closedOperatorCoordinate0_action_eq D hred u
      rw [hux, hsnd] at hact
      have hcoord := congrArg WithLp.fst hact
      simpa using hcoord.symm]
  exact D.closed_graph.preimage hcoords

private theorem closedOperatorCoordinateLinearMap1_closedGraph
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    IsClosed (Set.range fun v : closedOperatorCoordinateDomain1 D =>
      ((v : E1), closedOperatorCoordinateLinearMap1 D v)) := by
  let coords : E1 × E1 →
      DirectSumSpace (E0 := E0) (E1 := E1) ×
        DirectSumSpace (E0 := E0) (E1 := E1) :=
    fun p =>
      (blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1,
       blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2)
  have hcoords : Continuous coords := by
    fun_prop
  rw [show Set.range (fun v : closedOperatorCoordinateDomain1 D =>
      ((v : E1), closedOperatorCoordinateLinearMap1 D v)) =
      coords ⁻¹' (Set.range fun x : D.domain =>
        (((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)),
          D.toLinearMap x)) by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨closedOperatorCoordinateDomain1ToOriginal D v, ?_⟩
      apply Prod.ext
      · rfl
      · exact closedOperatorCoordinate1_action_eq D hred v
    · rintro ⟨x, hx⟩
      have hfst :
          ((x : D.domain) : DirectSumSpace (E0 := E0) (E1 := E1)) =
            blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 :=
        congrArg Prod.fst hx
      have hsnd :
          D.toLinearMap x =
            blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.2 :=
        congrArg Prod.snd hx
      have hp1 : p.1 ∈ closedOperatorCoordinateDomain1 D := by
        change blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1) p.1 ∈ D.domain
        rw [← hfst]
        exact x.property
      let v : closedOperatorCoordinateDomain1 D := ⟨p.1, hp1⟩
      have hvx : closedOperatorCoordinateDomain1ToOriginal D v = x := by
        apply Subtype.ext
        exact hfst.symm
      refine ⟨v, Prod.ext rfl ?_⟩
      have hact := closedOperatorCoordinate1_action_eq D hred v
      rw [hvx, hsnd] at hact
      have hcoord := congrArg WithLp.snd hact
      simpa using hcoord.symm]
  exact D.closed_graph.preimage hcoords

/-- The closed first-coordinate restriction of a reduced direct-sum operator. -/
noncomputable def closedOperatorCoordinateRestriction0
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    ClosedOperator (𝕜 := ℂ) (E := E0) where
  domain := closedOperatorCoordinateDomain0 D
  toLinearMap := closedOperatorCoordinateLinearMap0 D
  dense_domain := closedOperatorCoordinateDomain0_dense D hred
  closed_graph := closedOperatorCoordinateLinearMap0_closedGraph D hred

/-- The closed second-coordinate restriction of a reduced direct-sum operator. -/
noncomputable def closedOperatorCoordinateRestriction1
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    ClosedOperator (𝕜 := ℂ) (E := E1) where
  domain := closedOperatorCoordinateDomain1 D
  toLinearMap := closedOperatorCoordinateLinearMap1 D
  dense_domain := closedOperatorCoordinateDomain1_dense D hred
  closed_graph := closedOperatorCoordinateLinearMap1_closedGraph D hred

@[simp] theorem closedOperatorCoordinateRestriction0_domain
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    (closedOperatorCoordinateRestriction0 D hred).domain =
      closedOperatorCoordinateDomain0 D := rfl

@[simp] theorem closedOperatorCoordinateRestriction1_domain
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    (closedOperatorCoordinateRestriction1 D hred).domain =
      closedOperatorCoordinateDomain1 D := rfl

/-- The explicit closed direct sum of the two coordinate restrictions. -/
noncomputable def closedOperatorReducedCoordinateDirectSum
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)) :=
  closedOperatorDirectSum
    (closedOperatorCoordinateRestriction0 D hred)
    (closedOperatorCoordinateRestriction1 D hred)

@[simp] theorem mem_closedOperatorReducedCoordinateDirectSum_domain_iff
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (z : DirectSumSpace (E0 := E0) (E1 := E1)) :
    z ∈ (closedOperatorReducedCoordinateDirectSum D hred).domain ↔
      z ∈ D.domain := by
  change z ∈ (closedOperatorDirectSum
      (closedOperatorCoordinateRestriction0 D hred)
      (closedOperatorCoordinateRestriction1 D hred)).domain ↔ z ∈ D.domain
  rw [mem_closedOperatorDirectSum_domain_iff]
  change (WithLp.fst z ∈ closedOperatorCoordinateDomain0 D ∧
      WithLp.snd z ∈ closedOperatorCoordinateDomain1 D) ↔ z ∈ D.domain
  exact (mem_closedOperator_domain_iff_coordinate_domains D hred z).symm

/-- The explicit coordinate direct sum has exactly the same action as the
original reduced operator after transporting the common domain witness. -/
theorem closedOperatorReducedCoordinateDirectSum_action
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)))
    (z : (closedOperatorReducedCoordinateDirectSum D hred).domain) :
    (closedOperatorReducedCoordinateDirectSum D hred).toLinearMap z =
      D.toLinearMap
        ⟨(z : DirectSumSpace (E0 := E0) (E1 := E1)),
          (mem_closedOperatorReducedCoordinateDirectSum_domain_iff D hred z).mp
            z.property⟩ := by
  let A0 := closedOperatorCoordinateRestriction0 D hred
  let A1 := closedOperatorCoordinateRestriction1 D hred
  let u : closedOperatorCoordinateDomain0 D :=
    closedOperatorDirectSumDomainFst A0 A1 z
  let v : closedOperatorCoordinateDomain1 D :=
    closedOperatorDirectSumDomainSnd A0 A1 z
  let zD : D.domain :=
    ⟨(z : DirectSumSpace (E0 := E0) (E1 := E1)),
      (mem_closedOperatorReducedCoordinateDirectSum_domain_iff D hred z).mp
        z.property⟩
  have hzsplit : zD =
      closedOperatorCoordinateDomain0ToOriginal D u +
        closedOperatorCoordinateDomain1ToOriginal D v := by
    apply Subtype.ext
    exact (blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ)
      (z : DirectSumSpace (E0 := E0) (E1 := E1))).symm
  have hDsplit : D.toLinearMap zD =
      blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
          (closedOperatorCoordinateLinearMap0 D u) +
        blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
          (closedOperatorCoordinateLinearMap1 D v) := by
    calc
      D.toLinearMap zD = D.toLinearMap
          (closedOperatorCoordinateDomain0ToOriginal D u +
            closedOperatorCoordinateDomain1ToOriginal D v) :=
        congrArg D.toLinearMap hzsplit
      _ = D.toLinearMap (closedOperatorCoordinateDomain0ToOriginal D u) +
          D.toLinearMap (closedOperatorCoordinateDomain1ToOriginal D v) := by
        rw [map_add]
      _ = _ := by
        rw [closedOperatorCoordinate0_action_eq D hred u,
          closedOperatorCoordinate1_action_eq D hred v]
  have hsum := blockCoordinate0_add_blockCoordinate1 (𝕜 := ℂ)
    ((closedOperatorReducedCoordinateDirectSum D hred).toLinearMap z)
  change blockCoordinate0 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
      (closedOperatorCoordinateLinearMap0 D u) +
    blockCoordinate1 (𝕜 := ℂ) (E0 := E0) (E1 := E1)
      (closedOperatorCoordinateLinearMap1 D v) =
    (closedOperatorReducedCoordinateDirectSum D hred).toLinearMap z at hsum
  exact hsum.symm.trans hDsplit.symm

/-- The coordinate direct sum and the original reduced operator are equivalent
through the identity, with both domain directions and actions explicit. -/
theorem closedOperatorReducedCoordinateDirectSum_unitaryEquivalent
    (D : ClosedOperator (𝕜 := ℂ) (E := DirectSumSpace (E0 := E0) (E1 := E1)))
    (hred : D.ReducesSubspace
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))) :
    ClosedOperator.UnitaryEquivalent
      (closedOperatorReducedCoordinateDirectSum D hred) D
      (ContinuousLinearMap.id ℂ _)
      (ContinuousLinearMap.id ℂ _) := by
  have hid : IsUnitaryOperator
      (ContinuousLinearMap.id ℂ (DirectSumSpace (E0 := E0) (E1 := E1))) := by
    constructor
    · intro x
      rfl
    · intro y
      exact ⟨y, rfl⟩
  refine ⟨hid, hid, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · let hWdom : ∀ x : (closedOperatorReducedCoordinateDirectSum D hred).domain,
        (ContinuousLinearMap.id ℂ _) (x : DirectSumSpace (E0 := E0) (E1 := E1)) ∈
          D.domain := fun x =>
      (mem_closedOperatorReducedCoordinateDirectSum_domain_iff D hred x).mp
        x.property
    refine ⟨hWdom, ?_⟩
    let hWinvdom : ∀ y : D.domain,
        (ContinuousLinearMap.id ℂ _) (y : DirectSumSpace (E0 := E0) (E1 := E1)) ∈
          (closedOperatorReducedCoordinateDirectSum D hred).domain := fun y =>
      (mem_closedOperatorReducedCoordinateDirectSum_domain_iff D hred y).mpr
        y.property
    refine ⟨hWinvdom, ?_, ?_⟩
    · intro x
      change D.toLinearMap
          ⟨(x : DirectSumSpace (E0 := E0) (E1 := E1)), hWdom x⟩ =
        (closedOperatorReducedCoordinateDirectSum D hred).toLinearMap x
      exact (closedOperatorReducedCoordinateDirectSum_action D hred x).symm
    · intro y
      change (closedOperatorReducedCoordinateDirectSum D hred).toLinearMap
          ⟨(y : DirectSumSpace (E0 := E0) (E1 := E1)), hWinvdom y⟩ =
        D.toLinearMap y
      have h := closedOperatorReducedCoordinateDirectSum_action D hred
        ⟨(y : DirectSumSpace (E0 := E0) (E1 := E1)), hWinvdom y⟩
      simpa using h

/-- The two closed diagonal restrictions of the graph-rotated unbounded block
operator. -/
noncomputable def unboundedBlockDiagonalRestriction0
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ClosedOperator (𝕜 := ℂ) (E := E0) :=
  closedOperatorCoordinateRestriction0
    (unboundedBlockDiagonalOperatorCore H X)
    (unboundedBlockDiagonalOperatorCore_reduces_zeroGraph H X hred)

/-- The second closed diagonal restriction of the graph-rotated unbounded block
operator. -/
noncomputable def unboundedBlockDiagonalRestriction1
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ClosedOperator (𝕜 := ℂ) (E := E1) :=
  closedOperatorCoordinateRestriction1
    (unboundedBlockDiagonalOperatorCore H X)
    (unboundedBlockDiagonalOperatorCore_reduces_zeroGraph H X hred)

/-- The graph-rotated block operator is exactly represented, up to identity
transport of the common domain, by the closed direct sum of its two coordinate
restrictions. -/
theorem unboundedBlockDiagonalOperatorCore_coordinateDirectSum
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ClosedOperator.UnitaryEquivalent
      (closedOperatorDirectSum
        (unboundedBlockDiagonalRestriction0 H X hred)
        (unboundedBlockDiagonalRestriction1 H X hred))
      (unboundedBlockDiagonalOperatorCore H X)
      (ContinuousLinearMap.id ℂ _)
      (ContinuousLinearMap.id ℂ _) := by
  exact closedOperatorReducedCoordinateDirectSum_unitaryEquivalent
    (unboundedBlockDiagonalOperatorCore H X)
    (unboundedBlockDiagonalOperatorCore_reduces_zeroGraph H X hred)

end DavisKahanExt
end TauCeti