/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedExistence
import DavisKahan.Experimental.InfiniteDimensional.Riccati.UnboundedDiagonalRestrictions

/-!
# Proof-complete public surface for unbounded Riccati reduction

This module aggregates the proof-complete unbounded Riccati leaves.  It keeps
spectral branch selection explicit: a selected contractive reducing graph is
converted to a strong solution by `UnboundedExistence`, while the construction
of that selected graph remains continuation work.

For complex Hilbert spaces, the canonical graph rotation transports the
coordinate-diagonal pullback to the original block operator.  The orientation
below follows that map: the forward unitary carries the zero coordinate graph
to the Riccati graph.  The two closed coordinate restrictions are exposed as a
separate identity-unitary equivalence with the rotated pullback.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Canonical proof-complete closed block operator on the explicit product
operator domain. -/
noncomputable abbrev constructedUnboundedBlockOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) :=
  unboundedBlockOperatorCore H

/-- Canonical proof-complete block core over raw partial-map data. -/
noncomputable abbrev constructedUnboundedBlockOperatorPMap
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →ₗ.[𝕜] WithLp 2 (E0 × E1) :=
  unboundedBlockOperatorPMapCore H

/-- Raw public aggregate form of the domain-controlled graph-invariance
characterization. -/
theorem constructedUnboundedBlockGraphPMap_invariant_iff_strongRiccati
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiPMapDomains H X ∧
      TauCeti.LinearPMap.InvariantSubspace
        (constructedUnboundedBlockOperatorPMap H)
        (unboundedBlockGraph X)) ↔
      StrongSolvesRiccatiPMap H X := by
  exact unboundedBlockGraph_invariantPMapData_iff_strongRiccatiPMapCore H X

/-- The raw continuation handoff exposed from the aggregate module. -/
theorem constructedStrongRiccatiPMapSolution_of_selectedGraph
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (hselection : Nonempty (ContractiveReducingGraphSelectionPMap H)) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccatiPMap H X ∧ ‖X‖ < 1 ∧
      TauCeti.LinearPMap.ReducesSubspace
        (constructedUnboundedBlockOperatorPMap H)
        (unboundedBlockGraph X) := by
  exact exists_strongRiccatiPMap_solution_of_selected_reducing_graph H hselection

/-- Public aggregate form of the domain-controlled graph-invariance
characterization. -/
theorem constructedUnboundedBlockGraph_invariant_iff_strongRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      (constructedUnboundedBlockOperator H).InvariantSubspace
        (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  exact unboundedBlockGraph_invariant_iff_strongRiccatiCore H X

/-- The continuation handoff, exposed from the aggregate module: once the
selected branch is supplied as a contractive reducing graph, the complete
strong Riccati package follows. -/
theorem constructedStrongRiccatiSolution_of_selectedGraph
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (hselection : Nonempty (ContractiveReducingGraphSelection H)) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccati H X ∧ ‖X‖ < 1 ∧
      (constructedUnboundedBlockOperator H).ReducesSubspace
        (unboundedBlockGraph X) := by
  exact exists_strongRiccati_solution_of_selected_reducing_graph H hselection

section Complex

variable {F0 : Type*} [NormedAddCommGroup F0] [InnerProductSpace ℂ F0]
  [CompleteSpace F0]
variable {F1 : Type*} [NormedAddCommGroup F1] [InnerProductSpace ℂ F1]
  [CompleteSpace F1]

/-- Raw complex graph-rotation diagonalization.  The coordinate-restriction
direct-sum statement below remains a closed-output compatibility endpoint;
this theorem is the canonical partial-map transport result consumed before
such closed coordinate packages are requested. -/
theorem complex_unbounded_blockDiagonalizationPMap
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    (X : F0 →L[ℂ] F1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorPMapCore H) (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (F0 × F1) →L[ℂ] WithLp 2 (F0 × F1),
      TauCeti.LinearPMap.UnitaryEquivalent
        (unboundedBlockDiagonalPMapCore H X)
        (unboundedBlockOperatorPMapCore H) W Winv ∧
      W ∘L projection (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) =
        projection (unboundedBlockGraph X) ∘L W ∧
      TauCeti.LinearPMap.ReducesSubspace
        (unboundedBlockDiagonalPMapCore H X)
        (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) := by
  let W := (unboundedGraphRotationEquiv X).toContinuousLinearMap
  let Winv := (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap
  refine ⟨W, Winv, ?_, ?_, ?_⟩
  · exact unboundedBlockDiagonalPMapCore_unitaryEquivalent H X
  · exact unboundedGraphRotationEquiv_intertwines_projection X
  · exact unboundedBlockDiagonalPMapCore_reduces_zeroGraph H X hred

/-- The complex coordinate-diagonal representative obtained by pulling the
full block operator back through the canonical graph rotation. -/
noncomputable abbrev complexUnboundedBlockDiagonalOperator
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    (X : F0 →L[ℂ] F1) :
    ClosedOperator (𝕜 := ℂ) (E := WithLp 2 (F0 × F1)) :=
  unboundedBlockDiagonalOperatorCore H X

/-- Full domain-controlled complex block diagonalization.

The forward unitary maps the coordinate-diagonal pullback to the original
block operator and carries the zero graph to the Riccati graph.  The last
conjunct identifies the pullback with the closed direct sum of its two
coordinate restrictions. -/
theorem complex_unbounded_blockDiagonalization
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    (X : F0 →L[ℂ] F1)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (F0 × F1) →L[ℂ] WithLp 2 (F0 × F1),
      ClosedOperator.UnitaryEquivalent
        (complexUnboundedBlockDiagonalOperator H X)
        (unboundedBlockOperatorCore H) W Winv ∧
      W ∘L projection (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) =
        projection (unboundedBlockGraph X) ∘L W ∧
      ClosedOperator.UnitaryEquivalent
        (closedOperatorDirectSum
          (unboundedBlockDiagonalRestriction0 H X hred)
          (unboundedBlockDiagonalRestriction1 H X hred))
        (complexUnboundedBlockDiagonalOperator H X)
        (ContinuousLinearMap.id ℂ _)
        (ContinuousLinearMap.id ℂ _) := by
  let W := (unboundedGraphRotationEquiv X).toContinuousLinearMap
  let Winv := (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap
  refine ⟨W, Winv, ?_, ?_, ?_⟩
  · exact unboundedBlockDiagonalOperatorCore_unitaryEquivalent H X
  · exact unboundedGraphRotationEquiv_intertwines_projection X
  · exact unboundedBlockDiagonalOperatorCore_coordinateDirectSum H X hred

/-- Strong-solution form of the complex diagonalization theorem.  Reduction is
kept as a separate hypothesis because one-sided graph invariance alone does not
supply the orthogonal-complement domain decomposition. -/
theorem complex_unbounded_blockDiagonalization_of_strongSolution
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    {X : F0 →L[ℂ] F1} (_hX : StrongSolvesRiccati H X)
    (hred : (unboundedBlockOperatorCore H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (F0 × F1) →L[ℂ] WithLp 2 (F0 × F1),
      ClosedOperator.UnitaryEquivalent
        (complexUnboundedBlockDiagonalOperator H X)
        (unboundedBlockOperatorCore H) W Winv ∧
      W ∘L projection (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) =
        projection (unboundedBlockGraph X) ∘L W ∧
      ClosedOperator.UnitaryEquivalent
        (closedOperatorDirectSum
          (unboundedBlockDiagonalRestriction0 H X hred)
          (unboundedBlockDiagonalRestriction1 H X hred))
        (complexUnboundedBlockDiagonalOperator H X)
        (ContinuousLinearMap.id ℂ _)
        (ContinuousLinearMap.id ℂ _) :=
  complex_unbounded_blockDiagonalization H X hred

end Complex

end DavisKahanExt
end TauCeti
