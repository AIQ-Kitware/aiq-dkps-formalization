/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedReduction

/-!
# Strong unbounded Riccati solutions from selected reducing graphs

This leaf isolates the exact handoff from spectral continuation to the
unbounded Riccati theory.  Once the selected spectral branch has been
identified as a contractive graph, preserves the diagonal operator domains,
and reduces the block core, the strong Riccati equation follows
from the graph-invariance equivalence proved in `UnboundedReduction`.

The construction of the selected branch itself remains spectral-continuation
work.  Keeping that dependency explicit prevents arbitrary block
diagonalization from being mistaken for branch selection.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Data supplied by a selected spectral branch after it has been identified
as a contractive graph over the first coordinate.  Domain preservation is a
separate field because it is not a consequence of the ambient graph equality
alone. -/
structure ContractiveReducingGraphSelectionPMap
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) where
  X : E0 →L[𝕜] E1
  preservesDomains : PreservesRiccatiPMapDomains H X
  norm_lt_one : ‖X‖ < 1
  reduces : TauCeti.LinearPMap.ReducesSubspace (unboundedBlockOperatorPMapCore H)
    (unboundedBlockGraph X)

namespace ContractiveReducingGraphSelectionPMap

/-- The selected reducing graph is invariant under the block core. -/
theorem invariant
    {H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)}
    (S : ContractiveReducingGraphSelectionPMap H) :
    TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperatorPMapCore H)
      (unboundedBlockGraph S.X) :=
  S.reduces.2.2.1

/-- A domain-compatible selected reducing graph satisfies the strong unbounded
Riccati equation. -/
theorem strongSolvesRiccati
    {H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)}
    (S : ContractiveReducingGraphSelectionPMap H) :
    StrongSolvesRiccatiPMap H S.X :=
  (unboundedBlockGraph_invariantPMapData_iff_strongRiccatiPMapCore H S.X).1
    ⟨S.preservesDomains, S.invariant⟩

/-- Package the selected graph as the contractive strong solution required by
later unbounded diagonalization. -/
theorem exists_strongRiccati_solution
    {H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)}
    (S : ContractiveReducingGraphSelectionPMap H) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccatiPMap H X ∧ ‖X‖ < 1 ∧
      TauCeti.LinearPMap.ReducesSubspace (unboundedBlockOperatorPMapCore H)
        (unboundedBlockGraph X) :=
  ⟨S.X, S.strongSolvesRiccati, S.norm_lt_one, S.reduces⟩

end ContractiveReducingGraphSelectionPMap

/-- Existential form of the continuation handoff. -/
theorem exists_strongRiccatiPMap_solution_of_selected_reducing_graph
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (hselection : Nonempty (ContractiveReducingGraphSelectionPMap H)) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccatiPMap H X ∧ ‖X‖ < 1 ∧
      TauCeti.LinearPMap.ReducesSubspace (unboundedBlockOperatorPMapCore H)
        (unboundedBlockGraph X) := by
  obtain ⟨S⟩ := hselection
  exact S.exists_strongRiccati_solution

end DavisKahanExt
end TauCeti
