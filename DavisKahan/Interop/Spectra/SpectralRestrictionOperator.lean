/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import DavisKahan.Interop.Spectra.SpectralRestriction
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.YosidaApproximation

/-!
# Self-adjoint operators on spectral ranges

For a self-adjoint operator `A` and a measurable spectral set `B`, this file
packages the restriction of `A` to the range of `E_A(B)` as a self-adjoint DK
closed operator, whose subtype inclusion maps the restricted domain into
`A.domain` and intertwines the two operators.

## Provenance

Until 2026-07-28 this went through `vendor/Spectra`'s Stone theory: the unitary
group `genToGroup hA` was restricted to the spectral range (which required
`spectralCalculus_group_comm` to see that the projection commutes with the
group), and the restricted operator was recovered as the *Stone generator* of
the restricted group, self-adjoint by
`Spectra.Resolvent.generator_isSelfAdjoint`.  Identifying it with `A` on the
range then needed `generator_genToGroup`, i.e. the hard direction of Stone's
theorem.

None of that is necessary.  The restriction is definable directly — domain
`{x ∈ ran E_A(B) | x ∈ dom A}`, action `x ↦ A x` — and is self-adjoint by the
`(· ± i)`-surjectivity criterion, because the resolvent preserves the spectral
range (it commutes with the projection: both are images of the same Borel
calculus of the Cayley transform).  See
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean`,
`specRestrict` and `isSelfAdjoint_specRestrict`.  The declarations this module
exports downstream are unchanged; the group-theoretic scaffolding that
supported them is gone.
-/

open scoped InnerProductSpace
open Filter Topology

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Package a self-adjoint partial map as a DK closed operator. -/
noncomputable def closedOperatorOfSelfAdjointPMap {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : K →ₗ.[ℂ] K) (hT : IsSelfAdjoint T) : DKClosedOperator (H := K) where
  domain := T.domain
  toLinearMap := T.toFun
  dense_domain := hT.dense_domain
  closed_graph := by
    have hclosed : T.IsClosed := hT.isClosed
    change IsClosed (T.graph : Set (K × K)) at hclosed
    have hgraph : (T.graph : Set (K × K)) =
        Set.range (fun x : T.domain => ((x : K), T x)) := by
      ext p
      change p ∈ T.graph ↔ ∃ x : T.domain, ((x : K), T x) = p
      rw [LinearPMap.mem_graph_iff]
      constructor
      · rintro ⟨x, hx, hAx⟩
        exact ⟨x, Prod.ext hx hAx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    rw [hgraph] at hclosed
    exact hclosed

@[simp] theorem closedOperatorOfSelfAdjointPMap_toLinearPMap {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : K →ₗ.[ℂ] K) (hT : IsSelfAdjoint T) :
    (closedOperatorOfSelfAdjointPMap T hT).toLinearPMap = T := rfl

/-- The restriction of a self-adjoint operator to one of its spectral ranges,
as a DK closed operator. -/
noncomputable def selfAdjointSpectralRestriction
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    DKClosedOperator (H := selfAdjointSpectralSubspace A hA B hB) :=
  closedOperatorOfSelfAdjointPMap
    (TauCeti.LinearPMap.specRestrict hA B hB)
    (TauCeti.LinearPMap.isSelfAdjoint_specRestrict hA B hB)

/-- The spectral restriction is self-adjoint. -/
theorem selfAdjointSpectralRestriction_isSelfAdjoint
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (selfAdjointSpectralRestriction A hA B hB).IsSelfAdjoint :=
  TauCeti.LinearPMap.isSelfAdjoint_specRestrict hA B hB

/-- The spectral-range inclusion maps the restricted operator domain into the
ambient operator domain. -/
theorem selfAdjointSpectralRestriction_inclusion_mem_domain
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    (x : (selfAdjointSpectralRestriction A hA B hB).domain) :
    selfAdjointSpectralSubspaceInclusion A hA B hB
        (x : selfAdjointSpectralSubspace A hA B hB) ∈ A.domain :=
  x.2

/-- The spectral-range inclusion intertwines the restricted closed operator
with the ambient self-adjoint operator. -/
theorem selfAdjointSpectralRestriction_inclusion_intertwines
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B)
    (x : (selfAdjointSpectralRestriction A hA B hB).domain) :
    A.toLinearMap
        ⟨selfAdjointSpectralSubspaceInclusion A hA B hB
            (x : selfAdjointSpectralSubspace A hA B hB),
          selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB x⟩ =
      selfAdjointSpectralSubspaceInclusion A hA B hB
        ((selfAdjointSpectralRestriction A hA B hB).toLinearMap x) :=
  rfl

/-- The one-parameter unitary group generated by the spectral restriction. -/
noncomputable def selfAdjointSpectralSubspaceUnitaryGroup
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (B : Set ℝ) (hB : MeasurableSet B) :
    TauCeti.OneParameterUnitaryGroup (selfAdjointSpectralSubspace A hA B hB) :=
  TauCeti.LinearPMap.genToGroup
    (TauCeti.LinearPMap.isSelfAdjoint_specRestrict hA B hB)

end SpectraBridge
end Experimental
end DavisKahan
end TauCeti
