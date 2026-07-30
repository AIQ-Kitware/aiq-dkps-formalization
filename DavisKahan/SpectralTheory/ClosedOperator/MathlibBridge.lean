/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic

/-!
# Closed-operator bridge to Mathlib and Spectra

The scalar-generic Davis--Kahan development currently carries a small
`ClosedOperator` wrapper.  Mathlib and Spectra use `LinearPMap` as the canonical
partial-operator representation.  This module gives lossless adapters in the
complex Hilbert-space branch so analytic work can move to the established
adjoint and self-adjoint APIs without deleting the generic wrapper.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Local shorthand for the DKPS closed-operator bundle. -/
abbrev DKClosedOperator :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)

/-- Package a self-adjoint partial map as a DK closed operator.

Until 2026-07-29 this file carried a pair of adapters to and from Spectra's
`Operator.SelfAdjointOperator`; the only remaining consumer of the outbound
adapter is `DavisKahan.SpectralTheory.OrderedHalfLine`, which now carries its
own copy, so this module — imported by most of the bridge — is Spectra-free. -/
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

/-- The closed operator built from a self-adjoint partial map has that map as its underlying `LinearPMap`. -/
@[simp] theorem closedOperatorOfSelfAdjointPMap_toLinearPMap {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : K →ₗ.[ℂ] K) (hT : IsSelfAdjoint T) :
    (closedOperatorOfSelfAdjointPMap T hT).toLinearPMap = T := rfl

/-- Its domain is the partial map's domain. -/
@[simp] theorem closedOperatorOfSelfAdjointPMap_domain {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : K →ₗ.[ℂ] K) (hT : IsSelfAdjoint T) :
    (closedOperatorOfSelfAdjointPMap T hT).domain = T.domain := rfl

end Experimental
end DavisKahan
end TauCeti