/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import Spectra.Operator.SelfAdjoint

/-!
# Closed-operator bridge to Mathlib and Spectra

The scalar-generic Davis--Kahan development currently carries a small
`ClosedOperator` wrapper.  Mathlib and Spectra use `LinearPMap` as the canonical
partial-operator representation.  This module gives lossless adapters in the
complex Hilbert-space branch so analytic work can move to the established
adjoint and self-adjoint APIs without deleting the generic wrapper.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

abbrev DKClosedOperator :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)

/-- Forget a Spectra self-adjoint operator to the scalar-generic DK closed
operator wrapper. -/
noncomputable def closedOperatorOfSpectra
    (A : Spectra.Operator.SelfAdjointOperator H) :
    DKClosedOperator (H := H) where
  domain := A.domain
  toLinearMap := A.toLinearPMap.toFun
  dense_domain := A.dense
  closed_graph := by
    have hclosed : A.toLinearPMap.IsClosed := A.selfAdjoint.isClosed
    change IsClosed (A.toLinearPMap.graph : Set (H × H)) at hclosed
    have hgraph : (A.toLinearPMap.graph : Set (H × H)) =
        Set.range (fun x : A.domain => ((x : H), A.toLinearPMap x)) := by
      ext p
      change p ∈ A.toLinearPMap.graph ↔
        ∃ x : A.domain, ((x : H), A.toLinearPMap x) = p
      rw [LinearPMap.mem_graph_iff]
      constructor
      · rintro ⟨x, hx, hAx⟩
        exact ⟨x, Prod.ext hx hAx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    rw [hgraph] at hclosed
    exact hclosed

@[simp] theorem closedOperatorOfSpectra_domain
    (A : Spectra.Operator.SelfAdjointOperator H) :
    (closedOperatorOfSpectra A).domain = A.domain := rfl

@[simp] theorem closedOperatorOfSpectra_apply
    (A : Spectra.Operator.SelfAdjointOperator H) (x : A.domain) :
    closedOperatorOfSpectra A x = A.toLinearPMap x := rfl

/-- Passing through the DK wrapper preserves the underlying Mathlib partial
linear map definitionally. -/
@[simp] theorem toLinearPMap_closedOperatorOfSpectra
    (A : Spectra.Operator.SelfAdjointOperator H) :
    (closedOperatorOfSpectra A).toLinearPMap = A.toLinearPMap := rfl

/-- Upgrade a DK closed operator to a Spectra self-adjoint operator once its
canonical Mathlib partial-linear-map view is proved self-adjoint. -/
noncomputable def closedOperatorToSpectra
    (A : DKClosedOperator (H := H))
    (hA : IsSelfAdjoint A.toLinearPMap) :
    Spectra.Operator.SelfAdjointOperator H where
  toLinearPMap := A.toLinearPMap
  selfAdjoint := hA

@[simp] theorem closedOperatorToSpectra_toLinearPMap
    (A : DKClosedOperator (H := H))
    (hA : IsSelfAdjoint A.toLinearPMap) :
    (closedOperatorToSpectra A hA).toLinearPMap = A.toLinearPMap := rfl

@[simp] theorem closedOperatorToSpectra_domain
    (A : DKClosedOperator (H := H))
    (hA : IsSelfAdjoint A.toLinearPMap) :
    (closedOperatorToSpectra A hA).domain = A.domain := rfl

/-- The upgraded operator inherits Spectra's derived symmetry law. -/
theorem closedOperatorToSpectra_symmetric
    (A : DKClosedOperator (H := H))
    (hA : IsSelfAdjoint A.toLinearPMap)
    (x y : A.domain) :
    ⟪A.toLinearMap x, (y : H)⟫_ℂ =
      ⟪(x : H), A.toLinearMap y⟫_ℂ := by
  change
    ⟪(closedOperatorToSpectra A hA).toLinearPMap x, (y : H)⟫_ℂ =
      ⟪(x : H), (closedOperatorToSpectra A hA).toLinearPMap y⟫_ℂ
  exact (closedOperatorToSpectra A hA).symmetric'
    (ψ := (x : H)) (φ := (y : H)) x.property y.property

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
