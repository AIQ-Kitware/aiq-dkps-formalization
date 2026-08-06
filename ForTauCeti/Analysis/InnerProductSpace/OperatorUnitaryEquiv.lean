/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Unitary equivalence of bounded operators

Two bounded operators on possibly different complex Hilbert spaces are **unitarily equivalent**
when some linear isometric equivalence intertwines them.

The relation is already spelled out at several places in the Davis--Kahan development; it is
introduced here so that the *chain* of equivalences produced by the multiplicity construction --
operator, cyclic model, slice model, normal form -- can be composed by `trans` instead of by
hand.  The definition is literally the same existential as
`TauCeti.DavisKahan.Experimental.Frontier.BoundedOperatorsUnitaryEquivalent`, so the two unfold
to each other.

The intertwining is stated **pointwise**.  Writing it as a composition of continuous linear maps
would force the equivalence through `LinearMap.toContinuousLinearMap`, which carries a
finite-dimensionality hypothesis that none of the source statements have.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

namespace TauCeti

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L]

/-- **Unitary equivalence of bounded operators** on possibly different complex Hilbert spaces.

Exposed, because consumers outside this module need to see that it is the same existential as
the Davis--Kahan development's own `BoundedOperatorsUnitaryEquivalent`. -/
@[expose]
def OperatorUnitaryEquiv (A : H →L[ℂ] H) (B : K →L[ℂ] K) : Prop :=
  ∃ e : H ≃ₗᵢ[ℂ] K, ∀ x : H, e (A x) = B (e x)

/-- A linear isometric equivalence that intertwines two operators exhibits their unitary
equivalence.  This is the introduction rule; it exists so that call sites never write the
anonymous constructor and can be read at a glance. -/
theorem operatorUnitaryEquiv_of_intertwines {A : H →L[ℂ] H} {B : K →L[ℂ] K} (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x : H, e (A x) = B (e x)) : OperatorUnitaryEquiv A B :=
  ⟨e, he⟩

/-- Unitary equivalence is reflexive, witnessed by the identity. -/
@[refl]
theorem OperatorUnitaryEquiv.refl (A : H →L[ℂ] H) : OperatorUnitaryEquiv A A :=
  ⟨LinearIsometryEquiv.refl ℂ H, fun _ => rfl⟩

/-- Unitary equivalence is symmetric: the inverse of the intertwining unitary intertwines the
operators the other way. -/
@[symm]
theorem OperatorUnitaryEquiv.symm {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (h : OperatorUnitaryEquiv A B) : OperatorUnitaryEquiv B A := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun y => ?_⟩
  have hy := he (e.symm y)
  rw [e.apply_symm_apply] at hy
  rw [← hy, e.symm_apply_apply]

/-- Unitary equivalence is transitive.  This is what lets the chain of equivalences produced by
the multiplicity construction be composed one step at a time. -/
theorem OperatorUnitaryEquiv.trans {A : H →L[ℂ] H} {B : K →L[ℂ] K} {C : L →L[ℂ] L}
    (h : OperatorUnitaryEquiv A B) (h' : OperatorUnitaryEquiv B C) :
    OperatorUnitaryEquiv A C := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e.trans e', fun x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  rw [he x, he' (e x)]

end TauCeti
