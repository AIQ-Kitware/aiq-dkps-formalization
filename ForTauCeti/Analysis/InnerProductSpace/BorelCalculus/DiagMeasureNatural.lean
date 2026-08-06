/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# The functional calculus is natural under a unitary intertwiner

If a unitary `e` intertwines two normal operators, `e (a x) = b (e x)`, then it intertwines their
whole continuous functional calculi:

```text
e (f(a) x) = f(b) (e x)   for every `f` continuous on the spectrum.
```

Mathlib supplies both moving parts, which is what makes this short:

* `LinearIsometryEquiv.conjStarAlgEquiv` turns the unitary into a `⋆`-algebra equivalence of the
  two endomorphism algebras, and the intertwining hypothesis says exactly that it sends `a` to
  `b`.
* `StarAlgHomClass.map_cfc` says `⋆`-algebra homomorphisms commute with the continuous functional
  calculus.

## Why it is here

This is the first step of the open **uniqueness** half of the multiplicity classification: it is
what will make the *measure class* of a multiplicity datum an invariant of the operator rather
than of the presentation.  The remaining step of that argument -- that the scalar spectral
measures therefore agree, i.e.

```text
(diagMeasure hb (e ξ)).map (↑) = (diagMeasure ha ξ).map (↑)
```

as measures on `ℂ`, both sides pushed forward because the two live on the *spectrum subtypes* of
`a` and of `b`, which are equal as sets but different types -- is plumbing on top of this
theorem: `diagMeasure` is characterised by `∫ f d(diagMeasure ha ξ) = ⟪ξ, f(a) ξ⟫` on continuous
symbols, a unitary preserves inner products, and a finite Borel measure on `ℂ` is determined by
the integrals of bounded continuous real functions
(`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`).

## Main results

* `TauCeti.BorelCalculus.conjStarAlgEquiv_eq_of_intertwines`: intertwining, as an equation
  between `⋆`-algebra images.
* `TauCeti.BorelCalculus.isStarNormal_of_intertwines`: normality transports.
* `TauCeti.BorelCalculus.cfc_apply_of_intertwines`: **the naturality theorem.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {a : H →L[ℂ] H} {b : K →L[ℂ] K}

/-- **The intertwining hypothesis, as an equation between `⋆`-algebra images.**  A unitary
intertwines `a` and `b` exactly when the induced `⋆`-algebra equivalence of the endomorphism
algebras sends `a` to `b`. -/
theorem conjStarAlgEquiv_eq_of_intertwines (e : H ≃ₗᵢ[ℂ] K) (he : ∀ x, e (a x) = b (e x)) :
    e.conjStarAlgEquiv a = b := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, he, LinearIsometryEquiv.apply_symm_apply]

/-- A unitarily conjugate of a normal operator is normal. -/
theorem isStarNormal_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) : IsStarNormal b := by
  rw [← conjStarAlgEquiv_eq_of_intertwines e he]
  refine ⟨?_⟩
  rw [← map_star]
  exact (ha.star_comm_self).map e.conjStarAlgEquiv

/-- **The continuous functional calculus is natural under a unitary intertwiner.** -/
theorem cfc_apply_of_intertwines (ha : IsStarNormal a) (e : H ≃ₗᵢ[ℂ] K)
    (he : ∀ x, e (a x) = b (e x)) {f : ℂ → ℂ} (hf : ContinuousOn f (spectrum ℂ a)) (x : H) :
    e (cfc f a x) = cfc f b (e x) := by
  haveI hb : IsStarNormal b := isStarNormal_of_intertwines ha e he
  have hrw : (e.conjStarAlgEquiv : (H →L[ℂ] H) → (K →L[ℂ] K))
      = fun x => ((e : H →L[ℂ] K) ∘L x) ∘L (e.symm : K →L[ℂ] H) :=
    funext fun x => LinearIsometryEquiv.conjStarAlgEquiv_apply e x
  have hφ : Continuous (e.conjStarAlgEquiv : (H →L[ℂ] H) → (K →L[ℂ] K)) := by
    rw [hrw]
    fun_prop
  have hmap := StarAlgHomClass.map_cfc (R := ℂ) (S := ℂ) e.conjStarAlgEquiv f a hf hφ ha
    (by rw [conjStarAlgEquiv_eq_of_intertwines e he]; exact hb)
  rw [conjStarAlgEquiv_eq_of_intertwines e he] at hmap
  have h2 := congrArg (fun T : K →L[ℂ] K => T (e x)) hmap
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] at h2
  exact h2

end BorelCalculus
end TauCeti
