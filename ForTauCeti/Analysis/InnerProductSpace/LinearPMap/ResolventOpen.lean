/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventBound
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The resolvent set is open, and the spectrum is closed

Mathlib has this for bounded operators (`spectrum.isOpen_resolventSet`); for a
`LinearPMap` it has to be proved, and the proof is the usual Neumann-series
perturbation, run through `resolvent_unique` so that no second inverse has to be
identified by hand.

## Why it is needed

Measurability.  Every consumer that wants to feed a spectral set to a
projection-valued measure — `specProjection hA (Complex.ofReal ⁻¹' spectrum A)`,
and in particular the Rosenblum argument, which needs a *measurable* set
separating two disjoint spectra — needs the spectrum to be a Borel set first,
and closedness is how that is obtained.

## The perturbation

For `z₀ ∈ ρ(A)` write `R₀ = (A - z₀)⁻¹` and, for `z` near `z₀`,
`V = 1 - (z - z₀) • R₀`, invertible as soon as `‖z - z₀‖ ‖R₀‖ < 1`.  Then

* `(A - z) (R₀ ψ) = V ψ` for every `ψ`, and
* `R₀ ((A - z) x) = V x` for every `x ∈ dom A`,

so `R₀ ∘ V⁻¹` is a two-sided inverse of `A - z`.  Both identities are one line
from `sub_smul_resolvent` / `resolvent_apply_sub_smul` after splitting
`A - z = (A - z₀) - (z - z₀)`, and `V` commutes with `R₀` because it is a
polynomial in it, which is what lets the same operator serve on both sides.

## Provenance

* **Original repository:** none — **authored in place** in the AIQ DKPS
  formalization (`https://github.com/AIQ-Kitware/aiq-dkps-formalization`),
  commit `9be75beb`, for staging into Tau Ceti.
* **Original module:** none; written directly at this path.
* **Original authors / copyright / licence:** Copyright (c) 2026 Kitware, Inc.;
  `Authors: Jon Crall, Claude Opus 5`; Apache 2.0 (this repository's `LICENSE`).
  No third-party code is incorporated, so no donor notice is carried.
* **Extraction class:** *authored in place*, for upstreaming to Tau Ceti.
* **Relation to existing libraries:** Mathlib proves the bounded analogue,
  `spectrum.isOpen_resolventSet`. This module is the `LinearPMap` statement,
  which Mathlib does not have; the argument is the usual Neumann-series
  perturbation, routed through `resolvent_unique` so that no second inverse has
  to be identified by hand. Spectra did not influence the selection or the proof.
* **Semantic differences from a donor:** not applicable.
-/

@[expose] public section

open scoped Topology

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

section Perturbation

variable {A : E →ₗ.[𝕜] E} {z₀ : 𝕜} (hz₀ : z₀ ∈ resolventSet A)

/-- The Neumann factor `V = 1 - (z - z₀) • R₀`. -/
noncomputable def neumannFactor (z : 𝕜) : E →L[𝕜] E :=
  1 - (z - z₀) • resolvent A hz₀

omit [CompleteSpace E] in
/-- The Neumann factor acts as the geometric series `∑ ((z - w) R(z))ⁿ`. -/
@[simp]
theorem neumannFactor_apply (z : 𝕜) (ψ : E) :
    neumannFactor hz₀ z ψ = ψ - (z - z₀) • resolvent A hz₀ ψ := by
  simp [neumannFactor]

omit [CompleteSpace E] in
/-- Shifting the spectral parameter turns the resolvent into the Neumann
factor: `(A - z) (R₀ ψ) = V ψ`. -/
theorem sub_smul_resolvent_shift (z : 𝕜) (ψ : E) :
    A ⟨resolvent A hz₀ ψ, resolvent_mem_domain hz₀ ψ⟩ - z • resolvent A hz₀ ψ
      = neumannFactor hz₀ z ψ := by
  have h := sub_smul_resolvent hz₀ ψ
  rw [neumannFactor_apply]
  linear_combination (norm := module) h

omit [CompleteSpace E] in
/-- The same shift on the other side: `R₀ ((A - z) x) = V x`. -/
theorem resolvent_sub_smul_shift (z : 𝕜) (x : A.domain) :
    resolvent A hz₀ (A x - z • (x : E)) = neumannFactor hz₀ z (x : E) := by
  have h := resolvent_apply_sub_smul hz₀ x
  rw [neumannFactor_apply,
    show A x - z • (x : E) = (A x - z₀ • (x : E)) - (z - z₀) • (x : E) by module,
    map_sub, h, map_smul]

omit [CompleteSpace E] in
/-- The resolvent commutes with its own Neumann factor, which is what lets the perturbed resolvent
be written as a product in either order. -/
theorem commute_resolvent_neumannFactor (z : 𝕜) :
    Commute (resolvent A hz₀) (neumannFactor hz₀ z) := by
  rw [neumannFactor]
  exact ((Commute.one_right _).sub_right ((Commute.refl _).smul_right _))

end Perturbation

/-- **The resolvent set is open.** -/
theorem isOpen_resolventSet (A : E →ₗ.[𝕜] E) : IsOpen (resolventSet A) := by
  rw [Metric.isOpen_iff]
  intro z₀ hz₀
  set R₀ := resolvent A hz₀ with hR₀
  refine ⟨(‖R₀‖ + 1)⁻¹, by positivity, fun z hz => ?_⟩
  have hlt : ‖(z - z₀) • R₀‖ < 1 := by
    rw [norm_smul]
    have hd : ‖z - z₀‖ < (‖R₀‖ + 1)⁻¹ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hR : (0 : ℝ) ≤ ‖R₀‖ := norm_nonneg _
    have hden : (0 : ℝ) < ‖R₀‖ + 1 := by linarith
    calc ‖z - z₀‖ * ‖R₀‖ ≤ ‖z - z₀‖ * (‖R₀‖ + 1) := by nlinarith [norm_nonneg (z - z₀)]
      _ < (‖R₀‖ + 1)⁻¹ * (‖R₀‖ + 1) := by
          exact mul_lt_mul_of_pos_right hd hden
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hden)
  set V : (E →L[𝕜] E)ˣ := Units.oneSub ((z - z₀) • R₀) hlt with hV
  have hVval : (V : E →L[𝕜] E) = neumannFactor hz₀ z := rfl
  have hcomm : Commute R₀ (V : E →L[𝕜] E) := by
    rw [hVval]; exact commute_resolvent_neumannFactor hz₀ z
  have hcomm' : Commute R₀ (↑V⁻¹ : E →L[𝕜] E) := hcomm.units_inv_right
  refine ⟨R₀ ∘L (↑V⁻¹ : E →L[𝕜] E), fun ψ => ?_, fun φ => ?_⟩
  · -- left inverse on the domain
    have hshift := resolvent_sub_smul_shift hz₀ z ψ
    change R₀ ((↑V⁻¹ : E →L[𝕜] E) (A ψ - z • (ψ : E))) = (ψ : E)
    have hswap : R₀ ((↑V⁻¹ : E →L[𝕜] E) (A ψ - z • (ψ : E)))
        = (↑V⁻¹ : E →L[𝕜] E) (R₀ (A ψ - z • (ψ : E))) := by
      have := hcomm'
      simpa [ContinuousLinearMap.mul_def] using
        congrArg (fun T : E →L[𝕜] E => T (A ψ - z • (ψ : E))) this
    rw [hswap, hshift, ← hVval]
    exact congrArg (fun T : E →L[𝕜] E => T (ψ : E)) V.inv_mul
  · -- right inverse everywhere, landing in the domain
    refine ⟨resolvent_mem_domain hz₀ _, ?_⟩
    change A ⟨R₀ ((↑V⁻¹ : E →L[𝕜] E) φ), _⟩ - z • R₀ ((↑V⁻¹ : E →L[𝕜] E) φ) = φ
    rw [sub_smul_resolvent_shift hz₀ z, ← hVval]
    exact congrArg (fun T : E →L[𝕜] E => T φ) V.mul_inv

/-- **The spectrum is closed.** -/
theorem isClosed_spectrum (A : E →ₗ.[𝕜] E) : IsClosed (spectrum A) := by
  rw [spectrum, isClosed_compl_iff]
  exact isOpen_resolventSet A

section RealPoints

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The real points of the spectrum form a closed, hence measurable, subset of
`ℝ` — the form every spectral-measure consumer needs. -/
theorem isClosed_realSpectrum (A : F →ₗ.[ℂ] F) :
    IsClosed (Complex.ofReal ⁻¹' spectrum A) :=
  (isClosed_spectrum A).preimage Complex.continuous_ofReal

/-- The real spectrum is measurable, being closed.  This is the enabling fact for defining spectral
measures on it; Mathlib has the open-resolvent-set statement only for bounded operators. -/
theorem measurableSet_realSpectrum (A : F →ₗ.[ℂ] F) :
    MeasurableSet (Complex.ofReal ⁻¹' spectrum A) :=
  (isClosed_realSpectrum A).measurableSet

end RealPoints

end LinearPMap
end TauCeti
