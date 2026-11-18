/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Bounds

/-!
# Quadratic-form bounds under Hilbert complexification

Upper and lower real form bounds are equivalent to the corresponding bounds
on the complexified subspace. The real part of the complex quadratic form is
the sum of the forms on the two real coordinates.

Adapted from `DavisKahan/SpectralTheory/Complexification/FormTransport.lean`
(Kitware, Jon Crall and Claude Opus 5; Apache-2.0), on Tau Ceti's native carrier.
-/

public section

open TauCeti WithLp
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lower form bounds are preserved and reflected by Hilbert complexification. -/
@[simp]
theorem lowerFormBoundOn_complexifyL2_iff (A : E →L[ℝ] E) (U : Submodule ℝ E) (c : ℝ) :
    A.complexifyL2.LowerFormBoundOn U.complexifyL2 c ↔ A.LowerFormBoundOn U c := by
  rw [lowerFormBoundOn_iff, lowerFormBoundOn_iff]
  constructor
  · intro h x hx
    have hx' : toLp 2 (Complexification.ofReal x) ∈ U.complexifyL2 := by
      simpa only [Submodule.mem_complexifyL2, ofLp_toLp,
        Complexification.ofReal_re, Complexification.ofReal_im] using And.intro hx U.zero_mem
    simpa using h _ hx'
  · intro h z hz
    rw [Submodule.mem_complexifyL2] at hz
    -- The coordinate lemma uses Complex.re rather than the RCLike projection.
    change c * ‖z‖ ^ 2 ≤ (⟪A.complexifyL2 z, z⟫_ℂ).re
    rw [WithLp.complexification_norm_sq_eq, WithLp.complexification_re_inner]
    simp only [ofLp_complexifyL2_apply, complexify_apply_re, complexify_apply_im]
    -- On real scalars the RCLike real-part map is the identity.
    change ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ at h
    linarith [h _ hz.1, h _ hz.2]

/-- Upper form bounds are preserved and reflected by Hilbert complexification. -/
@[simp]
theorem upperFormBoundOn_complexifyL2_iff (A : E →L[ℝ] E) (U : Submodule ℝ E) (c : ℝ) :
    A.complexifyL2.UpperFormBoundOn U.complexifyL2 c ↔ A.UpperFormBoundOn U c := by
  rw [upperFormBoundOn_iff, upperFormBoundOn_iff]
  constructor
  · intro h x hx
    have hx' : toLp 2 (Complexification.ofReal x) ∈ U.complexifyL2 := by
      simpa only [Submodule.mem_complexifyL2, ofLp_toLp,
        Complexification.ofReal_re, Complexification.ofReal_im] using And.intro hx U.zero_mem
    simpa using h _ hx'
  · intro h z hz
    rw [Submodule.mem_complexifyL2] at hz
    -- The coordinate lemma uses Complex.re rather than the RCLike projection.
    change (⟪A.complexifyL2 z, z⟫_ℂ).re ≤ c * ‖z‖ ^ 2
    rw [WithLp.complexification_norm_sq_eq, WithLp.complexification_re_inner]
    simp only [ofLp_complexifyL2_apply, complexify_apply_re, complexify_apply_im]
    -- On real scalars the RCLike real-part map is the identity.
    change ∀ x ∈ U, ⟪A x, x⟫_ℝ ≤ c * ‖x‖ ^ 2 at h
    linarith [h _ hz.1, h _ hz.2]

end ContinuousLinearMap
