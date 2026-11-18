/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Orthogonal projections under Hilbert complexification

Complexification preserves orthogonal complements, orthogonal projections and
the projection gap of real subspaces. No ambient completeness is needed.

Adapted from `DavisKahan/SpectralTheory/Complexification/Subspace.lean`
(Kitware, Jon Crall and Claude Opus 5; Apache-2.0), replacing its product
carrier by the native `WithLp 2 (TauCeti.Complexification E)`.
-/

public section

open TauCeti WithLp
open scoped InnerProductSpace

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hilbert complexification commutes with orthogonal complementation. -/
@[simp]
theorem complexifyL2_orthogonal (U : Submodule ℝ E) :
    Uᗮ.complexifyL2 = U.complexifyL2ᗮ := by
  ext z
  constructor
  · intro hz
    rw [mem_complexifyL2] at hz
    rw [mem_orthogonal]
    intro w hw
    rw [mem_complexifyL2] at hw
    -- Expose the two coordinate formulas for the native complex inner product.
    apply Complex.ext
    · change ⟪w.ofLp.re, z.ofLp.re⟫_ℝ + ⟪w.ofLp.im, z.ofLp.im⟫_ℝ = 0
      simp [inner_right_of_mem_orthogonal hw.1 hz.1,
        inner_right_of_mem_orthogonal hw.2 hz.2]
    · change ⟪w.ofLp.re, z.ofLp.im⟫_ℝ - ⟪w.ofLp.im, z.ofLp.re⟫_ℝ = 0
      simp [inner_right_of_mem_orthogonal hw.1 hz.2,
        inner_right_of_mem_orthogonal hw.2 hz.1]
  · intro hz
    have h (u : E) (hu : u ∈ U) :
        ⟪toLp 2 (Complexification.ofReal u), z⟫_ℂ = 0 :=
      hz _ (by simpa only [mem_complexifyL2, ofLp_toLp,
        Complexification.ofReal_re, Complexification.ofReal_im] using And.intro hu U.zero_mem)
    rw [mem_complexifyL2]
    constructor
    · rw [mem_orthogonal]
      intro u hu
      simpa using congrArg Complex.re (h u hu)
    · rw [mem_orthogonal]
      intro u hu
      simpa using congrArg Complex.im (h u hu)

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

/-- The complexified projection takes values in the complexified subspace. -/
theorem complexifyL2_starProjection_mem (z : WithLp 2 (Complexification E)) :
    U.starProjection.complexifyL2 z ∈ U.complexifyL2 := by
  rw [mem_complexifyL2]
  simpa only [ContinuousLinearMap.ofLp_complexifyL2_apply,
    ContinuousLinearMap.complexify_apply_re, ContinuousLinearMap.complexify_apply_im] using
    And.intro (U.starProjection_apply_mem z.ofLp.re) (U.starProjection_apply_mem z.ofLp.im)

/-- The residual from the complexified projection is orthogonal to its range. -/
theorem sub_complexifyL2_starProjection_mem_orthogonal
    (z : WithLp 2 (Complexification E)) :
    z - U.starProjection.complexifyL2 z ∈ U.complexifyL2ᗮ := by
  rw [← complexifyL2_orthogonal, mem_complexifyL2]
  simp

/-- An orthogonally complemented real subspace remains complemented after complexification. -/
instance instHasOrthogonalProjectionComplexifyL2 : U.complexifyL2.HasOrthogonalProjection where
  exists_orthogonal z := ⟨_, U.complexifyL2_starProjection_mem z,
    U.sub_complexifyL2_starProjection_mem_orthogonal z⟩

/-- Orthogonal projection commutes with Hilbert complexification. -/
@[simp]
theorem starProjection_complexifyL2 :
    U.complexifyL2.starProjection = U.starProjection.complexifyL2 := by
  ext z
  exact U.complexifyL2.eq_starProjection_of_mem_orthogonal
    (U.complexifyL2_starProjection_mem z)
    (U.sub_complexifyL2_starProjection_mem_orthogonal z)

/-- Hilbert complexification preserves the gap between two orthogonally complemented subspaces. -/
@[simp]
theorem projectionGap_complexifyL2 (V : Submodule ℝ E) [V.HasOrthogonalProjection] :
    U.complexifyL2.projectionGap V.complexifyL2 = U.projectionGap V := by
  have hsub : (U.starProjection - V.starProjection).complexifyL2 =
      U.starProjection.complexifyL2 - V.starProjection.complexifyL2 :=
    by simpa only [LinearIsometry.coe_toLinearMap,
      ContinuousLinearMap.complexifyL2ₗᵢ_apply] using
      map_sub (ContinuousLinearMap.complexifyL2ₗᵢ E E).toLinearMap
        U.starProjection V.starProjection
  rw [projectionGap_def, projectionGap_def, starProjection_complexifyL2,
    starProjection_complexifyL2, ← hsub, ContinuousLinearMap.norm_complexifyL2]

end Submodule
