/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.RealSpectrumCyclicModel

/-!
# The intertwining law of the cyclic model on the real spectrum

The coordinate classes in `L∞` give native multiplication operators on the real
and complex models. The homeomorphism between the scalar spectra identifies the
coordinate functions, and the corresponding `L²` equivalence carries the real
multiplication operator to the complex one. This transports the cyclic
intertwining law to the real spectrum.

## Provenance

The transport and intertwining arguments were developed in DKPS by Jon Crall
and Claude Opus 5 (Kitware 2026, Apache-2.0).
-/

public section

open scoped ENNReal
open MeasureTheory

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Symbol

omit [CompleteSpace H] in
/-- The real coordinate symbol -- the inclusion of the real spectrum into `ℂ` -- is measurable,
being continuous for the subspace topology. -/
theorem measurable_realCoord : Measurable (fun x : spectrum ℝ a => ((x : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.comp continuous_subtypeVal).measurable

/-- The real coordinate has the same bound as the complex coordinate. -/
theorem norm_realCoord_le (ha : IsSelfAdjoint a) (x : spectrum ℝ a) :
    ‖((x : ℝ) : ℂ)‖ ≤
      ‖BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))‖ := by
  rw [← realSpectrumHomeomorph_symm_apply_coe ha x]
  simpa using BoundedBorelFunction.norm_coe_le_norm
    (BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)))
    ((realSpectrumHomeomorph ha).symm x)

end Symbol

section Multiplication

/-- The real coordinate, read in `ℂ`, as an essentially bounded spectral class. -/
noncomputable def realSpectrumCoordinateLp (ha : IsSelfAdjoint a) (ξ : H) :
    Lp ℂ ∞ (realSpectrumDiagMeasure ha ξ) :=
  (memLp_top_of_bound (measurable_realCoord (a := a)).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_realCoord_le ha))).toLp
    (fun x : spectrum ℝ a => ((x : ℝ) : ℂ))

/-- The real spectral coordinate represents the pointwise inclusion almost everywhere. -/
theorem coeFn_realSpectrumCoordinateLp (ha : IsSelfAdjoint a) (ξ : H) :
    (realSpectrumCoordinateLp ha ξ : spectrum ℝ a → ℂ) =ᵐ[realSpectrumDiagMeasure ha ξ]
      fun x => ((x : ℝ) : ℂ) := by
  unfold realSpectrumCoordinateLp
  exact MemLp.coeFn_toLp _

/-- The native multiplication operator for the real spectral coordinate acts pointwise. -/
theorem coeFn_realSpectrumCoordinateLp_multiplicationOperator (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    (Lp.multiplicationOperator (realSpectrumCoordinateLp ha ξ) F : spectrum ℝ a → ℂ)
      =ᵐ[realSpectrumDiagMeasure ha ξ] fun x => ((x : ℝ) : ℂ) * F x := by
  filter_upwards [Lp.multiplicationOperator_ae (realSpectrumCoordinateLp ha ξ) F,
    coeFn_realSpectrumCoordinateLp ha ξ] with x hm hx
  rw [hm, hx, smul_eq_mul]

end Multiplication

section Transport

/-- **The two coordinate multiplications agree after transport.**

The `L²` transport `realSpectrumDiagMeasureLpEquiv` conjugates multiplication by the real
coordinate on `L²` of the real-spectrum diagonal measure into multiplication by the complex
coordinate on `L²` of the diagonal measure.

This is the single new fact the real-spectrum intertwining law needs, and it is where
`realSpectrumHomeomorph` being *the real-part map on the spectrum* is used: at a point `z` of
`spectrum ℂ a` the transported multiplier is `((realSpectrumHomeomorph ha z : ℝ) : ℂ)`, which
`coe_realSpectrumHomeomorph` identifies with `(z : ℂ)` on the nose.  The only measure theory is
that an almost-everywhere identity for the pushforward pulls back along the measure-preserving
homeomorphism. -/
theorem realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumDiagMeasureLpEquiv ha ξ
        (Lp.multiplicationOperator (realSpectrumCoordinateLp ha ξ) F)
      = Lp.multiplicationOperator (spectrumCoordinateLp ha.isStarNormal ξ)
          (realSpectrumDiagMeasureLpEquiv ha ξ F) := by
  have hpull := (measurePreserving_realSpectrumHomeomorph ha ξ).quasiMeasurePreserving.ae_eq_comp
    (coeFn_realSpectrumCoordinateLp_multiplicationOperator ha ξ F)
  refine Lp.ext ?_
  filter_upwards [coeFn_realSpectrumDiagMeasureLpEquiv ha ξ
    (Lp.multiplicationOperator (realSpectrumCoordinateLp ha ξ) F), hpull,
    coeFn_spectrumCoordinateLp_multiplicationOperator ha.isStarNormal ξ
      (realSpectrumDiagMeasureLpEquiv ha ξ F),
    coeFn_realSpectrumDiagMeasureLpEquiv ha ξ F] with z h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h4
  rw [h1, h2, h3, h4, coe_realSpectrumHomeomorph ha z]

end Transport

section Intertwining

/-- **The intertwining law of the cyclic model, on the real spectrum.**

The real-spectrum cyclic isometry carries multiplication by the **real** coordinate on
`L²` of the real-spectrum diagonal measure to the action of `a` on `H`:

```text
Φ_ℝ (x · F) = a (Φ_ℝ F)   for every F in L²(spectrum ℝ a, μ_ξ).
```

With `range_realSpectrumCyclicIsometry` this says that `a`, restricted to the cyclic subspace
generated by `ξ`, *is* multiplication by the real spectral parameter -- which is the statement
a real-parameter spectral multiplicity theory is phrased against.

No density argument is re-run: the law is `cyclicIsometry_coordMulLp` composed with
`realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp`, and the latter is a pointwise identity
of multipliers. -/
theorem realSpectrumCyclicIsometry_realSpectrumCoordMulLp (ha : IsSelfAdjoint a) (ξ : H)
    (F : Lp ℂ 2 (realSpectrumDiagMeasure ha ξ)) :
    realSpectrumCyclicIsometry ha ξ (Lp.multiplicationOperator (realSpectrumCoordinateLp ha ξ) F)
      = a (realSpectrumCyclicIsometry ha ξ F) := by
  rw [realSpectrumCyclicIsometry_apply, realSpectrumCyclicIsometry_apply,
    realSpectrumDiagMeasureLpEquiv_realSpectrumCoordMulLp]
  exact cyclicIsometry_coordMulLp ha.isStarNormal ξ (realSpectrumDiagMeasureLpEquiv ha ξ F)

/-- **The intertwining law in operator form.**  The same statement as a composition of
continuous linear maps, which is the shape a consumer building a unitary equivalence
consumes. -/
theorem realSpectrumCyclicIsometry_realSpectrumCoordMulLp_comp (ha : IsSelfAdjoint a) (ξ : H) :
    (realSpectrumCyclicIsometry ha ξ).toContinuousLinearMap.comp
        (Lp.multiplicationOperator (realSpectrumCoordinateLp ha ξ))
      = a.comp (realSpectrumCyclicIsometry ha ξ).toContinuousLinearMap :=
  ContinuousLinearMap.ext (realSpectrumCyclicIsometry_realSpectrumCoordMulLp ha ξ)

/-- **The cyclic subspace is invariant under its operator**, re-derived from the real-spectrum
model alone.  This is `apply_mem_cyclicSubspace` with the real coordinate supplying the
preimage, and it is the first consumer showing the real-spectrum model is as usable as the
complex one. -/
theorem apply_mem_cyclicSubspace_of_realSpectrum (ha : IsSelfAdjoint a) (ξ : H) {y : H}
    (hy : y ∈ cyclicSubspace ha.isStarNormal ξ) : a y ∈ cyclicSubspace ha.isStarNormal ξ := by
  obtain ⟨F, rfl⟩ := exists_realSpectrumCyclicIsometry_eq ha ξ hy
  rw [← realSpectrumCyclicIsometry_realSpectrumCoordMulLp ha ξ F]
  exact realSpectrumCyclicIsometry_mem_cyclicSubspace ha ξ _

end Intertwining

end BorelCalculus
end TauCeti
