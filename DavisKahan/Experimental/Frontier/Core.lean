/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Interop.Spectra.HalmosTwoProjections
import DavisKahan.Interop.Spectra.SpectralRestriction
-- supplies `compressOperator`
import DavisKahan.Sylvester.GenuineSpectrum
import ForMathlib.Analysis.Normed.Operator.ApproximationNumber
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Experimental frontier interfaces for the remaining Davis--Kahan 1970 proof

This module isolates reusable signatures needed by several uncompleted source
results.  The declarations deliberately live under `Experimental.Frontier` and
are not imported by the supported library target.

The purpose is to make the remaining dependency graph explicit.  Each
interface is intended to be replaced by a concrete construction or theorem,
not treated as a permanent hypothesis in the source-facing API.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier

open SpectraBridge

universe u v

section UnitaryGeometry

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A bounded operator is a paper-style direct rotation when it is unitary,
intertwines the two orthogonal projections, has nonnegative diagonal
compressions, and has skew-adjoint crossed blocks. -/
structure IsPaperDirectRotation
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (T : H →L[ℂ] H) : Prop where
  unitary_mem : T ∈ unitary (H →L[ℂ] H)
  intertwines : T * projection U = projection V * T
  source_compression_nonnegative :
    ∀ x : H, 0 ≤ RCLike.re
      ⟪x, (projection U * T * projection U) x⟫_ℂ
  complement_compression_nonnegative :
    ∀ x : H, 0 ≤ RCLike.re
      ⟪x, (complementaryProjection U * T * complementaryProjection U) x⟫_ℂ
  crossed_blocks :
    complementaryProjection U * T * projection U =
      -star (projection U * T * complementaryProjection U)

/-- The source and target crossed intersections admit a unitary
identification.  This is the constructive form of equality of their Hilbert
space dimensions. -/
def CrossedDefectsEquivalent
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : Prop :=
  Nonempty
    (halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V)

/-- Restriction of the Halmos cosine square to the reducing generic summand,
realized as the compression to the generic part.  The generic part reduces
both projections, hence every word in them, so the compression is the honest
restriction. -/
noncomputable def genericHalmosCosineSq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  DavisKahanExt.compressOperator (halmosGenericPart U V) (halmosCosineSq U V)

/-- Restriction of the Halmos sine square to the reducing generic summand. -/
noncomputable def genericHalmosSineSq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  DavisKahanExt.compressOperator (halmosGenericPart U V) (halmosSineSq U V)

/-- The restricted generic cosine and sine squares retain the Pythagorean
identity. -/
theorem genericHalmosCosineSq_add_sineSq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    genericHalmosCosineSq U V + genericHalmosSineSq U V = 1 := by
  ext x
  have hsum : halmosCosineSq U V (x : H) + halmosSineSq U V (x : H) =
      (x : H) := by
    have h := congrArg
      (fun T : H →L[ℂ] H => T (x : H)) (halmosCosineSq_add_sineSq U V)
    simpa using h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    genericHalmosCosineSq, genericHalmosSineSq, DavisKahanExt.compressOperator,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  simp only [Submodule.coe_add, Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← map_add, hsum, Submodule.starProjection_eq_self_iff.mpr x.2]

end UnitaryGeometry

section CrossSpaceClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]

/-- Unitary equivalence of two ordered pairs of subspaces.

Stated as existential quantification over the unitary rather than as a
`Prop`-valued structure carrying it: the intended notion is a proposition, and
a `Prop` structure cannot hold the datum `H₁ ≃ₗᵢ[ℂ] H₂`. -/
def PairOfSubspacesUnitaryEquivalent
    (U₁ V₁ : Submodule ℂ H₁) (U₂ V₂ : Submodule ℂ H₂) : Prop :=
  ∃ e : H₁ ≃ₗᵢ[ℂ] H₂,
    U₁.map e.toLinearMap = U₂ ∧ V₁.map e.toLinearMap = V₂

/-- Unitary equivalence of bounded operators acting on possibly different
Hilbert spaces.

The intertwining is stated pointwise.  Writing it as a composition of
continuous linear maps forces `e` through `LinearMap.toContinuousLinearMap`,
which carries a `FiniteDimensional` hypothesis that the source statement does
not have. -/
def BoundedOperatorsUnitaryEquivalent
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : Prop :=
  ∃ e : H₁ ≃ₗᵢ[ℂ] H₂, ∀ x : H₁, e (A x) = B (e x)

/-- Abstract equality of spectral multiplicity data.  A concrete definition
must encode the measure class and the cardinal-valued multiplicity function,
not merely point-spectrum multiplicities. -/
noncomputable def SameSpectralMultiplicity
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : Prop := by
  sorry

/-- Spectral multiplicity data classify self-adjoint bounded operators up to
unitary equivalence.  This is the missing spectral-theorem bridge in the
paper's formulation of Theorem 3.1. -/
theorem sameSpectralMultiplicity_iff_unitarilyEquivalent
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    SameSpectralMultiplicity A B ↔
      BoundedOperatorsUnitaryEquivalent A B := by
  sorry

end CrossSpaceClassification

section CircleRieszInterface

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A circle separates a chosen measurable subset of the real spectrum of a
self-adjoint closed operator. -/
structure CircleSeparatesRealSpectrum
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : Set ℝ) (center radius : ℝ) : Prop where
  radius_pos : 0 < radius
  contour_resolvent :
    ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      z ∉ spectrum ℂ A
  inside_iff_mem :
    ∀ x : ℝ, (x : ℂ) ∈ spectrum ℂ A →
      (‖(x : ℂ) - (center : ℂ)‖ < radius ↔ x ∈ B)

/-- Circle-integral Riesz projection for a bounded operator, through Mathlib's
circle integral: `(2 π i)⁻¹ ∮_{|z-c|=r} (z - A)⁻¹ dz`, with the resolvent
taken through the total `Ring.inverse` so the definition needs no separation
hypothesis. -/
noncomputable def circleRieszProjection
    (A : H →L[ℂ] H) (center radius : ℝ) : H →L[ℂ] H :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∮ z in C((center : ℂ), radius),
      Ring.inverse (z • (1 : H →L[ℂ] H) - A)

end CircleRieszInterface

end Frontier
end Experimental
end DavisKahan
end ForMathlib
