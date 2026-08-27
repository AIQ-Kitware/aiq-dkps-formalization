/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Sol
-/

import DavisKahan.Specialized.FreeBeam.BeamFormSpaceScalar

/-!
# The real free-beam form model

This file is the explicit real-scalar instantiation of the scalar-generic concrete free-beam
form construction.  Davis--Kahan Section 9 uses the real Hilbert space `L²(0,1)`, so these
names provide the source-facing real model without duplicating the analytic proof.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real

noncomputable section

abbrev BeamL2 : Type := Scalar.BeamL2 (𝕜 := ℝ)
abbrev BeamPairSpace : Type := Scalar.BeamPairSpace (𝕜 := ℝ)
abbrev BeamV : Type := Scalar.BeamV (𝕜 := ℝ)

abbrev pairFst : BeamPairSpace →L[ℝ] BeamL2 := Scalar.pairFst (𝕜 := ℝ)
abbrev pairSnd : BeamPairSpace →L[ℝ] BeamL2 := Scalar.pairSnd (𝕜 := ℝ)
abbrev beamFormSubmodule : Submodule ℝ BeamPairSpace := Scalar.beamFormSubmodule (𝕜 := ℝ)

abbrev beamEmbed : BeamV →L[ℝ] BeamL2 := Scalar.beamEmbed (𝕜 := ℝ)
abbrev beamSnd : BeamV →L[ℝ] BeamL2 := Scalar.beamSnd (𝕜 := ℝ)

abbrev contToLp := Scalar.contToLp (𝕜 := ℝ)
abbrev beamOneLp : BeamL2 := Scalar.beamOneLp (𝕜 := ℝ)
abbrev beamIdLp : BeamL2 := Scalar.beamIdLp (𝕜 := ℝ)

abbrev beamCoerciveFormData := Scalar.beamCoerciveFormData (𝕜 := ℝ)
abbrev beamShiftedFormData := Scalar.beamShiftedFormData (𝕜 := ℝ)

theorem mem_beamFormSubmodule_iff (p : BeamPairSpace) :
    p ∈ beamFormSubmodule ↔
      ∀ k : ℕ,
        ∫ t, (pairFst p : ℝ → ℝ) t * intervalBumpD2 k t ∂unitIocMeasure =
          ∫ t, (pairSnd p : ℝ → ℝ) t * intervalBump k t ∂unitIocMeasure :=
  Scalar.mem_beamFormSubmodule_iff (𝕜 := ℝ) p

theorem beamV_repr (p : BeamV) :
    ∃ a b : ℝ, (beamEmbed p : ℝ → ℝ) =ᵐ[unitIocMeasure]
      fun t => a + b * t + secondPrimitive ((beamSnd p : ℝ → ℝ)) t :=
  Scalar.beamV_repr (𝕜 := ℝ) p

theorem contPair_mem {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x)
    (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ BeamL2 BeamL2).symm
      (contToLp f hf, contToLp f2 hf2) ∈ beamFormSubmodule :=
  Scalar.contPair_mem (𝕜 := ℝ) hf hf1 hf2 hd hd1

theorem coeFn_contToLp (g : ℝ → ℝ) (hg : Continuous g) :
    (contToLp g hg : ℝ → ℝ) =ᵐ[unitIocMeasure] g :=
  Scalar.coeFn_contToLp (𝕜 := ℝ) g hg

theorem coeFn_beamOneLp :
    (beamOneLp : ℝ → ℝ) =ᵐ[unitIocMeasure] fun _ => 1 :=
  Scalar.coeFn_beamOneLp (𝕜 := ℝ)

theorem coeFn_beamIdLp :
    (beamIdLp : ℝ → ℝ) =ᵐ[unitIocMeasure] fun t => t :=
  Scalar.coeFn_beamIdLp (𝕜 := ℝ)

/-- The real `L²(0,1]` free-beam operator represented by the shifted bending form. -/
abbrev beamOperator : DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := BeamL2) :=
  Scalar.beamOperator (𝕜 := ℝ)

/-- The real free-beam realization is self-adjoint. -/
theorem beamOperator_isSelfAdjoint : beamOperator.IsSelfAdjoint :=
  Scalar.beamOperator_isSelfAdjoint (𝕜 := ℝ)

/-- The real free-beam realization is nonnegative. -/
theorem beamOperator_nonneg (x : beamOperator.domain) :
    0 ≤ RCLike.re ⟪beamOperator.toLinearMap x, (x : BeamL2)⟫_ℝ :=
  Scalar.beamOperator_nonneg (𝕜 := ℝ) x

/-- The real form-domain embedding is compact. -/
theorem isCompactOperator_beamEmbed : IsCompactOperator beamEmbed :=
  Scalar.isCompactOperator_beamEmbed (𝕜 := ℝ)

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
