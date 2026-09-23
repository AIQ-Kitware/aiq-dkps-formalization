/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, GPT-5.6 Sol
-/

import DavisKahan.Specialized.FreeBeam.BeamFormSpaceScalar

open TauCeti.DavisKahan.Sylvester

/-!
# The complex free-beam form model

This file is the complex specialization of the scalar-generic construction in
`BeamFormSpaceScalar`. It intentionally contains only compatibility aliases and
thin theorem wrappers: the analytic implementation and proofs have one owner,
the scalar-generic module. `BeamFormSpaceReal` follows the same pattern for `ℝ`.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

noncomputable section

/-- The complex `L²(0,1]` of the free-beam model. -/
abbrev BeamL2 : Type := Scalar.BeamL2 (𝕜 := ℂ)

/-- The complex pair space carrying a function and its second derivative. -/
abbrev BeamPairSpace : Type := Scalar.BeamPairSpace (𝕜 := ℂ)

/-- First coordinate of a pair. -/
abbrev pairFst : BeamPairSpace →L[ℂ] BeamL2 := Scalar.pairFst (𝕜 := ℂ)

/-- Second coordinate of a pair. -/
abbrev pairSnd : BeamPairSpace →L[ℂ] BeamL2 := Scalar.pairSnd (𝕜 := ℂ)

@[simp] theorem pairFst_apply (p : BeamPairSpace) :
    pairFst p = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 p).1 :=
  Scalar.pairFst_apply (𝕜 := ℂ) p

@[simp] theorem pairSnd_apply (p : BeamPairSpace) :
    pairSnd p = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 p).2 :=
  Scalar.pairSnd_apply (𝕜 := ℂ) p

/-- Sup bound used by the pairing functional. -/
abbrev pairingBound (g : ℝ → ℂ) (hg : Continuous g) : ℝ :=
  Scalar.pairingBound (𝕜 := ℂ) g hg

theorem pairingBound_spec (g : ℝ → ℂ) (hg : Continuous g) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ pairingBound g hg :=
  Scalar.pairingBound_spec (𝕜 := ℂ) g hg

theorem pairingBound_nonneg (g : ℝ → ℂ) (hg : Continuous g) : 0 ≤ pairingBound g hg :=
  Scalar.pairingBound_nonneg (𝕜 := ℂ) g hg

/-- Integration against a continuous weight. -/
abbrev pairingCLM (g : ℝ → ℂ) (hg : Continuous g) : BeamL2 →L[ℂ] ℂ :=
  Scalar.pairingCLM (𝕜 := ℂ) g hg

@[simp] theorem pairingCLM_apply (g : ℝ → ℂ) (hg : Continuous g) (W : BeamL2) :
    pairingCLM g hg W = ∫ t, (W : ℝ → ℂ) t * g t ∂unitIocMeasure :=
  Scalar.pairingCLM_apply (𝕜 := ℂ) g hg W

/-- Complex lift of the second bump derivative. -/
abbrev bumpD2C (k : ℕ) (t : ℝ) : ℂ := Scalar.bumpD2Scalar (𝕜 := ℂ) k t

/-- Complex lift of the interval bump. -/
abbrev bumpC (k : ℕ) (t : ℝ) : ℂ := Scalar.bumpScalar (𝕜 := ℂ) k t

theorem continuous_bumpD2C (k : ℕ) : Continuous (bumpD2C k) :=
  Scalar.continuous_bumpD2Scalar (𝕜 := ℂ) k

theorem continuous_bumpC (k : ℕ) : Continuous (bumpC k) :=
  Scalar.continuous_bumpScalar (𝕜 := ℂ) k

/-- The `k`-th weak-second-derivative constraint. -/
abbrev constraintCLM (k : ℕ) : BeamPairSpace →L[ℂ] ℂ :=
  Scalar.constraintCLM (𝕜 := ℂ) k

/-- The form domain as a submodule of the pair space. -/
abbrev beamFormSubmodule : Submodule ℂ BeamPairSpace :=
  Scalar.beamFormSubmodule (𝕜 := ℂ)

theorem mem_beamFormSubmodule_iff (p : BeamPairSpace) :
    p ∈ beamFormSubmodule ↔ ∀ k : ℕ,
      ∫ t, (pairFst p : ℝ → ℂ) t * bumpD2C k t ∂unitIocMeasure
        = ∫ t, (pairSnd p : ℝ → ℂ) t * bumpC k t ∂unitIocMeasure :=
  Scalar.mem_beamFormSubmodule_iff (𝕜 := ℂ) p

theorem isClosed_beamFormSubmodule :
    IsClosed (beamFormSubmodule : Set BeamPairSpace) :=
  Scalar.isClosed_beamFormSubmodule (𝕜 := ℂ)

/-- The complex free-beam form space. -/
abbrev BeamV : Type := Scalar.BeamV (𝕜 := ℂ)

/-- Inclusion of the form domain into the ambient `L²`. -/
abbrev beamEmbed : BeamV →L[ℂ] BeamL2 := Scalar.beamEmbed (𝕜 := ℂ)

/-- The second-derivative slot of the form domain. -/
abbrev beamSnd : BeamV →L[ℂ] BeamL2 := Scalar.beamSnd (𝕜 := ℂ)

@[simp] theorem beamEmbed_apply (p : BeamV) : beamEmbed p = pairFst (p : BeamPairSpace) :=
  Scalar.beamEmbed_apply (𝕜 := ℂ) p

@[simp] theorem beamSnd_apply (p : BeamV) : beamSnd p = pairSnd (p : BeamPairSpace) :=
  Scalar.beamSnd_apply (𝕜 := ℂ) p

theorem beamV_weak (p : BeamV) (k : ℕ) :
    ∫ t, (beamEmbed p : ℝ → ℂ) t * (intervalBumpD2 k t : ℂ) ∂unitIocMeasure
      = ∫ t, (beamSnd p : ℝ → ℂ) t * (intervalBump k t : ℂ) ∂unitIocMeasure :=
  Scalar.beamV_weak (𝕜 := ℂ) p k

theorem beamV_repr (p : BeamV) :
    ∃ a b : ℂ, (beamEmbed p : ℝ → ℂ) =ᵐ[unitIocMeasure]
      fun t => a + b * (t : ℂ) + secondPrimitive ((beamSnd p : ℝ → ℂ)) t :=
  Scalar.beamV_repr (𝕜 := ℂ) p

theorem beamEmbed_injective : Function.Injective beamEmbed :=
  Scalar.beamEmbed_injective (𝕜 := ℂ)

/-- Continuous functions embedded into the ambient `L²`. -/
abbrev contToLp (g : ℝ → ℂ) (hg : Continuous g) : BeamL2 :=
  Scalar.contToLp (𝕜 := ℂ) g hg

theorem coeFn_contToLp (g : ℝ → ℂ) (hg : Continuous g) :
    (contToLp g hg : ℝ → ℂ) =ᵐ[unitIocMeasure] g :=
  Scalar.coeFn_contToLp (𝕜 := ℂ) g hg

theorem integral_mul_intervalBumpD2_eq_of_hasDerivAt {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x) (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, f t * intervalBumpD2 k t
      = ∫ t in (0 : ℝ)..1, f2 t * intervalBump k t :=
  Scalar.integral_mul_intervalBumpD2_eq_of_hasDerivAt hf hf1 hf2 hd hd1 k

theorem contPair_mem {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x) (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) :
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
        (contToLp (fun t => (f t : ℂ)) (by fun_prop),
          contToLp (fun t => (f2 t : ℂ)) (by fun_prop)))
      ∈ beamFormSubmodule :=
  Scalar.contPair_mem (𝕜 := ℂ) hf hf1 hf2 hd hd1

theorem contToLp_polynomial_mem_range (q : Polynomial ℝ) :
    contToLp (fun t => ((q.eval t : ℝ) : ℂ)) (by fun_prop)
      ∈ LinearMap.range (beamEmbed : BeamV →ₗ[ℂ] BeamL2) :=
  Scalar.contToLp_polynomial_mem_range (𝕜 := ℂ) q

theorem denseRange_beamEmbed : DenseRange beamEmbed :=
  Scalar.denseRange_beamEmbed (𝕜 := ℂ)

theorem beamEmbed_adjoint_injective :
    Function.Injective (ContinuousLinearMap.adjoint beamEmbed) :=
  Scalar.beamEmbed_adjoint_injective (𝕜 := ℂ)

/-- Coercive bending form data for the complex model. -/
abbrev beamCoerciveFormData :
    Abstract.CoerciveFormData (𝕜 := ℂ) (H := BeamL2) (V := BeamV) :=
  Scalar.beamCoerciveFormData (𝕜 := ℂ)

theorem beamV_re_inner_self (u : BeamV) :
    RCLike.re ⟪u, u⟫_ℂ = ‖beamEmbed u‖ ^ 2 + ‖beamSnd u‖ ^ 2 :=
  Scalar.beamV_re_inner_self (𝕜 := ℂ) u

/-- Shifted free-beam form data for the complex model. -/
abbrev beamShiftedFormData :
    Analytic.ShiftedBeamFormData (𝕜 := ℂ) (H := BeamL2) (V := BeamV) :=
  Scalar.beamShiftedFormData (𝕜 := ℂ)

/-- The complex free-beam operator represented by the shifted bending form. -/
abbrev beamOperator : BeamL2 →ₗ.[ℂ] BeamL2 := Scalar.beamOperator (𝕜 := ℂ)

theorem beamOperator_isSelfAdjoint : IsSelfAdjoint beamOperator :=
  Scalar.beamOperator_isSelfAdjoint (𝕜 := ℂ)

theorem beamOperator_nonneg (x : beamOperator.domain) :
    0 ≤ RCLike.re ⟪beamOperator x, (x : BeamL2)⟫_ℂ :=
  Scalar.beamOperator_nonneg (𝕜 := ℂ) x

/-- The constant function `1` in the ambient `L²`. -/
abbrev beamOneLp : BeamL2 := Scalar.beamOneLp (𝕜 := ℂ)

/-- The identity function `t ↦ t` in the ambient `L²`. -/
abbrev beamIdLp : BeamL2 := Scalar.beamIdLp (𝕜 := ℂ)

theorem coeFn_beamOneLp : (beamOneLp : ℝ → ℂ) =ᵐ[unitIocMeasure] fun _ => (1 : ℂ) :=
  Scalar.coeFn_beamOneLp (𝕜 := ℂ)

theorem coeFn_beamIdLp : (beamIdLp : ℝ → ℂ) =ᵐ[unitIocMeasure] fun t => (t : ℂ) :=
  Scalar.coeFn_beamIdLp (𝕜 := ℂ)

theorem exists_affine_of_beamEmbed_sub (p : BeamV) :
    ∃ a b : ℂ, beamEmbed p - secondPrimitiveCLM (beamSnd p)
      = a • beamOneLp + b • beamIdLp :=
  Scalar.exists_affine_of_beamEmbed_sub (𝕜 := ℂ) p

theorem isCompactOperator_beamEmbed : IsCompactOperator beamEmbed :=
  Scalar.isCompactOperator_beamEmbed (𝕜 := ℂ)

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
