/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Angle.AngleFunctionalCalculusReal
import DavisKahan.SpectralTheory.ReflectionRestriction
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
import ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-!
# The operator angle at an arbitrary `RCLike` field

`sinAngleOperator`, `angleOperator` and `sinTwoAngleOperator` are the paper's `sin Θ`, `Θ` and
`sin 2Θ` between two closed subspaces of a Hilbert space over an arbitrary `RCLike` field:

```text
sin Θ  = |P_U - P_V|            Θ = arcsin (sin Θ)          sin 2Θ = sin (2 Θ)
```

Nothing in those formulas is field-specific.  They were nevertheless written twice — over `ℂ`
by the functional calculus and over `ℝ` by descent from the complexification — because the real
continuous functional calculus was not available at an abstract field.
`ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean` registers it, so the
definitions below are the direct ones and carry no hypothesis beyond `[RCLike 𝕜]`.

## The two identifications

* over `ℂ` the generic definitions **are** `sinAngleOperatorC`, `angleOperatorC` and
  `sinTwoAngleOperatorC`, definitionally;
* over `ℝ` they agree with `sinAngleOperatorR`, `angleOperatorR` and `sinTwoAngleOperatorR`,
  which are defined by descent.  That is a theorem, and its content is the naturality of the
  calculus along the complexification (`TauCeti.RealComplexification.complexify_cfc` and
  `complexify_modulus`).

Those two identifications are what lets a scalar-generic theorem be proved by dispatching an
arbitrary `RCLike` field to its real-like or complex-like case and reusing the fixed-field
analytic proofs.  `clm_sinTwoAngleOperator` and its siblings carry the objects across the
scalar transport that makes the dispatch possible.
-/

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

noncomputable section

universe u w v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ## The definitions -/

/-- **The paper's `sin Θ` between two closed subspaces**, at an arbitrary `RCLike` field: the
modulus of the projector difference. -/
def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (U.starProjection - V.starProjection)

/-- **The paper's Hermitian operator angle `Θ = arcsin |P_U - P_V|`**, at an arbitrary `RCLike`
field. -/
def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  cfc Real.arcsin (sinAngleOperator U V)

/-- **The paper's ambient `sin 2Θ`**, at an arbitrary `RCLike` field. -/
def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperator U V)

variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- `sin Θ` is nonnegative, being a modulus. -/
theorem sinAngleOperator_nonneg : 0 ≤ sinAngleOperator U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- `sin Θ` is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperator : IsSelfAdjoint (sinAngleOperator U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

/-- The operator angle is self-adjoint. -/
theorem isSelfAdjoint_angleOperator : IsSelfAdjoint (angleOperator U V) :=
  cfc_predicate Real.arcsin (sinAngleOperator U V)

/-- `sin 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_sinTwoAngleOperator : IsSelfAdjoint (sinTwoAngleOperator U V) :=
  cfc_predicate _ (angleOperator U V)

/-! ## Over `ℂ`: the generic objects are the complex ones

Definitionally so: `ContinuousFunctionalCalculus` is a `Prop`, and the real algebra structure
the generic definition resolves is the restriction of scalars that `E →L[ℂ] E` already
carries. -/

section Complex

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U V : Submodule ℂ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

@[simp] theorem sinAngleOperator_complex : sinAngleOperator U V = sinAngleOperatorC U V := rfl

@[simp] theorem angleOperator_complex : angleOperator U V = angleOperatorC U V := rfl

@[simp] theorem sinTwoAngleOperator_complex :
    sinTwoAngleOperator U V = sinTwoAngleOperatorC U V := rfl

end Complex

/-! ## Over `ℝ`: the generic objects are the descended ones

Here there is something to prove.  `sinAngleOperatorR` and its siblings are *defined* as the
real parts of the complex angle operators of the complexified pair, so the identification is
the naturality of the modulus and of the calculus along `complexify`, plus injectivity of
`complexify`. -/

section Real

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (U V : Submodule ℝ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

@[simp] theorem sinAngleOperator_real : sinAngleOperator U V = sinAngleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_sinAngleOperatorR]
  change complexify (ContinuousLinearMap.modulus (U.starProjection - V.starProjection)) =
    ContinuousLinearMap.modulus
      ((complexifySubmodule U).starProjection - (complexifySubmodule V).starProjection)
  rw [complexify_modulus, starProjection_complexifySubmodule, starProjection_complexifySubmodule,
    complexify_sub]

@[simp] theorem angleOperator_real : angleOperator U V = angleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_angleOperatorR]
  change complexify (cfc Real.arcsin (sinAngleOperator U V)) = _
  rw [complexify_cfc Real.arcsin (isSelfAdjoint_sinAngleOperator U V)
      Real.continuous_arcsin.continuousOn,
    sinAngleOperator_real, complexify_sinAngleOperatorR]
  rfl

@[simp] theorem sinTwoAngleOperator_real :
    sinTwoAngleOperator U V = sinTwoAngleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_sinTwoAngleOperatorR]
  change complexify (cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperator U V)) = _
  rw [complexify_cfc _ (isSelfAdjoint_angleOperator U V)
      (by fun_prop : ContinuousOn (fun t : ℝ => Real.sin (2 * t)) _),
    angleOperator_real, complexify_angleOperatorR]
  rfl

end Real

/-! ## Across the scalar transport

`ScalarTransport e E` is `E` with the `𝕂`-structure induced by a field isomorphism
`e : RCLikeIso 𝕜 𝕂`, and `ScalarTransport.clm` carries operators across it.  These three
lemmas say the angle operators go across too, which is what turns a fixed-field theorem into a
theorem at an arbitrary `RCLike` field. -/

section Transport

variable {𝕂 : Type w} [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}

open TauCeti.ScalarTransport

@[simp] theorem clm_sinAngleOperator :
    clm (e := e) (sinAngleOperator U V) =
      sinAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (ContinuousLinearMap.modulus (U.starProjection - V.starProjection)) =
    ContinuousLinearMap.modulus
      ((ScalarTransport.submodule (e := e) U).starProjection -
        (ScalarTransport.submodule (e := e) V).starProjection)
  rw [clm_modulus, starProjection_clm, starProjection_clm, clm_sub]

@[simp] theorem clm_angleOperator :
    clm (e := e) (angleOperator U V) =
      angleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (cfc Real.arcsin (sinAngleOperator U V)) = _
  rw [clm_cfc Real.arcsin (isSelfAdjoint_sinAngleOperator U V)
      Real.continuous_arcsin.continuousOn, clm_sinAngleOperator]
  rfl

@[simp] theorem clm_sinTwoAngleOperator :
    clm (e := e) (sinTwoAngleOperator U V) =
      sinTwoAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperator U V)) = _
  rw [clm_cfc _ (isSelfAdjoint_angleOperator U V)
      (by fun_prop : ContinuousOn (fun t : ℝ => Real.sin (2 * t)) _), clm_angleOperator]
  rfl

end Transport

/-! ## The reflection form of `sin 2Θ`

`sin 2Θ` is the modulus of the difference between the projection onto `U` and the projection
onto the mirror image of `U` through `V`.  This is the paper's own double-angle trick, and it
is the form every `sin 2Θ` estimate is actually proved in: the right-hand side is an ordinary
`sin Θ` between a reflected pair.

The identity holds at every `RCLike` field.  It is proved once over `ℂ`
(`directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub`, a functional-calculus
computation), descended to `ℝ`, and then carried to an arbitrary field by the scalar
transport. -/

section ReflectionForm

/-- The projection onto a reflected complexified subspace is the complexification of the
projection onto the reflected real subspace. -/
theorem complexify_starProjection_map_reflection {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    complexify ((U.map (V.reflection.toLinearEquiv : F →ₗ[ℝ] F)).starProjection -
        U.starProjection) =
      ((complexifySubmodule U).map
          ((complexifySubmodule V).reflection.toLinearEquiv :
            RealComplexification F →ₗ[ℂ] RealComplexification F)).starProjection -
        (complexifySubmodule U).starProjection := by
  have hconj : ∀ T : F →L[ℝ] F,
      _root_.TauCeti.DavisKahan.boundedUnitaryConjugate V.reflection T =
        V.reflectionOperator ∘L T ∘L V.reflectionOperator :=
    fun _ => ContinuousLinearMap.ext fun _ => rfl
  have hconjC : ∀ T : RealComplexification F →L[ℂ] RealComplexification F,
      _root_.TauCeti.DavisKahan.boundedUnitaryConjugate (complexifySubmodule V).reflection T =
        (complexifySubmodule V).reflectionOperator ∘L T ∘L
          (complexifySubmodule V).reflectionOperator :=
    fun _ => ContinuousLinearMap.ext fun _ => rfl
  have hrefl : complexify V.reflectionOperator = (complexifySubmodule V).reflectionOperator := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id,
      Submodule.reflectionOperator_eq_two_smul_sub_id, complexify_sub,
      complexify_real_smul, complexify_id, starProjection_complexifySubmodule]
    norm_num
  rw [_root_.TauCeti.DavisKahan.starProjection_map_unitary U V.reflection,
    _root_.TauCeti.DavisKahan.starProjection_map_unitary (complexifySubmodule U)
      (complexifySubmodule V).reflection,
    complexify_sub, hconj U.starProjection,
    hconjC (complexifySubmodule U).starProjection,
    complexify_comp, complexify_comp, hrefl, starProjection_complexifySubmodule]

/-- The reflection form of `sin 2Θ` over `ℝ`, by descent from `ℂ`. -/
theorem sinTwoAngleOperatorR_eq_modulus_starProjection_sub {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinTwoAngleOperatorR U V =
      ((U.map (V.reflection.toLinearEquiv : F →ₗ[ℝ] F)).starProjection -
        U.starProjection).modulus := by
  refine complexify_injective ?_
  rw [complexify_sinTwoAngleOperatorR, complexify_modulus,
    complexify_starProjection_map_reflection,
    directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub]

/-- Transport step: the reflection form at a field isomorphic to `𝕜` gives it at `𝕜`. -/
private theorem reflectionForm_of_transport {𝕂 : Type w} [RCLike 𝕂] (e : RCLikeIso 𝕜 𝕂)
    (h : sinTwoAngleOperator (TauCeti.ScalarTransport.submodule (e := e) U)
          (TauCeti.ScalarTransport.submodule (e := e) V) =
        (((TauCeti.ScalarTransport.submodule (e := e) U).map
              ((TauCeti.ScalarTransport.submodule (e := e) V).reflection.toLinearEquiv :
                TauCeti.ScalarTransport e E →ₗ[𝕂] TauCeti.ScalarTransport e E)).starProjection -
            (TauCeti.ScalarTransport.submodule (e := e) U).starProjection).modulus) :
    sinTwoAngleOperator U V =
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection -
        U.starProjection).modulus := by
  refine (TauCeti.ScalarTransport.clmEquiv (e := e)).injective ?_
  change TauCeti.ScalarTransport.clm (e := e) (sinTwoAngleOperator U V) =
    TauCeti.ScalarTransport.clm (e := e) _
  rw [clm_sinTwoAngleOperator, TauCeti.ScalarTransport.clm_modulus,
    TauCeti.ScalarTransport.clm_sub, ← TauCeti.ScalarTransport.starProjection_clm,
    ← TauCeti.ScalarTransport.starProjection_clm,
    Submodule.starProjection_congr
      (TauCeti.ScalarTransport.submodule_map_reflection (e := e) U V)]
  exact h

/-- **The reflection form of `sin 2Θ`, at an arbitrary `RCLike` field.**

`sin 2Θ(U, V) = |P_{J_V U} - P_U|`, where `J_V` is the reflection in `V`.  This is what makes
a `sin 2Θ` bound an instance of a `sin Θ` bound for the reflected pair. -/
theorem sinTwoAngleOperator_eq_modulus_starProjection_sub :
    sinTwoAngleOperator U V =
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection -
        U.starProjection).modulus := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · refine reflectionForm_of_transport U V (RCLikeIso.real h) ?_
    rw [sinTwoAngleOperator_real]
    exact sinTwoAngleOperatorR_eq_modulus_starProjection_sub _ _
  · refine reflectionForm_of_transport U V (RCLikeIso.complex h) ?_
    rw [sinTwoAngleOperator_complex]
    exact directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub _ _

/-- **An operator and its modulus have the same approximation numbers**, at an arbitrary
`RCLike` field.

`ContinuousLinearMap.modulus_hasSameApproximationNumbers` is stated over `ℂ` because the
modulus needs a real functional calculus on the operator algebra; this file activates that
calculus at every `RCLike` field, so the same one-line proof applies. -/
theorem modulus_hasSameApproximationNumbers_rclike {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (T : E →L[𝕜] F) :
    (ContinuousLinearMap.modulus T).HasSameApproximationNumbers T :=
  ContinuousLinearMap.hasSameApproximationNumbers_of_norm_apply_eq _ _ T.norm_modulus_apply

/-- The consequence the ambient `sin 2Θ` theorem uses: `sin 2Θ` and the reflected projector
difference have the same complete singular-value sequence, so no unitarily invariant norm can
tell them apart. -/
theorem sinTwoAngleOperator_hasSameApproximationNumbers :
    (sinTwoAngleOperator U V).HasSameApproximationNumbers
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection - U.starProjection) := by
  rw [sinTwoAngleOperator_eq_modulus_starProjection_sub]
  exact modulus_hasSameApproximationNumbers_rclike _

end ReflectionForm


end

end DavisKahan.Angle
end TauCeti
