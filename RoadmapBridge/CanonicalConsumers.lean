/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.Decay
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.RitzTangent
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import DavisKahan.All
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import ForTauCeti.Analysis.Normed.Operator.Restriction
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance

/-! # Direct canonical consumers

These examples exercise the canonical APIs without paper-local forwarding definitions.
The norm and spectrum restrictions do not require an inner product or completeness;
the finite Sylvester estimate accepts independent rectangular carriers over `RCLike`.
The imported production library must not reintroduce the removed compatibility names.
-/

public section

namespace RoadmapBridge.CanonicalConsumers

universe u v w

section Decay

example {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Asymptotics.IsLittleO (Filter.cocompact ℝ)
      (fun x : ℝ => Real.exp (-(a * |x|))) (fun x : ℝ => |x| ^ s) :=
  TauCeti.exp_neg_mul_abs_isLittleO_abs_rpow_cocompact ha s

example {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    Asymptotics.IsLittleO (Filter.cocompact ℝ)
      (fun x : ℝ => Complex.exp (-(a * |x|))) (fun x : ℝ => |x| ^ s) :=
  TauCeti.cexp_neg_mul_abs_isLittleO_abs_rpow_cocompact ha s

end Decay

section Normed

variable {K : Type u} [NontriviallyNormedField K]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

example (T : E →L[K] F) (M : Submodule K F) (hT : forall x, T x ∈ M) :
    norm (T.codRestrict M hT) = norm T :=
  ContinuousLinearMap.opNorm_codRestrict_eq T M hT

example (A : E →L[K] E)
    (hA : ∀ x ∈ (⊤ : Submodule K E), A x ∈ (⊤ : Submodule K E)) :
    spectrum K (A.restrict hA) = spectrum K A :=
  ContinuousLinearMap.spectrum_restrict_top A hA

end Normed

section Hilbert

variable {K : Type u} [RCLike K]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]
  {F : Type w} [NormedAddCommGroup F] [InnerProductSpace K F]

example [FiniteDimensional K E] {Z U : Submodule K E}
    [U.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (N : TauCeti.UnitarilyInvariantSeminorm K Z E)
    {A : E →ₗ[K] E} (hA : A.IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U)
    {α δ : ℝ} (hδ : 0 < δ)
    (hM : Module.End.PointSpectrumIn (Z.subtype.adjoint ∘ₗ A ∘ₗ Z.subtype) ⊤ (Set.Iic α))
    (hperp : Module.End.PointSpectrumIn A Uᗮ (Set.Ici (α + δ))) :
    δ * N (Z.tanThetaMap U) ≤
      N (A ∘ₗ Z.subtype - Z.subtype ∘ₗ (Z.subtype.adjoint ∘ₗ A ∘ₗ Z.subtype)) :=
  N.mul_map_tanThetaMap_le_map_ritzResidual hA hU hδ hM hperp

example (T : E →ₗ.[K] F) :
    T.IsClosed ↔ IsClosed (Set.range fun x : T.domain => ((x : E), T x)) :=
  TauCeti.LinearPMap.isClosed_iff_range_isClosed T

example [CompleteSpace E] (A : E →L[K] E) (hA : A.IsSymmetric) :
    IsSelfAdjoint ((A : E →ₗ[K] E).toPMap ⊤) :=
  _root_.LinearPMap.isSelfAdjoint_toPMap_top
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)

example {A B : E →L[K] E} (hB : B.IsSymmetric)
    {U V : Submodule K E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {c g : Real} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * norm x ^ 2 ≤ RCLike.re (inner K (A x) x))
    (hVc : ∀ x ∈ V, RCLike.re (inner K (B x) x) ≤ c * norm x ^ 2) :
    norm (V.starProjection.comp U.starProjection) ≤ norm (B - A) / g :=
  Submodule.norm_starProjection_comp_starProjection_le_norm_sub_div U V hB hU hV hg hUc hVc

example [FiniteDimensional K E] [FiniteDimensional K F]
    (N : TauCeti.UnitarilyInvariantSeminorm K E F)
    {A : F →L[K] F} {B : E →L[K] E} (X : E →L[K] F)
    (hA : (A : F →ₗ[K] F).IsSymmetric) (hB : (B : E →ₗ[K] E).IsSymmetric)
    {delta : Real} (hgap : Module.End.PointSpectraSeparated
      (A : F →ₗ[K] F) ⊤ (B : E →ₗ[K] E) ⊤ delta) :
    delta * N X ≤ (Real.pi / 2) * N (A.sylvester B X) :=
  N.mul_map_le_pi_div_two_mul_map_sylvester_apply hA hB hgap X

end Hilbert

end RoadmapBridge.CanonicalConsumers

-- Absence is checked after importing the production aggregate, not on an empty environment.
open Lean in
run_cmd do
  let env ← Lean.getEnv
  for name in #[
      `TauCeti.DavisKahan.IsSelfAdjointOperator,
      `TauCeti.DavisKahan.projection,
      `TauCeti.DavisKahan.complementaryProjection,
      `TauCeti.DavisKahan.subspaceGap,
      `TauCeti.DavisKahan.directedGap,
      `TauCeti.DavisKahan.Foundation.IsUnitaryOperator,
      `TauCeti.DavisKahan.Foundation.topContinuousLinearEquiv,
      `TauCeti.DavisKahan.Foundation.conjAlgEquiv,
      `ContinuousLinearEquiv.conjAlgEquiv,
      `TauCeti.DavisKahan.Sylvester.sylvesterOperator,
      `TauCeti.DavisKahanExt.codRestrictTo,
      `TauCeti.DavisKahanExt.restrictToReducingSubspace,
      `TauCeti.DavisKahanExt.restrictToOrthogonal,
      `TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint,
      `TauCeti.RectangularUnitarilyInvariantSeminorm,
      `TauCeti.SquareUnitarilyInvariantSeminorm,
      `TauCeti.ContinuousLinearMap.isUnit_of_coercive,
      `TauCeti.kyFan_sylvester_le_of_spectralDistance,
      `TauCeti.uiNorm_sylvester_le_of_spectralDistance,
      `TauCeti.sinTheta_perturbation_le_of_spectralDistance,
      `TauCeti.uiNorm_sylvester_le_of_spectralDistance_real,
      `TauCeti.uiNorm_sylvester_le_of_spectralDistance_complex] do
    if env.contains name then
      throwError "Noncanonical compatibility declaration remains: {name}"
