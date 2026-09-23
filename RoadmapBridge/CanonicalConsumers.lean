/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DavisKahan.All
import ForTauCeti.Analysis.Normed.Operator.Restriction
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance

/-! # Direct canonical consumers

These examples exercise the canonical APIs without paper-local forwarding definitions.
The norm and spectrum restrictions do not require an inner product or completeness;
the finite Sylvester estimate accepts independent rectangular carriers over `RCLike`.
The imported production library must not reintroduce the removed compatibility names.
-/

namespace RoadmapBridge.CanonicalConsumers

universe u v w

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

example (T : E →ₗ.[K] F) :
    T.IsClosed ↔ IsClosed (Set.range fun x : T.domain => ((x : E), T x)) :=
  TauCeti.LinearPMap.isClosed_iff_range_isClosed T

example [CompleteSpace E] (A : E →L[K] E) (hA : A.IsSymmetric) :
    IsSelfAdjoint ((A : E →ₗ[K] E).toPMap ⊤) :=
  TauCeti.LinearPMap.isSelfAdjoint_toPMap_top
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA)

example [CompleteSpace E] {A B : E →L[K] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule K E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V) {c g : Real} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * norm x ^ 2 ≤ RCLike.re (inner K (A x) x))
    (hVc : ∀ x ∈ V, RCLike.re (inner K (B x) x) ≤ c * norm x ^ 2) :
    norm (V.starProjection.comp U.starProjection) ≤ norm (B - A) / g :=
  Submodule.sinTheta_directed_coercive hA hB hU hV hg hUc hVc

example [FiniteDimensional K E] [FiniteDimensional K F]
    (N : TauCeti.UnitarilyInvariantSeminorm K E F)
    {A : F →ₗ[K] F} {B : E →ₗ[K] E} {X C : E →ₗ[K] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {delta : Real} (hd : 0 < delta)
    (hgap : TauCeti.PointSpectraSeparated A ⊤ B ⊤ delta)
    (hEq : A.comp X - X.comp B = C) :
    delta * N X ≤ (Real.pi / 2) * N C :=
  TauCeti.uiNorm_sylvester_le_of_spectralDistance N hA hB hd hgap hEq

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
      `TauCeti.uiNorm_sylvester_le_of_spectralDistance_real,
      `TauCeti.uiNorm_sylvester_le_of_spectralDistance_complex] do
    if env.contains name then
      throwError "Noncanonical compatibility declaration remains: {name}"
