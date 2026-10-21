/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic
public import ForTauCeti.Analysis.InnerProductSpace.KyFan

/-! # UI-seminorm transport along isometric embeddings

Tau Ceti supplies the canonical unitarily-invariant seminorm and transport along isometric
equivalences. These two constructions extend that API to isometric embeddings by using zero-padded
composition on the codomain or the adjoint embedding on the domain. -/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

open scoped InnerProductSpace
open _root_.LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Pull a rectangular UI norm back along an isometric embedding of the
codomain.  The transported norm measures `A : E → H` by measuring
`ι ∘ A : E → F`. -/
@[expose]
noncomputable def codomainIsometryTransport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) :
    UnitarilyInvariantSeminorm 𝕜 E H where
  toSeminorm := Seminorm.of
    (fun A => N (ι.toLinearMap ∘ₗ A))
    (fun A B => by
      have hmap : ι.toLinearMap ∘ₗ (A + B) =
          (ι.toLinearMap ∘ₗ A) + (ι.toLinearMap ∘ₗ B) := by
        ext x
        simp
      rw [hmap]
      exact map_add_le_add N _ _)
    (fun a A => by
      have hmap : ι.toLinearMap ∘ₗ (a • A) =
          a • (ι.toLinearMap ∘ₗ A) := by
        ext x
        simp
      rw [hmap]
      exact map_smul_eq_mul N _ _)
  map_linearIsometryEquiv_comp_comp' U V A := by
        apply N.map_eq_of_singularValues_eq
        calc
          (ι.toLinearMap ∘ₗ (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)).singularValues =
              (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues :=
            singularValues_linearIsometry_comp ι _
          _ = A.singularValues := by
            change ((U : H →ₗ[𝕜] H) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)).singularValues = _
            simp only [LinearMap.singularValues_linearIsometryEquiv_comp,
              LinearMap.singularValues_comp_linearIsometryEquiv]
          _ = (ι.toLinearMap ∘ₗ A).singularValues :=
            (singularValues_linearIsometry_comp ι A).symm

/-- Codomain transport, unfolded. -/
@[simp] theorem codomainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] H) :
    N.codomainIsometryTransport ι A = N (ι.toLinearMap ∘ₗ A) :=
  (rfl)

/-- Pull a rectangular UI norm back along the adjoint of an isometric
embedding of the domain.  The transported norm measures `A : H → F` by the
zero-padded map `A ∘ ι⋆ : E → F`. -/
@[expose]
noncomputable def domainIsometryTransport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] E) :
    UnitarilyInvariantSeminorm 𝕜 H F where
  toSeminorm := Seminorm.of
    (fun A => N (A ∘ₗ LinearMap.adjoint ι.toLinearMap))
    (fun A B => by
      have hmap : (A + B) ∘ₗ LinearMap.adjoint ι.toLinearMap =
          (A ∘ₗ LinearMap.adjoint ι.toLinearMap) +
            (B ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
        ext x
        simp
      rw [hmap]
      exact map_add_le_add N _ _)
    (fun a A => by
      have hmap : (a • A) ∘ₗ LinearMap.adjoint ι.toLinearMap =
          a • (A ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
        ext x
        simp
      rw [hmap]
      exact map_smul_eq_mul N _ _)
  map_linearIsometryEquiv_comp_comp' U V A := by
        apply N.map_eq_of_singularValues_eq
        calc
          ((U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) ∘ₗ
              LinearMap.adjoint ι.toLinearMap).singularValues =
              (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues :=
            singularValues_comp_adjoint_linearIsometry ι _
          _ = A.singularValues := by
            change ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : H →ₗ[𝕜] H)).singularValues = _
            simp only [LinearMap.singularValues_linearIsometryEquiv_comp,
              LinearMap.singularValues_comp_linearIsometryEquiv]
          _ = (A ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues :=
            (singularValues_comp_adjoint_linearIsometry ι A).symm

/-- Domain transport, unfolded. -/
@[simp] theorem domainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] E) (A : H →ₗ[𝕜] F) :
    N.domainIsometryTransport ι A =
      N (A ∘ₗ LinearMap.adjoint ι.toLinearMap) :=
  (rfl)



end TauCeti.UnitarilyInvariantSeminorm
