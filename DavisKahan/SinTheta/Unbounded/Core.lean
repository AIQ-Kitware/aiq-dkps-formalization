/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Bounded.Core
import DavisKahan.OperatorIdeal.CanonicalRealView
import DavisKahan.Sylvester.Gap
import DavisKahan.Interop.TauCeti.ClosedOperator

/-!
# Unbounded `sin Θ` problem data and residual block identity

The paper-shaped data record for the unbounded residual theorem, the adjoint
residual block identity, and the ideal-gauge transport of that block.  None of
these consumes a Sylvester estimate, so every engine that supplies one shares
them.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

section GenericCore

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Local shorthand for the ambient closed operator. -/
abbrev ClosedOperatorAmbient :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)

/-- Local shorthand for the trial closed operator. -/
abbrev ClosedOperatorTrial :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

/-- Local shorthand for the complementary closed operator. -/
abbrev ClosedOperatorComplement :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := G)

/-- Paper-shaped data for the unbounded residual theorem. -/
structure UnboundedSinThetaData where
  A : ClosedOperatorAmbient (𝕜 := 𝕜) (E := E)
  A₀ : ClosedOperatorTrial (𝕜 := 𝕜) (F := F)
  Λ₁ : ClosedOperatorComplement (𝕜 := 𝕜) (G := G)
  X : F →L[𝕜] E
  F₁ : G →L[𝕜] E
  residual : F →L[𝕜] E
  X_maps_domain : ∀ x : A₀.domain, X (x : F) ∈ A.domain
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  residual_eq : ∀ x : A₀.domain,
    A.toLinearMap ⟨X (x : F), X_maps_domain x⟩ -
      X (A₀.toLinearMap x) = residual (x : F)
  intertwines : ∀ y : Λ₁.domain,
    A.toLinearMap ⟨F₁ (y : G), F₁_maps_domain y⟩ =
      F₁ (Λ₁.toLinearMap y)

/-- Canonical partial-map data for the unbounded residual theorem.  Density
and graph closedness are properties, not fields of a local operator bundle. -/
structure UnboundedSinThetaDataPMap where
  A : E →ₗ.[𝕜] E
  A₀ : F →ₗ.[𝕜] F
  Λ₁ : G →ₗ.[𝕜] G
  A_dense : Dense (A.domain : Set E)
  A₀_dense : Dense (A₀.domain : Set F)
  Λ₁_dense : Dense (Λ₁.domain : Set G)
  A_closed : A.IsClosed
  A₀_closed : A₀.IsClosed
  Λ₁_closed : Λ₁.IsClosed
  X : F →L[𝕜] E
  F₁ : G →L[𝕜] E
  residual : F →L[𝕜] E
  X_maps_domain : ∀ x : A₀.domain, X (x : F) ∈ A.domain
  F₁_maps_domain : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain
  residual_eq : ∀ x : A₀.domain,
    A ⟨X (x : F), X_maps_domain x⟩ - X (A₀ x) = residual (x : F)
  intertwines : ∀ y : Λ₁.domain,
    A ⟨F₁ (y : G), F₁_maps_domain y⟩ = F₁ (Λ₁ y)

namespace UnboundedSinThetaDataPMap

/-- The sole compatibility conversion used by source-facing residual results
that have not yet accepted raw partial-map data. -/
noncomputable def toClosed
    (D : UnboundedSinThetaDataPMap (𝕜 := 𝕜) (E := E) (F := F) (G := G)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) where
  A := TauCeti.DavisKahanExt.ClosedOperator.ofLinearPMap D.A D.A_dense D.A_closed
  A₀ := TauCeti.DavisKahanExt.ClosedOperator.ofLinearPMap D.A₀ D.A₀_dense D.A₀_closed
  Λ₁ := TauCeti.DavisKahanExt.ClosedOperator.ofLinearPMap D.Λ₁ D.Λ₁_dense D.Λ₁_closed
  X := D.X
  F₁ := D.F₁
  residual := D.residual
  X_maps_domain := D.X_maps_domain
  F₁_maps_domain := D.F₁_maps_domain
  residual_eq := D.residual_eq
  intertwines := D.intertwines

end UnboundedSinThetaDataPMap

namespace UnboundedSinThetaData

/-- Canonical view of the historical source-facing data record.  New generic
proofs use this partial-map representation; the bundled record remains only
at source and Spectra boundaries. -/
noncomputable def toPMap
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G)) :
    UnboundedSinThetaDataPMap (𝕜 := 𝕜) (E := E) (F := F) (G := G) where
  A := D.A.toLinearPMap
  A₀ := D.A₀.toLinearPMap
  Λ₁ := D.Λ₁.toLinearPMap
  A_dense := D.A.toLinearPMap_dense
  A₀_dense := D.A₀.toLinearPMap_dense
  Λ₁_dense := D.Λ₁.toLinearPMap_dense
  A_closed := D.A.toLinearPMap_isClosed
  A₀_closed := D.A₀.toLinearPMap_isClosed
  Λ₁_closed := D.Λ₁.toLinearPMap_isClosed
  X := D.X
  F₁ := D.F₁
  residual := D.residual
  X_maps_domain := D.X_maps_domain
  F₁_maps_domain := D.F₁_maps_domain
  residual_eq := D.residual_eq
  intertwines := D.intertwines

omit [CompleteSpace F] [CompleteSpace G] in
/-- A source-facing self-adjoint ambient operator has a self-adjoint raw
partial-map view. -/
theorem toPMap_A_isSelfAdjoint
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) : _root_.IsSelfAdjoint D.toPMap.A := by
  change _root_.IsSelfAdjoint D.A.toLinearPMap
  exact LinearPMap.isSelfAdjoint_def.mpr
    ((D.A.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hA)

omit [CompleteSpace E] [CompleteSpace G] in
/-- A source-facing self-adjoint trial operator has a self-adjoint raw
partial-map view. -/
theorem toPMap_A₀_isSelfAdjoint
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA₀ : D.A₀.IsSelfAdjoint) : _root_.IsSelfAdjoint D.toPMap.A₀ := by
  change _root_.IsSelfAdjoint D.A₀.toLinearPMap
  exact LinearPMap.isSelfAdjoint_def.mpr
    ((D.A₀.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hA₀)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A source-facing self-adjoint complementary operator has a self-adjoint
raw partial-map view. -/
theorem toPMap_Λ₁_isSelfAdjoint
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hΛ₁ : D.Λ₁.IsSelfAdjoint) : _root_.IsSelfAdjoint D.toPMap.Λ₁ := by
  change _root_.IsSelfAdjoint D.Λ₁.toLinearPMap
  exact LinearPMap.isSelfAdjoint_def.mpr
    ((D.Λ₁.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hΛ₁)

end UnboundedSinThetaData

/-- The residual identity induces the domain-aware complementary Sylvester
equation.  The right-hand side has a minus sign:
`A₀ X*F₁ - X*F₁ Λ₁ = -R*F₁`. -/
theorem unbounded_adjoint_residual_block_identity
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint)
    (hA₀ : D.A₀.IsSelfAdjoint)
    (_hΛ₁ : D.Λ₁.IsSelfAdjoint) :
    HasClosedSylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (-(D.residual.adjoint ∘L D.F₁)) := by
  have hA_symm := hA.isSymmetric
  have hA₀P : D.A₀.toLinearPMap.adjoint = D.A₀.toLinearPMap :=
    (D.A₀.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hA₀
  have key : ∀ (y : D.Λ₁.domain) (x : D.A₀.domain),
      ⟪D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
          D.residual.adjoint (D.F₁ (y : G)), (x : F)⟫_𝕜 =
        ⟪D.X.adjoint (D.F₁ (y : G)), D.A₀.toLinearMap x⟫_𝕜 := by
    intro y x
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    show ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜
    let Fx : D.A.domain := ⟨D.X (x : F), D.X_maps_domain x⟩
    let Fy : D.A.domain := ⟨D.F₁ (y : G), D.F₁_maps_domain y⟩
    calc
      ⟪w, (x : F)⟫_𝕜 =
          ⟪D.F₁ (D.Λ₁.toLinearMap y), D.X (x : F)⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        rw [inner_sub_left,
          D.X.adjoint_inner_left (x : F) (D.F₁ (D.Λ₁.toLinearMap y)),
          D.residual.adjoint_inner_left (x : F) (D.F₁ (y : G))]
      _ = ⟪D.A.toLinearMap Fy, D.X (x : F)⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        rw [← D.intertwines y]
      _ = ⟪D.F₁ (y : G), D.A.toLinearMap Fx⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        have hsymm :
            ⟪D.A.toLinearMap Fy, D.X (x : F)⟫_𝕜 =
              ⟪D.F₁ (y : G), D.A.toLinearMap Fx⟫_𝕜 := by
          simpa only [
            TauCeti.DavisKahanExt.ClosedOperator.toLinearPMap_apply,
            Fx, Fy] using hA_symm Fy Fx
        rw [hsymm]
      _ = ⟪D.F₁ (y : G), D.X (D.A₀.toLinearMap x)⟫_𝕜 := by
        rw [← D.residual_eq x, inner_sub_right]
        abel
      _ = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
        rw [← D.X.adjoint_inner_left (D.A₀.toLinearMap x) (D.F₁ (y : G))]
  refine ⟨?_, ?_⟩
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := key y
    have hzAdj : z ∈ D.A₀.toLinearPMap.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hz : z ∈ D.A₀.toLinearPMap.domain := by
      rw [← hA₀P]
      exact hzAdj
    simpa only [z, ContinuousLinearMap.comp_apply] using hz
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := key y
    have hzAdj : z ∈ D.A₀.toLinearPMap.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hzDomPMap : z ∈ D.A₀.toLinearPMap.domain := by
      simpa only [hA₀P] using hzAdj
    have hzDom : z ∈ D.A₀.domain := by
      simpa only [
        TauCeti.DavisKahanExt.ClosedOperator.toLinearPMap_domain] using
        hzDomPMap
    have hA₀z : D.A₀.toLinearMap ⟨z, hzDom⟩ = w := by
      have hinner :
          (fun x : F => ⟪D.A₀.toLinearMap ⟨z, hzDom⟩, x⟫_𝕜) =
            fun x : F => ⟪w, x⟫_𝕜 := by
        apply Continuous.ext_on D.A₀.dense_domain
        · exact continuous_const.inner continuous_id
        · exact continuous_const.inner continuous_id
        · intro x hx
          let xDom : D.A₀.domain := ⟨x, hx⟩
          calc
            ⟪D.A₀.toLinearMap ⟨z, hzDom⟩, x⟫_𝕜 =
                ⟪z, D.A₀.toLinearMap xDom⟫_𝕜 := hA₀.isSymmetric ⟨z, hzDom⟩ xDom
            _ = ⟪w, x⟫_𝕜 := (hw xDom).symm
      have hzero :
          ⟪D.A₀.toLinearMap ⟨z, hzDom⟩ - w,
            D.A₀.toLinearMap ⟨z, hzDom⟩ - w⟫_𝕜 = 0 := by
        rw [inner_sub_left,
          congrFun hinner (D.A₀.toLinearMap ⟨z, hzDom⟩ - w), sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
    change D.A₀.toLinearMap ⟨z, hzDom⟩ -
        D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) =
      -D.residual.adjoint (D.F₁ (y : G))
    rw [hA₀z]
    unfold w
    abel

/-- The raw partial-map form of the complementary residual Sylvester equation.
Unlike the historical source-facing wrapper, this theorem is proved directly
over `LinearPMap` domains and adjoints. -/
theorem linearPMap_unbounded_adjoint_residual_block_identity
    (D : UnboundedSinThetaDataPMap (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A)
    (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (_hΛ₁ : _root_.IsSelfAdjoint D.Λ₁) :
    TauCeti.LinearPMap.SylvesterEquation D.A₀ D.Λ₁
      (D.X.adjoint ∘L D.F₁)
      (-(D.residual.adjoint ∘L D.F₁)) := by
  have hA_symm : ∀ x y : D.A.domain,
      ⟪D.A x, (y : E)⟫_𝕜 = ⟪(x : E), D.A y⟫_𝕜 := by
    have hformal := LinearPMap.adjoint_isFormalAdjoint D.A_dense
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at hformal
    intro x y
    exact hformal x y
  have hA₀P : D.A₀.adjoint = D.A₀ := LinearPMap.isSelfAdjoint_def.mp hA₀
  have hA₀_symm : ∀ x y : D.A₀.domain,
      ⟪D.A₀ x, (y : F)⟫_𝕜 = ⟪(x : F), D.A₀ y⟫_𝕜 := by
    have hformal := LinearPMap.adjoint_isFormalAdjoint D.A₀_dense
    rw [hA₀P] at hformal
    intro x y
    exact hformal x y
  have key : ∀ (y : D.Λ₁.domain) (x : D.A₀.domain),
      ⟪D.X.adjoint (D.F₁ (D.Λ₁ y)) -
          D.residual.adjoint (D.F₁ (y : G)), (x : F)⟫_𝕜 =
        ⟪D.X.adjoint (D.F₁ (y : G)), D.A₀ x⟫_𝕜 := by
    intro y x
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁ y)) -
        D.residual.adjoint (D.F₁ (y : G))
    show ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀ x⟫_𝕜
    let Fx : D.A.domain := ⟨D.X (x : F), D.X_maps_domain x⟩
    let Fy : D.A.domain := ⟨D.F₁ (y : G), D.F₁_maps_domain y⟩
    calc
      ⟪w, (x : F)⟫_𝕜 =
          ⟪D.F₁ (D.Λ₁ y), D.X (x : F)⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        rw [inner_sub_left,
          D.X.adjoint_inner_left (x : F) (D.F₁ (D.Λ₁ y)),
          D.residual.adjoint_inner_left (x : F) (D.F₁ (y : G))]
      _ = ⟪D.A Fy, D.X (x : F)⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        rw [← D.intertwines y]
      _ = ⟪D.F₁ (y : G), D.A Fx⟫_𝕜 -
            ⟪D.F₁ (y : G), D.residual (x : F)⟫_𝕜 := by
        have hsymm :
            ⟪D.A Fy, D.X (x : F)⟫_𝕜 =
              ⟪D.F₁ (y : G), D.A Fx⟫_𝕜 := by
          simpa only [Fx, Fy] using hA_symm Fy Fx
        rw [hsymm]
      _ = ⟪D.F₁ (y : G), D.X (D.A₀ x)⟫_𝕜 := by
        rw [← D.residual_eq x, inner_sub_right]
        abel
      _ = ⟪z, D.A₀ x⟫_𝕜 := by
        rw [← D.X.adjoint_inner_left (D.A₀ x) (D.F₁ (y : G))]
  refine ⟨?_, ?_⟩
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁ y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀ x⟫_𝕜 := key y
    have hzAdj : z ∈ D.A₀.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hz : z ∈ D.A₀.domain := by
      rw [← hA₀P]
      exact hzAdj
    simpa only [z, ContinuousLinearMap.comp_apply] using hz
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁ y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀ x⟫_𝕜 := key y
    have hzAdj : z ∈ D.A₀.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hzDom : z ∈ D.A₀.domain := by
      simpa only [hA₀P] using hzAdj
    have hA₀z : D.A₀ ⟨z, hzDom⟩ = w := by
      have hinner :
          (fun x : F => ⟪D.A₀ ⟨z, hzDom⟩, x⟫_𝕜) =
            fun x : F => ⟪w, x⟫_𝕜 := by
        apply Continuous.ext_on D.A₀_dense
        · exact continuous_const.inner continuous_id
        · exact continuous_const.inner continuous_id
        · intro x hx
          let xDom : D.A₀.domain := ⟨x, hx⟩
          calc
            ⟪D.A₀ ⟨z, hzDom⟩, x⟫_𝕜 =
                ⟪z, D.A₀ xDom⟫_𝕜 := hA₀_symm ⟨z, hzDom⟩ xDom
            _ = ⟪w, x⟫_𝕜 := (hw xDom).symm
      have hzero :
          ⟪D.A₀ ⟨z, hzDom⟩ - w,
            D.A₀ ⟨z, hzDom⟩ - w⟫_𝕜 = 0 := by
        rw [inner_sub_left,
          congrFun hinner (D.A₀ ⟨z, hzDom⟩ - w), sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
    change D.A₀ ⟨z, hzDom⟩ - D.X.adjoint (D.F₁ (D.Λ₁ y)) =
      -D.residual.adjoint (D.F₁ (y : G))
    rw [hA₀z]
    unfold w
    abel

/-- The projected residual block remains in the same rectangular ideal and its
 gauge is no larger than the original residual gauge. -/
theorem adjointResidualBlock_mem_and_gauge_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hF₁ : IsometricEmbedding D.F₁)
    (hR : N.Mem D.residual) :
    N.Mem (-(D.residual.adjoint ∘L D.F₁)) ∧
      N.gaugeReal (-(D.residual.adjoint ∘L D.F₁)) ≤
        N.gaugeReal D.residual := by
  have hAdj : N.Mem D.residual.adjoint := N.adjoint_mem hR
  have hComp : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.comp_right_mem D.F₁ hAdj
  refine ⟨N.neg_mem hComp, ?_⟩
  calc
    N.gaugeReal (-(D.residual.adjoint ∘L D.F₁))
        = N.gaugeReal (D.residual.adjoint ∘L D.F₁) := N.gaugeReal_neg hComp
    _ ≤ N.gaugeReal D.residual.adjoint :=
      N.gaugeReal_comp_right_le D.F₁ hAdj (opNorm_le_one_of_isometry hF₁)
    _ = N.gaugeReal D.residual := N.gaugeReal_adjoint hR

end GenericCore

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
