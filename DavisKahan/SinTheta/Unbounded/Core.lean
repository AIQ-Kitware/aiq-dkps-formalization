/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Bounded.Core
import DavisKahan.Sylvester.Gap

/-!
# Unbounded `sin Θ` problem data and residual block identity

The paper-shaped data record for the unbounded residual theorem, the adjoint
residual block identity, and the ideal-gauge transport of that block.  None of
these consumes a Sylvester estimate, so every engine that supplies one shares
them.
-/

namespace ForMathlib
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

abbrev ClosedOperatorAmbient :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)

abbrev ClosedOperatorTrial :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

abbrev ClosedOperatorComplement :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := G)

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
  refine ⟨?_, ?_⟩
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
      intro x
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
          rw [hA_symm Fy Fx]
        _ = ⟪D.F₁ (y : G), D.X (D.A₀.toLinearMap x)⟫_𝕜 := by
          rw [← D.residual_eq x, inner_sub_right]
          abel
        _ = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
          rw [← D.X.adjoint_inner_left (D.A₀.toLinearMap x) (D.F₁ (y : G))]
    have hzAdj : z ∈ D.A₀.toLinearPMap.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hdom : D.A₀.toLinearPMap.adjoint.domain = D.A₀.domain :=
      congrArg LinearPMap.domain hA₀P
    exact hdom ▸ hzAdj
  · intro y
    let z : F := D.X.adjoint (D.F₁ (y : G))
    let w : F :=
      D.X.adjoint (D.F₁ (D.Λ₁.toLinearMap y)) -
        D.residual.adjoint (D.F₁ (y : G))
    have hw : ∀ x : D.A₀.domain,
        ⟪w, (x : F)⟫_𝕜 = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
      intro x
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
          rw [hA_symm Fy Fx]
        _ = ⟪D.F₁ (y : G), D.X (D.A₀.toLinearMap x)⟫_𝕜 := by
          rw [← D.residual_eq x, inner_sub_right]
          abel
        _ = ⟪z, D.A₀.toLinearMap x⟫_𝕜 := by
          rw [← D.X.adjoint_inner_left (D.A₀.toLinearMap x) (D.F₁ (y : G))]
    have hzAdj : z ∈ D.A₀.toLinearPMap.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists z ⟨w, hw⟩
    have hdom : D.A₀.toLinearPMap.adjoint.domain = D.A₀.domain :=
      congrArg LinearPMap.domain hA₀P
    have hzDom : z ∈ D.A₀.domain := hdom ▸ hzAdj
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

/-- The projected residual block remains in the same rectangular ideal and its
 gauge is no larger than the original residual gauge. -/
theorem adjointResidualBlock_mem_and_gauge_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hF₁ : IsometricEmbedding D.F₁)
    (hR : N.Mem D.residual) :
    N.Mem (-(D.residual.adjoint ∘L D.F₁)) ∧
      N.gauge (-(D.residual.adjoint ∘L D.F₁)) ≤
        N.gauge D.residual := by
  have hAdj : N.Mem D.residual.adjoint := N.adjoint_mem hR
  have hComp : N.Mem (D.residual.adjoint ∘L D.F₁) :=
    N.comp_right_mem D.F₁ hAdj
  refine ⟨N.neg_mem hComp, ?_⟩
  calc
    N.gauge (-(D.residual.adjoint ∘L D.F₁))
        = N.gauge (D.residual.adjoint ∘L D.F₁) := N.gauge_neg hComp
    _ ≤ N.gauge D.residual.adjoint :=
      N.gauge_comp_right_le D.F₁ hAdj (opNorm_le_one_of_isometry hF₁)
    _ = N.gauge D.residual := N.gauge_adjoint hR

end GenericCore

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
