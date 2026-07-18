/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SpectralRestriction
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.GapResolvent
import Spectra.Operator.KatoRellich

/-!
# Bounded-perturbation adapter for the unbounded sine-theta theorem

This module removes two pieces of provisional plumbing from the route to the
classical unbounded perturbation statement.

First, Spectra's bounded Kato--Rellich theorem proves that `A + V`, on the
original domain of a self-adjoint closed operator `A`, is self-adjoint whenever
`V` is bounded and self-adjoint.

Second, `boundedPerturbationSinThetaData` packages exact and trial spectral
blocks into `UnboundedSinThetaData`.  The residual is automatically `V X`.
The resulting theorem reduces the desired perturbation estimate to construction
of the two spectral restrictions and their intertwining maps; no ideal or
Halmos machinery is used.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open ForMathlib.DavisKahan.Experimental.ExactSinTheta

universe v

variable {H F G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The DK bounded sum is exactly Spectra's partial-map perturbation. -/
theorem toLinearPMap_addBounded_eq_perturbedOp
    (A : DKClosedOperator (H := H)) (V : H →L[ℂ] H) :
    (A.addBounded V).toLinearPMap =
      Spectra.Operator.perturbedOp A.toLinearPMap
        (V.comp (Submodule.subtypeL A.domain)).toLinearMap := by
  refine LinearPMap.ext_iff.mpr ⟨rfl, ?_⟩
  intro x hx hy
  rfl

/-- Bounded Kato--Rellich for the DK closed-operator wrapper, proved through
its canonical `LinearPMap` representation. -/
theorem addBounded_isSelfAdjoint
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (V : H →L[ℂ] H) (hV : IsSelfAdjointOperator V) :
    (A.addBounded V).IsSelfAdjoint := by
  have hV' : _root_.IsSelfAdjoint V :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hV
  change _root_.IsSelfAdjoint (A.addBounded V).toLinearPMap
  rw [toLinearPMap_addBounded_eq_perturbedOp]
  exact Spectra.Operator.kato_rellich_bounded hA hV'

/-- Package a bounded perturbation and two invariant block embeddings as the
paper-shaped unbounded residual data.  The residual identity is automatic and
has residual `V ∘ X`. -/
noncomputable def boundedPerturbationSinThetaData
    (A : DKClosedOperator (H := H)) (V : H →L[ℂ] H)
    (A₀ : DKClosedOperator (H := F)) (Λ₁ : DKClosedOperator (H := G))
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ = X (A₀.toLinearMap x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (A.addBounded V).toLinearMap ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁.toLinearMap y)) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := H) (F := F) (G := G) where
  A := A.addBounded V
  A₀ := A₀
  Λ₁ := Λ₁
  X := X
  F₁ := F₁
  residual := V ∘L X
  X_maps_domain := hXdom
  F₁_maps_domain := hF₁dom
  residual_eq := by
    intro x
    change
      (A.toLinearMap ⟨X (x : F), hXdom x⟩ + V (X (x : F))) -
          X (A₀.toLinearMap x) =
        V (X (x : F))
    rw [hXintertwines x]
    abel
  intertwines := hF₁intertwines

/-- The projected adjoint residual of a bounded perturbation is no larger than
`V` when both block embeddings are contractions. -/
theorem boundedPerturbation_adjointResidual_opNorm_le
    (V : H →L[ℂ] H) (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hX : ‖X‖ ≤ 1) (hF₁ : ‖F₁‖ ≤ 1) :
    ‖(V ∘L X).adjoint ∘L F₁‖ ≤ ‖V‖ := by
  calc
    ‖(V ∘L X).adjoint ∘L F₁‖
        ≤ ‖(V ∘L X).adjoint‖ * ‖F₁‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖V ∘L X‖ * ‖F₁‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ (‖V‖ * ‖X‖) * ‖F₁‖ :=
          mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (‖V‖ * 1) * ‖F₁‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX (norm_nonneg V)) (norm_nonneg F₁)
    _ ≤ (‖V‖ * 1) * 1 :=
          mul_le_mul_of_nonneg_left hF₁
            (mul_nonneg (norm_nonneg V) zero_le_one)
    _ = ‖V‖ := by ring

/-- Bounded-perturbation specialization of the genuine-spectrum unbounded
sine-theta theorem.  The only remaining block-specific inputs are the two
self-adjoint restricted operators, their domain-aware intertwining maps, and
the interval/exterior spectral hypotheses. -/
theorem sinTheta_addBounded_opNorm_of_spectrum_gap
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (V : H →L[ℂ] H) (hV : IsSelfAdjointOperator V)
    (A₀ : DKClosedOperator (H := F)) (hA₀ : A₀.IsSelfAdjoint)
    (Λ₁ : DKClosedOperator (H := G)) (hΛ₁ : Λ₁.IsSelfAdjoint)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ = X (A₀.toLinearMap x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (A.addBounded V).toLinearMap ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁.toLinearMap y))
    (hXnorm : ‖X‖ ≤ 1) (hF₁norm : ‖F₁‖ ≤ 1)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow A₀ β) (hA₀high : SemiboundedAbove A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum Λ₁.toLinearPMap) :
    δ * ‖X.adjoint ∘L F₁‖ ≤ ‖V‖ := by
  let D := boundedPerturbationSinThetaData A V A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : D.A.IsSelfAdjoint := by
    change (A.addBounded V).IsSelfAdjoint
    exact addBounded_isSelfAdjoint A hA V hV
  have hraw := sinTheta_unbounded_opNorm_of_spectrum_gap D hD hA₀ hΛ₁
    hβα hδ hA₀low hA₀high hΛspec
  have hraw' :
      δ * ‖X.adjoint ∘L F₁‖ ≤ ‖(V ∘L X).adjoint ∘L F₁‖ := by
    change δ * ‖X.adjoint ∘L F₁‖ ≤ ‖(V ∘L X).adjoint ∘L F₁‖ at hraw
    exact hraw
  have hres := boundedPerturbation_adjointResidual_opNorm_le V X F₁
    hXnorm hF₁norm
  exact hraw'.trans hres

/-- Isometric-embedding form of
`sinTheta_addBounded_opNorm_of_spectrum_gap`. -/
theorem sinTheta_addBounded_opNorm_of_spectrum_gap_isometric
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (V : H →L[ℂ] H) (hV : IsSelfAdjointOperator V)
    (A₀ : DKClosedOperator (H := F)) (hA₀ : A₀.IsSelfAdjoint)
    (Λ₁ : DKClosedOperator (H := G)) (hΛ₁ : Λ₁.IsSelfAdjoint)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ = X (A₀.toLinearMap x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (A.addBounded V).toLinearMap ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁.toLinearMap y))
    (hXiso : IsometricEmbedding X) (hF₁iso : IsometricEmbedding F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow A₀ β) (hA₀high : SemiboundedAbove A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      lam ∉ Spectra.Resolvent.spectrum Λ₁.toLinearPMap) :
    δ * ‖X.adjoint ∘L F₁‖ ≤ ‖V‖ := by
  exact sinTheta_addBounded_opNorm_of_spectrum_gap A hA V hV
    A₀ hA₀ Λ₁ hΛ₁ X F₁ hXdom hXintertwines hF₁dom hF₁intertwines
    (opNorm_le_one_of_isometry hXiso) (opNorm_le_one_of_isometry hF₁iso)
    hβα hδ hA₀low hA₀high hΛspec

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
