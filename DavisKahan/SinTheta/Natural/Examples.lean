/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Natural.Bounded
import DavisKahan.SinTheta.Natural.Reducing
import DavisKahan.SinTheta.Natural.GapConvenience
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Compile-only usage examples for the natural sine-theta API

These examples are regression tests for theorem usability. They instantiate the
ordinary operator-norm ideal family, exercise both scalar fields, and include a
finite-dimensional zero-residual model whose exact subspace is the whole
ambient space. The latter has an empty complementary block, hence an ordered
positive gap for every positive separation.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace NaturalExamples

noncomputable section

open TauCeti.DavisKahanExt

universe v

section AbstractComplexUse

open SpectraBridge

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

example
    (A : ClosedOperator (𝕜 := ℂ) (E := E)) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : ClosedOperator (𝕜 := ℂ) (E := F)) (hA0 : A0.IsSelfAdjoint)
    (X Rop : F →L[ℂ] E) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ - X (A0.toLinearMap x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuineUnboundedSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * ‖(ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion A hA S hS ∘L
          (selfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X‖ ≤
      ‖Rop‖ := by
  have hmain := sinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℂ))
      A hA S hS A0 hA0 X Rop hX hXdom hReq hδ hgap trivial
  exact hmain.2

/-- The same natural theorem instantiated with the nontrivial two-term Ky Fan
gauge rather than the operator norm. -/
example
    (A : ClosedOperator (𝕜 := ℂ) (E := E)) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : ClosedOperator (𝕜 := ℂ) (E := F)) (hA0 : A0.IsSelfAdjoint)
    (X Rop : F →L[ℂ] E) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ - X (A0.toLinearMap x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuineUnboundedSylvesterGap A0
      (selfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * kyFanApproximationGauge 2
        ((ContinuousLinearMap.id ℂ E -
          selfAdjointSpectralSubspaceInclusion A hA S hS ∘L
            (selfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X)
      ≤ kyFanApproximationGauge 2 Rop := by
  have hk : 0 < (2 : ℕ) := by omega
  let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) 2 hk
  have hmain := sinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap
    N A hA S hS A0 hA0 X Rop hX hXdom hReq hδ hgap
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) 2 hk Rop)
  simpa only [N, KyFanDominantIdealFamily.kyFan_gauge] using hmain.2

end AbstractComplexUse

section AbstractRealUse

open SpectraBridge.RealSpectralRestriction

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

example
    (A : ClosedOperator (𝕜 := ℝ) (E := E)) (hA : A.IsSelfAdjoint)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : ClosedOperator (𝕜 := ℝ) (E := F)) (hA0 : A0.IsSelfAdjoint)
    (X Rop : F →L[ℝ] E) (hX : IsometricEmbedding X)
    (hXdom : ∀ x : A0.domain, X (x : F) ∈ A.domain)
    (hReq : ∀ x : A0.domain,
      A.toLinearMap ⟨X (x : F), hXdom x⟩ - X (A0.toLinearMap x) = Rop (x : F))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap A0
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ) :
    δ * ‖(ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralSubspaceInclusion A hA S hS ∘L
          (realSelfAdjointSpectralSubspaceInclusion A hA S hS).adjoint) ∘L X‖ ≤
      ‖Rop‖ := by
  have hmain := sinTheta_unbounded_real_spectralSubspace
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ))
      A hA S hS A0 hA0 X Rop hX hXdom hReq hδ hgap trivial
  exact hmain.2

end AbstractRealUse

section AbstractBoundedUse

open SpectraBridge

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The bounded convenience theorem removes every domain-side argument. -/
example
    (A : E →L[ℂ] E) (hA : A.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S)
    (A0 : F →L[ℂ] F) (hA0 : A0.IsSymmetric)
    (X : F →L[ℂ] E) (hX : IsometricEmbedding X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : GenuineUnboundedSylvesterGap
      (ClosedOperator.ofBounded A0)
      (selfAdjointSpectralRestriction (ClosedOperator.ofBounded A)
        (ClosedOperator.ofBounded_isSelfAdjoint A hA) Sᶜ hS.compl) δ) :
    δ * ‖(ContinuousLinearMap.id ℂ E -
        selfAdjointSpectralSubspaceInclusion (ClosedOperator.ofBounded A)
          (ClosedOperator.ofBounded_isSelfAdjoint A hA) S hS ∘L
        (selfAdjointSpectralSubspaceInclusion (ClosedOperator.ofBounded A)
          (ClosedOperator.ofBounded_isSelfAdjoint A hA) S hS).adjoint) ∘L X‖
      ≤ ‖generalResidual A X A0‖ := by
  have hmain := sinTheta_bounded_spectralSubspace_of_genuineSpectrumGap
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℂ))
      A hA S hS A0 hA0 X hX hδ hgap trivial
  exact hmain.2

end AbstractBoundedUse

section FiniteRealModel

abbrev RealPlane := EuclideanSpace ℝ (Fin 2)

/-- A concrete finite-dimensional, zero-residual use of the natural reducing
API. The whole plane is the exact subspace and the complementary block is the
zero Hilbert space. -/
theorem realPlane_zeroResidual_model :
    let A : ClosedOperator (𝕜 := ℝ) (E := RealPlane) :=
      ClosedOperator.ofBounded (0 : RealPlane →L[ℝ] RealPlane)
    let A0 : ClosedOperator (𝕜 := ℝ) (E := RealPlane) :=
      ClosedOperator.ofBounded (0 : RealPlane →L[ℝ] RealPlane)
    let U : Submodule ℝ RealPlane := ⊤
    let X : RealPlane →L[ℝ] RealPlane := ContinuousLinearMap.id ℝ RealPlane
    let Rop : RealPlane →L[ℝ] RealPlane := 0
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)).toRectangularSymmetricIdealFamily.Mem
      ((ContinuousLinearMap.id ℝ RealPlane - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X) ∧
      1 * (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)).toRectangularSymmetricIdealFamily.gauge
        ((ContinuousLinearMap.id ℝ RealPlane - U.subtypeL ∘L U.subtypeL.adjoint) ∘L X)
      ≤ (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ)).toRectangularSymmetricIdealFamily.gauge Rop := by
  dsimp
  let A : ClosedOperator (𝕜 := ℝ) (E := RealPlane) :=
    ClosedOperator.ofBounded (0 : RealPlane →L[ℝ] RealPlane)
  let A0 : ClosedOperator (𝕜 := ℝ) (E := RealPlane) :=
    ClosedOperator.ofBounded (0 : RealPlane →L[ℝ] RealPlane)
  let U : Submodule ℝ RealPlane := ⊤
  have hred : A.ReducesSubspace U := by
    simp [A, U, ClosedOperator.ReducesSubspace,
      ClosedOperator.InvariantSubspace]
    rfl
  have hA : A.IsSelfAdjoint := by
    exact ClosedOperator.ofBounded_isSelfAdjoint
      (0 : RealPlane →L[ℝ] RealPlane) (by intro x y; simp)
  have hA0 : A0.IsSelfAdjoint := by
    exact ClosedOperator.ofBounded_isSelfAdjoint
      (0 : RealPlane →L[ℝ] RealPlane) (by intro x y; simp)
  have hA0upper : SemiboundedAbove A0 0 := by
    intro x
    show RCLike.re
      ⟪(0 : RealPlane →L[ℝ] RealPlane) (x : RealPlane), (x : RealPlane)⟫_ℝ ≤ _
    simp
  have hcompLower : SemiboundedBelow
      (ClosedOperator.reducingRestriction A Uᗮ hred.orthogonal) 1 := by
    intro x
    have hzero : ((x.1 : RealPlane)) = 0 :=
      inner_self_eq_zero.mp
        (Submodule.inner_right_of_mem_orthogonal (K := U) Submodule.mem_top x.1.2)
    have hx : x = 0 := Subtype.ext (Subtype.ext hzero)
    rw [hx]
    simp
  have hgap : UnboundedSylvesterGap A0
      (ClosedOperator.reducingRestriction A Uᗮ hred.orthogonal) 1 := by
    exact UnboundedSylvesterGap.trialBelow_complementAbove hA0upper
      (by simpa using hcompLower)
  apply sinTheta_unbounded_real_reducingSubspace
    (KyFanDominantIdealFamily.operatorNorm (𝕜 := ℝ))
      A hA U hred A0 hA0
      (ContinuousLinearMap.id ℝ RealPlane) 0 (fun _ => rfl)
  case hXdom => exact fun x => Submodule.mem_top
  case hReq =>
    intro x
    show (0 : RealPlane) - (0 : RealPlane) = (0 : RealPlane)
    simp
  case hδ => exact zero_lt_one
  case hgap => exact hgap
  case hR => trivial

end FiniteRealModel

end

end NaturalExamples
end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti