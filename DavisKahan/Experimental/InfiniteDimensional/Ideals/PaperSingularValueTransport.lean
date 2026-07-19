/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbers

/-!
# Complete singular-value transport for the paper-facing sine operators

Davis--Kahan Theorem 6.1 permits `sin Θ₀` to be any operator with the same
complete singular-value sequence as the canonical cross-projection block.
In infinite dimensions the zero-based approximation numbers are the stable
replacement for the finite singular-value list. This module proves that equal
approximation-number sequences give exactly the same membership and gauge in
every Ky-Fan-dominant unitarily invariant ideal family.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Operators between possibly different Hilbert spaces have the same complete
singular-value sequence.  This is the relation used literally in the paper. -/
def SameApproximationSingularSequence
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₂) : Prop :=
  ∀ n : ℕ, approximationSingularValue n A = approximationSingularValue n B

namespace SameApproximationSingularSequence

@[refl]
theorem refl
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : SameApproximationSingularSequence A A := fun _ => rfl

@[symm]
theorem symm
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    SameApproximationSingularSequence B A := fun n => (h n).symm

@[trans]
theorem trans
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ E₃ F₃ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃] [CompleteSpace E₃]
    [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃] [CompleteSpace F₃]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂} {C : E₃ →L[𝕜] F₃}
    (hAB : SameApproximationSingularSequence A B)
    (hBC : SameApproximationSingularSequence B C) :
    SameApproximationSingularSequence A C := fun n => (hAB n).trans (hBC n)

/-- Equal complete singular data gives equal operator norms. -/
theorem opNorm_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) : ‖A‖ = ‖B‖ := by
  rw [← approximationSingularValue_zero A,
    ← approximationSingularValue_zero B, h 0]

/-- Equal complete singular data gives equal finite Ky Fan sums. -/
theorem kyFanApproximationGauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) (k : ℕ) :
    kyFanApproximationGauge k A = kyFanApproximationGauge k B := by
  unfold kyFanApproximationGauge
  apply Finset.sum_congr rfl
  intro n hn
  exact h n

end SameApproximationSingularSequence


/-- Two rectangular bounded operators have the same complete singular-value
data when all of their approximation singular values agree. -/
def SameApproximationSingularValues (A B : E →L[𝕜] F) : Prop :=
  SameApproximationSingularSequence A B

namespace SameApproximationSingularValues

/-- Two-sided composition by isometric equivalences preserves every
approximation singular value. -/
theorem comp_isometricEquiv
    {A : E →L[𝕜] F}
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    SameApproximationSingularValues
      (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
        V.toContinuousLinearEquiv.toContinuousLinearMap) A := by
  intro n
  apply le_antisymm
  · have hleft := congrArg (fun x : NNReal => (x : ℝ))
      ((A ∘L V.toContinuousLinearEquiv.toContinuousLinearMap).
        approximationNumber_comp_left_le
          U.toContinuousLinearEquiv.toContinuousLinearMap n)
    have hright := congrArg (fun x : NNReal => (x : ℝ))
      (A.approximationNumber_comp_right_le
        V.toContinuousLinearEquiv.toContinuousLinearMap n)
    simpa [approximationSingularValue,
      U.toContinuousLinearEquiv.isometry.norm_toContinuousLinearMap,
      V.toContinuousLinearEquiv.isometry.norm_toContinuousLinearMap] using
      hleft.trans hright
  · let Uinv := U.symm
    let Vinv := V.symm
    have hfactor :
        Uinv.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          (U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
            V.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
          Vinv.toContinuousLinearEquiv.toContinuousLinearMap = A := by
      ext x
      simp [Uinv, Vinv]
    rw [← hfactor]
    have hleft := congrArg (fun x : NNReal => (x : ℝ))
      (((U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
          V.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
          Vinv.toContinuousLinearEquiv.toContinuousLinearMap).
        approximationNumber_comp_left_le
          Uinv.toContinuousLinearEquiv.toContinuousLinearMap n)
    have hright := congrArg (fun x : NNReal => (x : ℝ))
      ((U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
          V.toContinuousLinearEquiv.toContinuousLinearMap).
        approximationNumber_comp_right_le
          Vinv.toContinuousLinearEquiv.toContinuousLinearMap n)
    simpa [approximationSingularValue, Uinv, Vinv,
      U.symm.toContinuousLinearEquiv.isometry.norm_toContinuousLinearMap,
      V.symm.toContinuousLinearEquiv.isometry.norm_toContinuousLinearMap] using
      hleft.trans hright

/-- If an operator becomes another operator after unitary coordinate changes,
they have the same complete singular sequence. -/
theorem of_isometricEquiv_comp
    {E' F' : Type v}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
    (U : F ≃ₗᵢ[𝕜] F') (V : E ≃ₗᵢ[𝕜] E')
    {A : E →L[𝕜] F} {B : E' →L[𝕜] F'}
    (h : U.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
      V.symm.toContinuousLinearEquiv.toContinuousLinearMap = B) :
    SameApproximationSingularSequence A B := by
  intro n
  apply le_antisymm
  · have hback :
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L B ∘L
          V.toContinuousLinearEquiv.toContinuousLinearMap = A := by
      rw [← h]
      ext x
      simp
    rw [← hback]
    have hleft := congrArg (fun x : NNReal => (x : ℝ))
      ((B ∘L V.toContinuousLinearEquiv.toContinuousLinearMap).
        approximationNumber_comp_left_le
          U.symm.toContinuousLinearEquiv.toContinuousLinearMap n)
    have hright := congrArg (fun x : NNReal => (x : ℝ))
      (B.approximationNumber_comp_right_le
        V.toContinuousLinearEquiv.toContinuousLinearMap n)
    simpa [approximationSingularValue] using hleft.trans hright
  · rw [← h]
    have hleft := congrArg (fun x : NNReal => (x : ℝ))
      ((A ∘L V.symm.toContinuousLinearEquiv.toContinuousLinearMap).
        approximationNumber_comp_left_le
          U.toContinuousLinearEquiv.toContinuousLinearMap n)
    have hright := congrArg (fun x : NNReal => (x : ℝ))
      (A.approximationNumber_comp_right_le
        V.symm.toContinuousLinearEquiv.toContinuousLinearMap n)
    simpa [approximationSingularValue] using hleft.trans hright

@[refl]
theorem refl (A : E →L[𝕜] F) : SameApproximationSingularValues A A :=
  fun _ => rfl

@[symm]
theorem symm {A B : E →L[𝕜] F}
    (h : SameApproximationSingularValues A B) :
    SameApproximationSingularValues B A :=
  fun n => (h n).symm

@[trans]
theorem trans {A B C : E →L[𝕜] F}
    (hAB : SameApproximationSingularValues A B)
    (hBC : SameApproximationSingularValues B C) :
    SameApproximationSingularValues A C :=
  fun n => (hAB n).trans (hBC n)

/-- Equal complete singular-value data gives equal finite Ky Fan gauges. -/
theorem kyFanApproximationGauge_eq {A B : E →L[𝕜] F}
    (h : SameApproximationSingularValues A B) (k : ℕ) :
    kyFanApproximationGauge k A = kyFanApproximationGauge k B := by
  unfold kyFanApproximationGauge
  exact Finset.sum_congr rfl fun n _ => h n

/-- Transport ideal membership and exact gauge equality along complete
singular-value equality. -/
theorem mem_and_gauge_eq
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (h : SameApproximationSingularValues A B)
    (hB : N.toRectangularSymmetricIdealFamily.Mem B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      N.toRectangularSymmetricIdealFamily.gauge A =
        N.toRectangularSymmetricIdealFamily.gauge B := by
  let M := N.toRectangularSymmetricIdealFamily
  have hAB : ∀ k, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B := fun k =>
    le_of_eq (h.kyFanApproximationGauge_eq k)
  obtain ⟨hA, hleAB⟩ := N.majorization_mem_and_gauge_le hB hAB
  have hBA : ∀ k, kyFanApproximationGauge k B ≤
      kyFanApproximationGauge k A := fun k =>
    le_of_eq (h.kyFanApproximationGauge_eq k).symm
  obtain ⟨_, hleBA⟩ := N.majorization_mem_and_gauge_le hA hBA
  exact ⟨hA, le_antisymm hleAB hleBA⟩

/-- Transfer a sharp scalar gauge estimate to any operator with the same
complete singular-value sequence. -/
theorem mem_and_mul_gauge_le
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    {A B C : E →L[𝕜] F} {c : ℝ}
    (h : SameApproximationSingularValues A B)
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (hbound : c * N.toRectangularSymmetricIdealFamily.gauge B ≤
      N.toRectangularSymmetricIdealFamily.gauge C) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      c * N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge C := by
  obtain ⟨hA, hgauge⟩ := h.mem_and_gauge_eq N hB
  refine ⟨hA, ?_⟩
  rw [hgauge]
  exact hbound

end SameApproximationSingularValues

/-- Literal source packaging of the freedom in `sin Theta_0`.  The chosen
representative may act between different Hilbert coordinate spaces, exactly as
in the paper; only its complete singular-value sequence is prescribed. -/
structure PaperSinThetaRepresentativeAcross
    {E₀ F₀ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    (canonical : E →L[𝕜] F) where
  operator : E₀ →L[𝕜] F₀
  same_singular_sequence :
    SameApproximationSingularSequence operator canonical

namespace PaperSinThetaRepresentativeAcross

/-- The canonical operator is an admissible representative. -/
noncomputable def canonical (A : E →L[𝕜] F) :
    PaperSinThetaRepresentativeAcross A where
  operator := A
  same_singular_sequence := .refl A

end PaperSinThetaRepresentativeAcross

/-- Paper-facing packaging of the freedom in the definition of `sin Θ₀`:
the chosen operator has exactly the complete singular-value sequence of the
canonical directed sine block. -/
structure PaperSinThetaRepresentative (canonical : E →L[𝕜] F) where
  operator : E →L[𝕜] F
  same_singular_values : SameApproximationSingularValues operator canonical

namespace PaperSinThetaRepresentative

/-- The canonical block is itself an admissible paper representative. -/
noncomputable def canonical (A : E →L[𝕜] F) :
    PaperSinThetaRepresentative A where
  operator := A
  same_singular_values := .refl A

/-- Every paper representative has exactly the same ideal membership and
gauge as the canonical block. -/
theorem mem_and_gauge_eq
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    {canonical : E →L[𝕜] F}
    (S : PaperSinThetaRepresentative canonical)
    (hcanonical : N.toRectangularSymmetricIdealFamily.Mem canonical) :
    N.toRectangularSymmetricIdealFamily.Mem S.operator ∧
      N.toRectangularSymmetricIdealFamily.gauge S.operator =
        N.toRectangularSymmetricIdealFamily.gauge canonical :=
  S.same_singular_values.mem_and_gauge_eq N hcanonical

end PaperSinThetaRepresentative

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
