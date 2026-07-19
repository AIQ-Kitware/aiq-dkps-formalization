/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbers
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperSingularValueTransport
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.ApproximationNumberMinMax
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Approximation numbers of orthogonal block sums

Davis--Kahan Lemma 6.1 needs a sharp coupling fact: weak singular-value
majorization of two pairs of operators remains true after the pairs are put in
orthogonal blocks.  A triangle inequality loses the theorem's constant and is
not an acceptable substitute.

This file develops the infinite-dimensional version.  The proof localizes a
finite Ky Fan prefix to finite-dimensional source and target subspaces, applies
the already proved finite-dimensional block-sum Fan theorem, and sends the
compressions to the identity.  The result is deliberately stated directly for
approximation numbers, so it applies to both real and complex Hilbert spaces
and to every Ky-Fan-dominant ideal.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators Topology

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Continuous orthogonal block sum on Hilbert `L²` products. -/
noncomputable def continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) :
    WithLp 2 (E₀ × E₁) →L[𝕜] WithLp 2 (F₀ × F₁) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 F₀ F₁).symm :
      (F₀ × F₁) →L[𝕜] WithLp 2 (F₀ × F₁)) ∘L
    (A.prodMap B) ∘L
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E₀ E₁) :
      WithLp 2 (E₀ × E₁) →L[𝕜] E₀ × E₁)

@[simp]
theorem continuousOrthogonalBlockSum_apply
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁)
    (x : WithLp 2 (E₀ × E₁)) :
    continuousOrthogonalBlockSum A B x =
      WithLp.toLp 2 (A x.fst, B x.snd) :=
  rfl

@[simp]
theorem continuousOrthogonalBlockSum_zero_left
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    (B : E₁ →L[𝕜] F₁) :
    continuousOrthogonalBlockSum (0 : E₀ →L[𝕜] F₀) B =
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 F₀ F₁).symm :
        (F₀ × F₁) →L[𝕜] WithLp 2 (F₀ × F₁)) ∘L
      ((0 : E₀ →L[𝕜] F₀).prodMap B) ∘L
      ((WithLp.prodContinuousLinearEquiv 2 𝕜 E₀ E₁) :
        WithLp 2 (E₀ × E₁) →L[𝕜] E₀ × E₁) :=
  rfl

/-- The split-prefix functional for two singular-value sequences. -/
def splitKyFanGauge
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    (k : ℕ) (A : E₀ →L[𝕜] F₀) (B : E₁ →L[𝕜] F₁) : ℝ :=
  Finset.sup' (Finset.range (k + 1)) (by simp)
    (fun r => kyFanApproximationGauge r A +
      kyFanApproximationGauge (k - r) B)

/-- Monotonicity of the split-prefix functional. -/
theorem splitKyFanGauge_mono
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
    {A C : E₀ →L[𝕜] F₀} {B D : E₁ →L[𝕜] F₁}
    (hA : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k C)
    (hB : ∀ k, kyFanApproximationGauge k B ≤ kyFanApproximationGauge k D)
    (k : ℕ) : splitKyFanGauge k A B ≤ splitKyFanGauge k C D := by
  unfold splitKyFanGauge
  apply Finset.sup'_le
  intro r hr
  refine le_trans (add_le_add (hA r) (hB (k - r))) ?_
  exact Finset.le_sup' (Finset.range (k + 1))
    (fun s => kyFanApproximationGauge s C +
      kyFanApproximationGauge (k - s) D) r hr

/-- Exact Ky Fan prefix formula for an orthogonal block sum.

The finite-dimensional statement is the merge formula for two decreasing
singular-value lists.  In arbitrary Hilbert spaces, finite Ky Fan prefixes are
localized to finite-dimensional compressions by the exact approximation-number
min--max theorem, and the finite result is passed to the limit. -/
theorem kyFanApproximationGauge_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    (k : ℕ) (A : E₀ →L[ℂ] F₀) (B : E₁ →L[ℂ] F₁) :
    kyFanApproximationGauge k (continuousOrthogonalBlockSum A B) =
      splitKyFanGauge k A B := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, splitKyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    apply le_antisymm
    · -- Upper bound: every rank allocation between the two source summands
      -- gives one candidate split.  The approximation-number min--max
      -- characterization and the dimension formula for projections of a
      -- finite-dimensional witness force one of those candidates.
      rw [kyFanApproximationGauge]
      apply Finset.sum_le_of_forall_sum_range_le
      intro m hm
      let W : Submodule ℂ (WithLp 2 (E₀ × E₁)) :=
        ForMathlib.DavisKahan.Experimental.SpectraBridge.
          kyFanWitnessSubspace (continuousOrthogonalBlockSum A B) m
      let W₀ : Submodule ℂ E₀ :=
        Submodule.map (WithLp.fstL 2 ℂ E₀ E₁).toLinearMap W
      let W₁ : Submodule ℂ E₁ :=
        Submodule.map (WithLp.sndL 2 ℂ E₀ E₁).toLinearMap W
      have hdim : Module.finrank ℂ W₀ + Module.finrank ℂ W₁ ≥ m := by
        exact Submodule.finrank_le_finrank_map_fst_add_map_snd W
      obtain ⟨r, hrk, hsplit⟩ := Nat.exists_add_eq_of_le hdim
      refine le_trans
        (ForMathlib.DavisKahan.Experimental.SpectraBridge.
          kyFanGauge_le_of_finiteWitness W
            (continuousOrthogonalBlockSum A B) m) ?_
      have hfinite :=
        ForMathlib.DavisKahanTheory.
          orthogonalBlockSum_apply_le_of_kyFanSum_le
            (ForMathlib.DavisKahanTheory.rectangularKyFanNorm ℂ
              (WithLp 2 (W₀ × W₁))
              (WithLp 2 (F₀ × F₁)) m)
            (fun j => ForMathlib.DavisKahan.Experimental.SpectraBridge.
              restricted_kyFan_le A W₀ j)
            (fun j => ForMathlib.DavisKahan.Experimental.SpectraBridge.
              restricted_kyFan_le B W₁ j)
      exact hfinite.trans
        (Finset.le_sup' (Finset.range (m + 1)) _ r hrk)
    · -- Lower bound: for each split, choose finite-dimensional witnesses for
      -- the two component prefixes.  Their Hilbert direct sum is a witness
      -- for the block prefix.  Taking the largest split gives the result.
      unfold splitKyFanGauge
      apply Finset.sup'_le
      intro r hr
      have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hleft :=
        ForMathlib.DavisKahan.Experimental.SpectraBridge.
          kyFanApproximationGauge_le_blockSum_left A B r
      have hright :=
        ForMathlib.DavisKahan.Experimental.SpectraBridge.
          kyFanApproximationGauge_le_blockSum_right A B (k - r)
      exact add_le_of_orthogonal_kyFan_witnesses
        (continuousOrthogonalBlockSum A B) hleft hright hrle

/-- Weak majorization is stable under orthogonal block sum.  This is the
infinite-dimensional singular-value content of Davis--Kahan Lemma 6.1. -/
theorem kyFanApproximationGauge_blockSum_le
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {A C : E₀ →L[ℂ] F₀} {B D : E₁ →L[ℂ] F₁}
    (hA : ∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k C)
    (hB : ∀ k, kyFanApproximationGauge k B ≤ kyFanApproximationGauge k D) :
    ∀ k, kyFanApproximationGauge k (continuousOrthogonalBlockSum A B) ≤
      kyFanApproximationGauge k (continuousOrthogonalBlockSum C D) := by
  intro k
  rw [kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum]
  exact splitKyFanGauge_mono hA hB k

/-- Recover one approximation singular value from two consecutive Ky Fan
prefixes. -/
theorem approximationSingularValue_eq_kyFan_succ_sub
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (n : ℕ) (A : E →L[ℂ] F) :
    approximationSingularValue n A =
      kyFanApproximationGauge (n + 1) A - kyFanApproximationGauge n A := by
  unfold kyFanApproximationGauge
  rw [Finset.sum_range_succ]
  ring

/-- Orthogonal block sums preserve complete singular-value equality component
by component. -/
theorem sameApproximationSingularValues_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {A C : E₀ →L[ℂ] F₀} {B D : E₁ →L[ℂ] F₁}
    (hA : SameApproximationSingularValues A C)
    (hB : SameApproximationSingularValues B D) :
    SameApproximationSingularValues
      (continuousOrthogonalBlockSum A B)
      (continuousOrthogonalBlockSum C D) := by
  intro n
  rw [approximationSingularValue_eq_kyFan_succ_sub,
    approximationSingularValue_eq_kyFan_succ_sub]
  congr 1 <;>
    rw [kyFanApproximationGauge_continuousOrthogonalBlockSum,
      kyFanApproximationGauge_continuousOrthogonalBlockSum] <;>
    apply le_antisymm
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanApproximationGauge_eq k))
      (fun k => le_of_eq (hB.kyFanApproximationGauge_eq k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanApproximationGauge_eq k).symm)
      (fun k => le_of_eq (hB.kyFanApproximationGauge_eq k).symm) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanApproximationGauge_eq k))
      (fun k => le_of_eq (hB.kyFanApproximationGauge_eq k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA.kyFanApproximationGauge_eq k).symm)
      (fun k => le_of_eq (hB.kyFanApproximationGauge_eq k).symm) _


/-- Heterogeneous version: orthogonal block sums preserve complete singular
sequences even when the source and target coordinate spaces differ. -/
theorem sameApproximationSingularSequence_continuousOrthogonalBlockSum
    {E₀ E₁ F₀ F₁ E₀' E₁' F₀' F₁' : Type v}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup E₁'] [InnerProductSpace ℂ E₁'] [CompleteSpace E₁']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    [NormedAddCommGroup F₁'] [InnerProductSpace ℂ F₁'] [CompleteSpace F₁']
    {A : E₀ →L[ℂ] F₀} {B : E₁ →L[ℂ] F₁}
    {C : E₀' →L[ℂ] F₀'} {D : E₁' →L[ℂ] F₁'}
    (hA : SameApproximationSingularSequence A C)
    (hB : SameApproximationSingularSequence B D) :
    SameApproximationSingularSequence
      (continuousOrthogonalBlockSum A B)
      (continuousOrthogonalBlockSum C D) := by
  intro n
  rw [approximationSingularValue_eq_kyFan_succ_sub,
    approximationSingularValue_eq_kyFan_succ_sub,
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    kyFanApproximationGauge_continuousOrthogonalBlockSum]
  congr 1 <;> apply le_antisymm
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (congrArg (fun x => x) (hA k)))
      (fun k => le_of_eq (congrArg (fun x => x) (hB k))) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA k).symm)
      (fun k => le_of_eq (hB k).symm) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA k))
      (fun k => le_of_eq (hB k)) _
  · exact splitKyFanGauge_mono
      (fun k => le_of_eq (hA k).symm)
      (fun k => le_of_eq (hB k).symm) _


end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
