/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge.Faithfulness
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
public import TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Basic

/-!
# Extended-real approximation-number sequences

This is the bridge from DKPS's real-valued approximation numbers to the `ℝ≥0∞` sequences consumed
by Tau Ceti's symmetric-gauge extension. The accepted faithfulness theorem determines the
extension from the operator-ideal family.
The adapter below preserves arbitrary scalar and carrier universes by transporting operators
through a real/complex scalar isomorphism and universe lifts.
-/

public section

open scoped ENNReal

universe u v w z

namespace TauCeti

open ContinuousLinearMap

variable {𝕜 : Type u} [RCLike 𝕜]

noncomputable local instance uliftInnerProductSpace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    InnerProductSpace 𝕜 (ULift.{z} E) where
  inner x y := inner 𝕜 x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := 𝕜) x.down
  conj_inner_symm x y := inner_conj_symm (𝕜 := 𝕜) x.down y.down
  add_left x y z := inner_add_left (𝕜 := 𝕜) x.down y.down z.down
  smul_left x y r := inner_smul_left (𝕜 := 𝕜) x.down y.down r

/-- The approximation-number sequence of a bounded operator, in `ℝ≥0∞`. -/
noncomputable def approxSeq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((A.singularValue n : ℝ))

theorem approxSeq_antitone {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : Antitone (approxSeq A) := by
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal ((NNReal.coe_mono.comp_antitone
      (ContinuousLinearMap.antitone_singularValue A)) hmn)

/-- Equal symmetric-gauge values on all bounded Hilbert-space maps determine the extensions on
antitone nonnegative sequences. Scalar transport and universe lifts reduce the original
statement to accepted operator-ideal-family faithfulness, without restricting its universes. -/
theorem symmetricGauge_eq_of_approxSeq_eq {Φ Ψ : SymmetricGauge}
    (h : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), Φ.extend (approxSeq A) = Ψ.extend (approxSeq A))
    {a : ℕ → ENNReal} (ha : Antitone a) : Φ.extend a = Ψ.extend a := by
  have transfer {L : Type} [RCLike L] (e : RCLikeIso L 𝕜) :
      Φ.operatorIdealFamily.{0, 0, 0} L = Ψ.operatorIdealFamily.{0, 0, 0} L := by
    apply OperatorIdealFamily.ext
    intro E F _ _ _ _ _ _ A
    let H := ScalarTransport e E
    let K := ScalarTransport e F
    let ev : ULift.{v, 0} H ≃ₗᵢ[𝕜] H := LinearIsometryEquiv.ulift 𝕜 H
    let ew : K ≃ₗᵢ[𝕜] ULift.{w, 0} K :=
      (LinearIsometryEquiv.ulift 𝕜 K).symm
    let T : ULift.{v, 0} H →L[𝕜] ULift.{w, 0} K :=
      ew.toLinearIsometry.toContinuousLinearMap ∘L ScalarTransport.clm (e := e) A ∘L
        ev.toLinearIsometry.toContinuousLinearMap
    have hs : approxSeq T = (fun n => (A.singularValue n : ENNReal)) := by
      funext n
      simp only [approxSeq, T]
      rw [singularValue_comp_linearIsometryEquiv, ScalarTransport.approximationNumber_clm]
      exact ENNReal.ofReal_coe_nnreal
    have hT := h T
    rw [hs] at hT
    simpa only [SymmetricGauge.operatorIdealFamily_gauge, SymmetricGauge.opGauge_def] using hT
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · exact SymmetricGauge.extend_eq_of_operatorIdealFamily_eq
      (transfer (RCLikeIso.real hI).symm) ha
  · exact SymmetricGauge.extend_eq_of_operatorIdealFamily_eq
      (transfer (RCLikeIso.complex hI).symm) ha

end TauCeti
