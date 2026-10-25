/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
public import TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Basic

/-!
# Extended-real approximation-number sequences

This is the bridge from DKPS's real-valued approximation numbers to the `ℝ≥0∞` sequences consumed
by Tau Ceti's symmetric-gauge extension. The injectivity theorem below records a useful consequence
of the diagonal realization: agreement of two extended gauges on all Hilbert-space operators forces
agreement on every antitone sequence.
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
  ENNReal.ofReal (A.approximationNumber n)

theorem approxSeq_antitone {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : Antitone (approxSeq A) := by
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal (A.approximationNumber_antitone hmn)

/-- Equal symmetric-gauge values on all bounded Hilbert-space maps determine the extensions on
antitone nonnegative sequences. Bounded sequences are realized by diagonal operators; an
unbounded sequence has infinite extension for every symmetric gauge. -/
theorem symmetricGauge_eq_of_approxSeq_eq {Φ Ψ : SymmetricGauge}
    (h : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), Φ.extend (approxSeq A) = Ψ.extend (approxSeq A))
    {a : ℕ → ENNReal} (ha : Antitone a) : Φ.extend a = Ψ.extend a := by
  classical
  by_cases hbdd : ∃ B : NNReal, ∀ n, a n ≤ (B : ENNReal)
  · obtain ⟨B, hB⟩ := hbdd
    have hafin : ∀ n, a n ≠ ⊤ := fun n =>
      ne_top_of_le_ne_top (by simp) (hB n)
    have realize {L : Type} [RCLike L] (e : RCLikeIso L 𝕜) :
        Φ.extend a = Ψ.extend a := by
      let c : ℕ → L := fun n => ((a n).toReal : L)
      have hcnorm : ∀ n, ‖c n‖ = (a n).toReal := by
        intro n
        simp [c, abs_of_nonneg ENNReal.toReal_nonneg]
      have hB0 : (0 : ℝ) ≤ (B : ℝ) := B.coe_nonneg
      have hcB : ∀ n, ‖c n‖ ≤ (B : ℝ) := by
        intro n
        rw [hcnorm]
        exact (ENNReal.toReal_le_toReal (hafin n) (by simp)).2 (hB n)
      have hanti : Antitone fun n => ‖c n‖ := by
        intro i j hij
        simp only [hcnorm]
        exact (ENNReal.toReal_le_toReal (hafin j) (hafin i)).2 (ha hij)
      let H := ScalarTransport e (lp (fun _ : ℕ => L) 2)
      let Q : H →L[𝕜] H := ScalarTransport.clm (e := e) (diagOpLp c hB0 hcB)
      let ev : ULift.{v, 0} H ≃ₗᵢ[𝕜] H := LinearIsometryEquiv.ulift 𝕜 H
      let ew : H ≃ₗᵢ[𝕜] ULift.{w, 0} H :=
        (LinearIsometryEquiv.ulift 𝕜 H).symm
      let T : ULift.{v, 0} H →L[𝕜] ULift.{w, 0} H :=
        ew.toLinearIsometry.toContinuousLinearMap ∘L Q ∘L
          ev.toLinearIsometry.toContinuousLinearMap
      have hseq : approxSeq T = a := by
        funext n
        simp only [approxSeq, T, Q]
        rw [approximationNumber_eq_singularValue_toReal,
          singularValue_comp_linearIsometryEquiv,
          ← approximationNumber_eq_singularValue_toReal,
          ScalarTransport.approximationNumber_clm,
          approximationNumber_diagOpLp c hB0 hcB hanti n, hcnorm,
          ENNReal.ofReal_toReal (hafin n)]
      simpa only [hseq] using h T
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
    · exact realize (RCLikeIso.real hI).symm
    · exact realize (RCLikeIso.complex hI).symm
  · push Not at hbdd
    have hsup : (⨆ n, a n) = ⊤ := by
      refine iSup_eq_top.2 fun b hb => ?_
      lift b to NNReal using hb.ne
      obtain ⟨n, hn⟩ := hbdd b
      exact ⟨n, hn⟩
    have hinf : ∀ Theta : SymmetricGauge, Theta.extend a = ⊤ := fun Theta =>
      top_le_iff.1 (hsup ▸ Theta.iSup_le_extend a)
    rw [hinf Φ, hinf Ψ]

end TauCeti
