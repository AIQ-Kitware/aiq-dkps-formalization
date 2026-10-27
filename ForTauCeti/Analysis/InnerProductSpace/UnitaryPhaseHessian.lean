/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralVariation
public import ForTauCeti.Algebra.Star.ProjectionOverlap
public import TauCeti.Analysis.Calculus.DerivativeTest

/-!
# A common two-phase Hessian and overlap exclusion

A compressed derivative of a unitary spectral gradient gives the actual
two-compression Hessian of its cost. Overlap of the two high-phase
projections forces a negative paired second variation whenever one high
curvature is negative and the other is nonpositive. Thus local minimality
excludes overlap independently of the particular spectral penalty.

Formal provenance: the trace-compression calculation is adapted from
`SchattenTwoPhaseVariation`; the overlap argument is shared by the existing
`SchattenNoMixing` and `SmoothedNoMixing` proofs. The calculus and projection
identities are classical ingredients; this shared formulation makes no
historical-first claim. It is the operator mechanism for C1 in
`dev/spectral-transport-publication-core.md`, not the full decoupling theorem.
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- The actual cost Hessian follows from its trace-gradient first variation
and the compressed derivative of that gradient. Neither curvature sign nor
any optimality assumption is built into this calculus statement. -/
theorem hasDerivAt_deriv_unitary_cost_of_compressed_gradient
    (F : (E →L[ℂ] E) → ℝ) (G : (E →L[ℂ] E) → E →L[ℂ] E)
    (U : unitary (E →L[ℂ] E)) (H P : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (da db : ℝ)
    (hfirst : ∀ t : ℝ, HasDerivAt
      (fun s => F ((U : E →L[ℂ] E) * NormedSpace.exp (s • (Complex.I • H))))
      (LinearMap.trace ℂ E
        (G ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))) * H).toLinearMap).re t)
    (hgradient : HasDerivAt
      (fun t : ℝ => G ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))))
      ((da : ℂ) • ((1 - P) * H * (1 - P)) + (db : ℂ) • (P * H * P)) 0) :
    HasDerivAt
      (deriv (fun t : ℝ => F ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H)))))
      (da * (LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap).re +
       db * (LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap).re) 0 := by
  let D : E →L[ℂ] E :=
    (da : ℂ) • ((1 - P) * H * (1 - P)) + (db : ℂ) • (P * H * P)
  let tr : (E →L[ℂ] E) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((traceCLM ℂ E).restrictScalars ℝ)
  have htr (T : E →L[ℂ] E) : tr T = (LinearMap.trace ℂ E T.toLinearMap).re := by
    simp only [tr, ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
    exact congrArg Complex.re (traceCLM_apply T)
  have hd := tr.hasFDerivAt.comp_hasDerivAt 0 (hgradient.mul_const H)
  have hderiv : deriv (fun t : ℝ => F
      ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H)))) =
      (fun t => tr (G ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))) * H)) := by
    funext t
    rw [htr]
    exact (hfirst t).deriv
  change HasDerivAt (fun t => tr
    (G ((U : E →L[ℂ] E) * NormedSpace.exp (t • (Complex.I • H))) * H)) (tr (D * H)) 0 at hd
  rw [← hderiv] at hd
  apply hd.congr_deriv
  have hcomplex : LinearMap.trace ℂ E (D * H).toLinearMap =
      (da : ℂ) * LinearMap.trace ℂ E
        (((1 - P) * H * (1 - P)).adjoint * ((1 - P) * H * (1 - P))).toLinearMap +
      (db : ℂ) * LinearMap.trace ℂ E ((P * H * P).adjoint * (P * H * P)).toLinearMap := by
    dsimp only [D]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc,
      ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_smul,
      map_add, map_smul, map_smul,
      ContinuousLinearMap.trace_compression_mul_eq_trace_adjoint_square H (1 - P) hH hP.one_sub,
      ContinuousLinearMap.trace_compression_mul_eq_trace_adjoint_square H P hH hP]
    simp only [smul_eq_mul]
  rw [htr, hcomplex, Complex.add_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **The common no-overlap descent mechanism.** The lower compressions of
`AB+BA` vanish. Its high compressions detect any overlap, so negative high
curvature gives a strictly negative second variation of the actual paired
cost. The two low curvatures are arbitrary. -/
theorem exists_negative_second_variation_of_projection_overlap
    (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (A B : E →L[ℂ] E) (hA : IsStarProjection A) (hB : IsStarProjection B)
    (ca cb da db : ℝ) (hcb : cb < 0) (hdb : db ≤ 0)
    (hsecondA : HasDerivAt (deriv f)
      (ca * (LinearMap.trace ℂ E
        (((1 - A) * (A * B + B * A) * (1 - A)).adjoint *
          ((1 - A) * (A * B + B * A) * (1 - A))).toLinearMap).re +
       cb * (LinearMap.trace ℂ E
        ((A * (A * B + B * A) * A).adjoint * (A * (A * B + B * A) * A)).toLinearMap).re) 0)
    (hsecondB : HasDerivAt (deriv g)
      (da * (LinearMap.trace ℂ E
        (((1 - B) * (A * B + B * A) * (1 - B)).adjoint *
          ((1 - B) * (A * B + B * A) * (1 - B))).toLinearMap).re +
       db * (LinearMap.trace ℂ E
        ((B * (A * B + B * A) * B).adjoint * (B * (A * B + B * A) * B)).toLinearMap).re) 0)
    (hAB : A * B ≠ 0) :
    ∃ d < 0, HasDerivAt (deriv (fun t => f t + g t)) d 0 := by
  let X := A * B + B * A
  have hlowA : (1 - A) * X * (1 - A) = 0 :=
    projection_overlap_complement_compression hA.isIdempotentElem B
  have hlowB : (1 - B) * X * (1 - B) = 0 := by
    simpa only [X, add_comm] using projection_overlap_complement_compression hB.isIdempotentElem A
  have hhigh : A * X * A ≠ 0 := by
    change A * (A * B + B * A) * A ≠ 0
    rw [projection_overlap_compression hA.isIdempotentElem B]
    have hABA : A * B * A ≠ 0 := fun h =>
      hAB ((projection_compression_eq_zero_iff_mul_eq_zero hA hB).1 h)
    simpa only [two_nsmul, two_smul] using
      smul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hABA
  let a := (LinearMap.trace ℂ E ((A * X * A).adjoint * (A * X * A)).toLinearMap).re
  let b := (LinearMap.trace ℂ E ((B * X * B).adjoint * (B * X * B)).toLinearMap).re
  have ha : 0 < a := (ContinuousLinearMap.re_trace_adjoint_mul_self_pos_iff _).2 hhigh
  have hb : 0 ≤ b := ContinuousLinearMap.re_trace_adjoint_mul_self_nonneg _
  have hA' : HasDerivAt (deriv f) (cb * a) 0 := by
    simpa only [← show X = A * B + B * A from rfl, a, hlowA, map_zero, zero_mul,
      ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hsecondA
  have hB' : HasDerivAt (deriv g) (db * b) 0 := by
    simpa only [← show X = A * B + B * A from rfl, b, hlowB, map_zero, zero_mul,
      ContinuousLinearMap.toLinearMap_zero, Complex.zero_re, mul_zero, zero_add] using hsecondB
  have hderiv : deriv (fun t => f t + g t) = fun t => deriv f t + deriv g t := by
    funext t
    exact deriv_add (hf t) (hg t)
  refine ⟨cb * a + db * b,
    add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos hcb ha)
      (mul_nonpos_of_nonpos_of_nonneg hdb hb), ?_⟩
  rw [hderiv]
  exact hA'.add hB'

/-- A local minimum excludes overlap under the preceding actual Hessian
hypotheses. This is independent of the penalty's scalar formula. -/
theorem projection_overlap_eq_zero_of_paired_second_variations
    (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (A B : E →L[ℂ] E) (hA : IsStarProjection A) (hB : IsStarProjection B)
    (ca cb da db : ℝ) (hcb : cb < 0) (hdb : db ≤ 0)
    (hsecondA : HasDerivAt (deriv f)
      (ca * (LinearMap.trace ℂ E
        (((1 - A) * (A * B + B * A) * (1 - A)).adjoint *
          ((1 - A) * (A * B + B * A) * (1 - A))).toLinearMap).re +
       cb * (LinearMap.trace ℂ E
        ((A * (A * B + B * A) * A).adjoint * (A * (A * B + B * A) * A)).toLinearMap).re) 0)
    (hsecondB : HasDerivAt (deriv g)
      (da * (LinearMap.trace ℂ E
        (((1 - B) * (A * B + B * A) * (1 - B)).adjoint *
          ((1 - B) * (A * B + B * A) * (1 - B))).toLinearMap).re +
       db * (LinearMap.trace ℂ E
        ((B * (A * B + B * A) * B).adjoint * (B * (A * B + B * A) * B)).toLinearMap).re) 0)
    (hmin : IsLocalMin (fun t => f t + g t) 0) : A * B = 0 := by
  by_contra hAB
  obtain ⟨d, hd, hsecond⟩ := exists_negative_second_variation_of_projection_overlap
    f g hf hg A B hA hB ca cb da db hcb hdb hsecondA hsecondB hAB
  have hnonneg := deriv_deriv_nonneg_of_isLocalMin
    ((hf 0).continuousAt.add (hg 0).continuousAt) hmin
  change 0 ≤ deriv (deriv (fun t => f t + g t)) 0 at hnonneg
  rw [hsecond.deriv] at hnonneg
  exact (not_lt_of_ge hnonneg) hd

end TauCeti
