/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (exact configuration undetermined)
-/
module

public import DavisKahan.Sources.DavisKahan1970.Section8.Theorem82SourceUnbounded
public import DavisKahan.Sources.DavisKahan1970.SinTwoThetaCommonDomain
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ComplexRealBlocks

/-!
# Theorem 8.2 with only a bounded residual

The reference `A` and perturbed operator `T` may both be unbounded, with the same
self-adjoint domain. Only their difference on the reducing reference subspace is
required to extend to a bounded residual `R`. A bounded self-adjoint completion of
that residual replaces the full perturbation in the existing homotopy argument.
The finite reference spectral band supplies all trial-domain and Ritz data.

The norm interface retains `NormalizedUnitaryInvariantNorm`, including its
unconditional Fan-dominance assumption. The weaker norm comparisons are in
`Theorem82WhereDefinedNorms`; the operator-domain repair here does not assert
equivalence between the two norm classes.
-/

public section

open scoped InnerProductSpace
attribute [local instance] Submodule.completeSpace_coe_of_hasOrthogonalProjection

namespace TauCeti.DavisKahan1970.Section8

open TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe v

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

private theorem exists_bounded_selfAdjoint_of_symmetric_column
    {P : Submodule 𝕜 E} [P.HasOrthogonalProjection]
    (R : P →L[𝕜] E)
    (hsym : ∀ p q : P, ⟪R p, (q : E)⟫_𝕜 = ⟪(p : E), R q⟫_𝕜) :
    ∃ K : E →L[𝕜] E, K.IsSymmetric ∧ ∀ p : P, K (p : E) = R p := by
  let C : E →L[𝕜] E := R ∘L P.orthogonalProjectionOnto
  have hCp : ∀ p : P, C (p : E) = R p := by
    intro p
    change R (P.orthogonalProjectionOnto (p : E)) = R p
    congr 1
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr p.property
  have hCadj : ∀ p : P, C.adjoint (p : E) = P.starProjection (R p) := by
    intro p
    apply ext_inner_right 𝕜
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left]
    change ⟪(p : E), R (P.orthogonalProjectionOnto x)⟫_𝕜 = _
    rw [← hsym]
    change ⟪R p, P.starProjection x⟫_𝕜 = _
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_starProjection P)) (R p) x).symm
  have hPC : (P.starProjection ∘L C).IsSymmetric := by
    intro x y
    change ⟪P.starProjection (C x), y⟫_𝕜 = ⟪x, P.starProjection (C y)⟫_𝕜
    calc
      ⟪P.starProjection (C x), y⟫_𝕜 = ⟪C x, P.starProjection y⟫_𝕜 :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (isSelfAdjoint_starProjection P)) (C x) y
      _ = ⟪P.starProjection x, C y⟫_𝕜 := hsym _ _
      _ = ⟪x, P.starProjection (C y)⟫_𝕜 :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (isSelfAdjoint_starProjection P)) x (C y)
  refine ⟨C + C.adjoint - P.starProjection ∘L C, ?_, ?_⟩
  · intro x y
    change ⟪C x + C.adjoint x - P.starProjection (C x), y⟫_𝕜 =
      ⟪x, C y + C.adjoint y - P.starProjection (C y)⟫_𝕜
    simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    have hxy := hPC x y
    change ⟪P.starProjection (C x), y⟫_𝕜 = ⟪x, P.starProjection (C y)⟫_𝕜 at hxy
    rw [hxy]
    abel
  · intro p
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, hCp p, hCadj p]
    abel

private theorem exists_normPreserving_symmetric_column_completion_complex
    {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    {P : Submodule ℂ Hc} [P.HasOrthogonalProjection]
    (R : P →L[ℂ] Hc)
    (hsym : ∀ p q : P, ⟪R p, (q : Hc)⟫_ℂ = ⟪(p : Hc), R q⟫_ℂ) :
    ∃ K : Hc →L[ℂ] Hc, K.IsSymmetric ∧ (∀ p : P, K (p : Hc) = R p) ∧ ‖K‖ = ‖R‖ := by
  obtain ⟨K₀, hK₀, hcol₀⟩ := exists_bounded_selfAdjoint_of_symmetric_column R hsym
  obtain ⟨K, hK, hcol, hnorm⟩ := TauCeti.exists_selfAdjoint_completion_eqOn_of_norm_restriction
    K₀ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK₀) P
  have hrest : K₀ ∘L P.subtypeL = R := by ext p; exact hcol₀ p
  refine ⟨K, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK,
    fun p => (hcol p p.property).trans (hcol₀ p), ?_⟩
  rw [hnorm, ← TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection, hrest]

open TauCeti.RealComplexification in
private theorem exists_normPreserving_symmetric_column_completion_real
    {Er : Type*} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    {P : Submodule ℝ Er} [P.HasOrthogonalProjection]
    (R : P →L[ℝ] Er)
    (hsym : ∀ p q : P, ⟪R p, (q : Er)⟫_ℝ = ⟪(p : Er), R q⟫_ℝ) :
    ∃ K : Er →L[ℝ] Er, K.IsSymmetric ∧ (∀ p : P, K (p : Er) = R p) ∧ ‖K‖ = ‖R‖ := by
  obtain ⟨K₀, hK₀, hcol₀⟩ := exists_bounded_selfAdjoint_of_symmetric_column R hsym
  let PC := DavisKahan.Foundation.RealComplexification.complexifySubmodule P
  obtain ⟨KC, hKC, hcol, hnorm⟩ := TauCeti.exists_selfAdjoint_completion_eqOn_of_norm_restriction
    (complexify K₀) (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      ((complexify_isSymmetric_iff K₀).mpr hK₀)) PC
  have hrest : K₀ ∘L P.subtypeL = R := by ext p; exact hcol₀ p
  have hnormC : ‖KC‖ = ‖R‖ := by
    rw [hnorm, ← TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection,
      DavisKahan.Foundation.RealComplexification.norm_complexify_comp_subtypeL, hrest]
  have hrealcol : ∀ p : P, realPartOperator KC (p : Er) = R p := by
    intro p
    rw [realPartOperator_apply, hcol (ofReal (p : Er))
      ((DavisKahan.Foundation.RealComplexification.ofReal_mem_complexifySubmodule_iff P _).mpr
        p.property), complexify_ofReal, re_ofReal, hcol₀ p]
  refine ⟨realPartOperator KC, realPartOperator_isSymmetric KC hKC, hrealcol, ?_⟩
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
    intro x
    change ‖re (KC (ofReal x))‖ ≤ ‖R‖ * ‖x‖
    calc
      ‖re (KC (ofReal x))‖ ≤ ‖KC (ofReal x)‖ := norm_re_le _
      _ ≤ ‖KC‖ * ‖ofReal x‖ := KC.le_opNorm _
      _ = ‖R‖ * ‖x‖ := by rw [hnormC, ofReal.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound R (norm_nonneg _)
    intro p
    rw [← hrealcol p]
    exact (realPartOperator KC).le_opNorm (p : Er)

private theorem exists_modified_reference_of_commonDomain_residual
    {A T : E →ₗ.[𝕜] E} (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P : Submodule 𝕜 E} [P.HasOrthogonalProjection]
    (hP : _root_.LinearPMap.IsReducing A P)
    (hPdom : ∀ p : P, (p : E) ∈ A.domain)
    (R : P →L[𝕜] E)
    (hres : ∀ p : P, ∀ hp : (p : E) ∈ T.domain,
      T ⟨(p : E), hp⟩ = A ⟨(p : E), by rw [← hdom]; exact hp⟩ + R p)
    (K : E →L[𝕜] E) (hK : K.IsSymmetric)
    (hcol : ∀ p : P, K (p : E) = R p) :
    ∃ (A' : E →ₗ.[𝕜] E) (hP' : _root_.LinearPMap.IsReducing A' P),
      IsSelfAdjoint A' ∧ A'.restrict hP'.isInvariant = A.restrict hP.isInvariant ∧
      TauCeti.LinearPMap.addBounded A' K = T := by
  let A' := TauCeti.LinearPMap.addBounded T (-K)
  have hKneg : (-K).IsSymmetric := by
    intro x y
    change ⟪-K x, y⟫_𝕜 = ⟪x, -K y⟫_𝕜
    rw [inner_neg_left, inner_neg_right]
    exact congrArg Neg.neg (hK x y)
  have hA' : IsSelfAdjoint A' := DavisKahan.addBounded_isSelfAdjoint T hT (-K) hKneg
  have hPdomT : ∀ p : P, (p : E) ∈ T.domain := by
    intro p
    rw [hdom]
    exact hPdom p
  have hPdom' : ∀ p : P, (p : E) ∈ A'.domain := by
    intro p
    change (p : E) ∈ T.domain
    rw [hdom]
    exact hPdom p
  have hagree : ∀ p : P, A' ⟨(p : E), hPdom' p⟩ = A ⟨(p : E), hPdom p⟩ := by
    intro p
    change T ⟨(p : E), hPdomT p⟩ + (-K) (p : E) = A ⟨(p : E), hPdom p⟩
    rw [hres p (hPdomT p), neg_apply, hcol p]
    abel
  have hP' : _root_.LinearPMap.IsReducing A' P := by
    apply DavisKahan.reducesSubspace_of_isSelfAdjoint_of_invariant hA'
    · intro x
      exact hPdom' (P.orthogonalProjectionOnto (x : E))
    · rw [_root_.LinearPMap.isInvariant_iff]
      intro x hx
      have h := hagree ⟨(x : E), hx⟩
      rw [h]
      exact hP.isInvariant.apply_mem _ hx
  refine ⟨A', hP', hA', ?_, ?_⟩
  · refine LinearPMap.ext ?_ ?_
    · ext p
      rw [LinearPMap.mem_restrict_domain, LinearPMap.mem_restrict_domain]
      exact ⟨fun _ => hPdom p, fun _ => hPdom' p⟩
    · intro p hp hp'
      apply Subtype.ext
      rw [LinearPMap.coe_restrict_apply, LinearPMap.coe_restrict_apply]
      exact hagree p
  · change TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded T (-K)) K = T
    simpa only [neg_neg] using (TauCeti.LinearPMap.addBounded_neg_cancel T (-K))

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative over `ℂ`.**

The perturbation need only have a bounded residual on the reference subspace.
The full difference `T-A` is not required to be bounded. -/
theorem theorem8_2_residual_commonDomain_normalizedUIN_complex
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (N : TauCeti.DavisKahan.ExactSinTheta.NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A T : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing T Q)
    (hQspec : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.isInvariant) ⊆ Set.Icc beta alpha)
    (hQperp : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.orthogonal.isInvariant) ⊆ bandExterior beta alpha delta)
    (hPspec : _root_.LinearPMap.realSpectrum
      (A.restrict hPred.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (R : P →L[ℂ] H)
    (hres : ∀ p : P, ∀ hp : (p : H) ∈ T.domain,
      T ⟨(p : H), hp⟩ = A ⟨(p : H), by rw [← hdom]; exact hp⟩ + R p)
    (hsmall : ‖R‖ < delta / 2) (hRmem : N.Mem R) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ∧
      delta * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gauge R) ∧ sourceFullAngleLtC P Q (Real.pi / 4) := by
  obtain ⟨hPdom, M, hRitz⟩ :=
    exists_ritzBlock_of_realSpectrum_subset_Icc_complex hA hPred (by linarith) hPspec
  have hPdomT : ∀ p : P, (p : H) ∈ T.domain := by
    intro p
    rw [hdom]
    exact hPdom p
  have hsym : ∀ p q : P, ⟪R p, (q : H)⟫_ℂ = ⟪(p : H), R q⟫_ℂ := by
    intro p q
    have h := hT.isFormalAdjoint ⟨(p : H), hPdomT p⟩ ⟨(q : H), hPdomT q⟩
    rw [hres p (hPdomT p), hres q (hPdomT q), inner_add_left, inner_add_right] at h
    have hAinner := hA.isFormalAdjoint ⟨(p : H), hPdom p⟩ ⟨(q : H), hPdom q⟩
    rw [hAinner] at h
    exact add_left_cancel h
  obtain ⟨K, hK, hcol, hnorm⟩ :=
    exists_normPreserving_symmetric_column_completion_complex R hsym
  obtain ⟨A', hPred', hA', hrestrict, htotal⟩ :=
    exists_modified_reference_of_commonDomain_residual hT hdom hPred hPdom R hres K hK hcol
  have hQred' : _root_.LinearPMap.IsReducing (TauCeti.LinearPMap.addBounded A' K) Q := by
    rw [htotal]
    exact hQred
  have hQspec' : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A' K).restrict hQred'.isInvariant)
      ⊆ Set.Icc beta alpha := by simpa only [htotal] using hQspec
  have hQperp' : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A' K).restrict hQred'.orthogonal.isInvariant)
      ⊆ bandExterior beta alpha delta := by simpa only [htotal] using hQperp
  have hPspec' : _root_.LinearPMap.realSpectrum (A'.restrict hPred'.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2) := by
    rw [hrestrict]
    exact hPspec
  have hKsmall : ‖K‖ < delta / 2 := by
    rw [hnorm]
    exact hsmall
  refine ⟨?_, ?_⟩
  · have hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
        (T.restrict hQred.isInvariant) (T.restrict hQred.orthogonal.isInvariant) delta :=
      .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
    have hresRitz : ∀ p : P, T ⟨(p : H), hPdomT p⟩ = R p + ((M p : P) : H) := by
      intro p
      rw [hres p (hPdomT p), hRitz p]
      abel
    exact normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos hRmem
      fun Msnf hM =>
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex
          Msnf hT hQred hPdomT hresRitz hdelta hgap hM
  · exact (sourceFullAngleLtC_iff_maximalAngle_lt P Q (by positivity)).2
      (theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex
        hA' K hK hdelta hab hPred' hQred' hQspec' hQperp' hPspec' hcross hKsmall)

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative over `ℝ`.**

The perturbation need only have a bounded residual on the reference subspace.
The full difference `T-A` is not required to be bounded. -/
theorem theorem8_2_residual_commonDomain_normalizedUIN_real
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (N : TauCeti.DavisKahan.ExactSinTheta.NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A T : H →ₗ.[ℝ] H} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule ℝ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing T Q)
    (hQspec : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.isInvariant) ⊆ Set.Icc beta alpha)
    (hQperp : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.orthogonal.isInvariant) ⊆ bandExterior beta alpha delta)
    (hPspec : _root_.LinearPMap.realSpectrum
      (A.restrict hPred.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (R : P →L[ℝ] H)
    (hres : ∀ p : P, ∀ hp : (p : H) ∈ T.domain,
      T ⟨(p : H), hp⟩ = A ⟨(p : H), by rw [← hdom]; exact hp⟩ + R p)
    (hsmall : ‖R‖ < delta / 2) (hRmem : N.Mem R) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ∧
      delta * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gauge R) ∧ sourceFullAngleLtR P Q (Real.pi / 4) := by
  obtain ⟨hPdom, M, hRitz⟩ :=
    exists_ritzBlock_of_realSpectrum_subset_Icc_real hA hPred (by linarith) hPspec
  have hPdomT : ∀ p : P, (p : H) ∈ T.domain := by
    intro p
    rw [hdom]
    exact hPdom p
  have hsym : ∀ p q : P, ⟪R p, (q : H)⟫_ℝ = ⟪(p : H), R q⟫_ℝ := by
    intro p q
    have h := hT.isFormalAdjoint ⟨(p : H), hPdomT p⟩ ⟨(q : H), hPdomT q⟩
    rw [hres p (hPdomT p), hres q (hPdomT q), inner_add_left, inner_add_right] at h
    have hAinner := hA.isFormalAdjoint ⟨(p : H), hPdom p⟩ ⟨(q : H), hPdom q⟩
    rw [hAinner] at h
    exact add_left_cancel h
  obtain ⟨K, hK, hcol, hnorm⟩ :=
    exists_normPreserving_symmetric_column_completion_real R hsym
  obtain ⟨A', hPred', hA', hrestrict, htotal⟩ :=
    exists_modified_reference_of_commonDomain_residual hT hdom hPred hPdom R hres K hK hcol
  have hQred' : _root_.LinearPMap.IsReducing (TauCeti.LinearPMap.addBounded A' K) Q := by
    rw [htotal]
    exact hQred
  have hQspec' : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A' K).restrict hQred'.isInvariant)
      ⊆ Set.Icc beta alpha := by simpa only [htotal] using hQspec
  have hQperp' : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A' K).restrict hQred'.orthogonal.isInvariant)
      ⊆ bandExterior beta alpha delta := by simpa only [htotal] using hQperp
  have hPspec' : _root_.LinearPMap.realSpectrum (A'.restrict hPred'.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2) := by
    rw [hrestrict]
    exact hPspec
  have hKsmall : ‖K‖ < delta / 2 := by
    rw [hnorm]
    exact hsmall
  refine ⟨?_, ?_⟩
  · have hgap : TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap
        (T.restrict hQred.isInvariant) (T.restrict hQred.orthogonal.isInvariant) delta :=
      .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
    have hresRitz : ∀ p : P, T ⟨(p : H), hPdomT p⟩ = R p + ((M p : P) : H) := by
      intro p
      rw [hres p (hPdomT p), hRitz p]
      abel
    exact normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos hRmem
      fun Msnf hM =>
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real
          Msnf hT hQred hPdomT hresRitz hdelta hgap hM
  · exact (sourceFullAngleLtR_iff_maximalAngle_lt P Q (by positivity)).2
      (theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real
        hA' K hK hdelta hab hPred' hQred' hQspec' hQperp' hPspec' hcross hKsmall)

/-- The residual-only acute-branch conclusion has no ideal-norm hypothesis. -/
theorem theorem8_2_residual_commonDomain_fullAngle_lt_complex
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {A T : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing T Q)
    (hQspec : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.isInvariant) ⊆ Set.Icc beta alpha)
    (hQperp : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.orthogonal.isInvariant) ⊆ bandExterior beta alpha delta)
    (hPspec : _root_.LinearPMap.realSpectrum
      (A.restrict hPred.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (R : P →L[ℂ] H)
    (hres : ∀ p : P, ∀ hp : (p : H) ∈ T.domain,
      T ⟨(p : H), hp⟩ = A ⟨(p : H), by rw [← hdom]; exact hp⟩ + R p)
    (hsmall : ‖R‖ < delta / 2) :
    sourceFullAngleLtC P Q (Real.pi / 4) := by
  exact (theorem8_2_residual_commonDomain_normalizedUIN_complex
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) 1 (by decide))
    hA hT hdom hdelta hab hPred hQred hQspec hQperp hPspec hcross R hres hsmall
    (mem_kyFanNormalizedUnitaryInvariantNorm 1 (by decide) R)).2

/-- The residual-only acute-branch conclusion has no ideal-norm hypothesis. -/
theorem theorem8_2_residual_commonDomain_fullAngle_lt_real
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {A T : H →ₗ.[ℝ] H} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule ℝ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing T Q)
    (hQspec : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.isInvariant) ⊆ Set.Icc beta alpha)
    (hQperp : _root_.LinearPMap.realSpectrum
      (T.restrict hQred.orthogonal.isInvariant) ⊆ bandExterior beta alpha delta)
    (hPspec : _root_.LinearPMap.realSpectrum
      (A.restrict hPred.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (R : P →L[ℝ] H)
    (hres : ∀ p : P, ∀ hp : (p : H) ∈ T.domain,
      T ⟨(p : H), hp⟩ = A ⟨(p : H), by rw [← hdom]; exact hp⟩ + R p)
    (hsmall : ‖R‖ < delta / 2) :
    sourceFullAngleLtR P Q (Real.pi / 4) := by
  exact (theorem8_2_residual_commonDomain_normalizedUIN_real
    (kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℝ) 1 (by decide))
    hA hT hdom hdelta hab hPred hQred hQspec hQperp hPspec hcross R hres hsmall
    (mem_kyFanNormalizedUnitaryInvariantNorm 1 (by decide) R)).2

end
end TauCeti.DavisKahan1970.Section8
