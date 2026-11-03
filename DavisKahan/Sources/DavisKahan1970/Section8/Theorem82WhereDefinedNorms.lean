/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (exact configuration undetermined)
-/
module
public import DavisKahan.Sources.DavisKahan1970.Ideals.WhereDefinedNormTransfer
public import DavisKahan.Sources.DavisKahan1970.Section8.Theorem82CommonDomain

/-!
# Theorem 8.2 with where-defined unitary-invariant norms

The acute-branch conclusion is independent of the ideal norm. Each numerical
inequality uses the weaker normalized symmetric family and requires its two
displayed norms to exist. The residual alternative retains common-domain
unbounded operators and does not require bounded full perturbation.
-/
public section
namespace TauCeti.DavisKahan1970.Section8
open TauCeti TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Angle TauCeti.DavisKahan.Sylvester
open scoped InnerProductSpace
attribute [local instance] Submodule.completeSpace_coe_of_hasOrthogonalProjection
noncomputable section
universe u v

section perturbationcomplex

/-- Theorem 8.2, perturbation alternative, with the source where-defined norm convention. -/
theorem theorem8_2_perturbation_whereDefinedUIN_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A Hop).restrict hQred.isInvariant)
      ⊆ Set.Icc beta alpha)
    (hQperp : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A Hop).restrict
        hQred.orthogonal.isInvariant) ⊆ bandExterior beta alpha delta)
    (hPspec : _root_.LinearPMap.realSpectrum
      (A.restrict hPred.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2) :
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) → N.Mem Hop →
      delta * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal Hop) ∧
      sourceFullAngleLtC P Q (Real.pi / 4) := by
  refine ⟨?_, ?_⟩
  · exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N hdelta two_pos
      (X := TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) (Y := Hop) fun M hM =>
        (theorem8_2_perturbation_sourceExact_unbounded_complex M hA Hop hHop
          hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall hM).1
  · apply (sourceFullAngleLtC_iff_maximalAngle_lt P Q (by positivity)).2
    exact theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex
      hA Hop hHop hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall
end perturbationcomplex

section residualcomplex

/-- Theorem 8.2, residual alternative, with the source where-defined norm convention. -/
theorem theorem8_2_residual_commonDomain_whereDefinedUIN_complex
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (N : TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
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
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) → N.Mem R →
      delta * N.gaugeReal (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal R) ∧
      sourceFullAngleLtC P Q (Real.pi / 4) := by
  refine ⟨?_, theorem8_2_residual_commonDomain_fullAngle_lt_complex
    hA hT hdom hdelta hab hPred hQred hQspec hQperp hPspec hcross R hres hsmall⟩
  exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N hdelta two_pos
    (X := (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q)) (Y := R) fun M hM =>
      (theorem8_2_residual_commonDomain_normalizedUIN_complex M hA hT hdom
        hdelta hab hPred hQred hQspec hQperp hPspec hcross R hres hsmall hM).1
end residualcomplex

section perturbationreal

/-- Theorem 8.2, perturbation alternative, with the source where-defined norm convention. -/
theorem theorem8_2_perturbation_whereDefinedUIN_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : _root_.LinearPMap.IsReducing A P)
    (hQred : _root_.LinearPMap.IsReducing
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A Hop).restrict hQred.isInvariant)
      ⊆ Set.Icc beta alpha)
    (hQperp : _root_.LinearPMap.realSpectrum
      ((TauCeti.LinearPMap.addBounded A Hop).restrict
        hQred.orthogonal.isInvariant) ⊆ bandExterior beta alpha delta)
    (hPspec : _root_.LinearPMap.realSpectrum
      (A.restrict hPred.isInvariant)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2) :
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) → N.Mem Hop →
      delta * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal Hop) ∧
      sourceFullAngleLtR P Q (Real.pi / 4) := by
  refine ⟨?_, ?_⟩
  · exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N hdelta two_pos
      (X := TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) (Y := Hop) fun M hM =>
        (theorem8_2_perturbation_sourceExact_unbounded_real M hA Hop hHop
          hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall hM).1
  · apply (sourceFullAngleLtR_iff_maximalAngle_lt P Q (by positivity)).2
    exact theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real
      hA Hop hHop hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall
end perturbationreal

section residualreal

/-- Theorem 8.2, residual alternative, with the source where-defined norm convention. -/
theorem theorem8_2_residual_commonDomain_whereDefinedUIN_real
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (N : TauCeti.DavisKahan.ExactSinTheta.NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
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
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) → N.Mem R →
      delta * N.gaugeReal (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gaugeReal R) ∧
      sourceFullAngleLtR P Q (Real.pi / 4) := by
  refine ⟨?_, theorem8_2_residual_commonDomain_fullAngle_lt_real
    hA hT hdom hdelta hab hPred hQred hQspec hQperp hPspec hcross R hres hsmall⟩
  exact whereDefinedUIN_of_normalizedUnitaryInvariant_mul N hdelta two_pos
    (X := (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q)) (Y := R) fun M hM =>
      (theorem8_2_residual_commonDomain_normalizedUIN_real M hA hT hdom
        hdelta hab hPred hQred hQspec hQperp hPspec hcross R hres hsmall hM).1
end residualreal

end
end TauCeti.DavisKahan1970.Section8
