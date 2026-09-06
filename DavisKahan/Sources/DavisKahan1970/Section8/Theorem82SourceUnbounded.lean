/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section8.Theorem82UnboundedPath
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedAngle

/-!
# Theorem 8.2 as one source-facing theorem, at unbounded ambient scope

Davis and Kahan state Theorem 8.2 as a single theorem: add to the hypotheses of
the `sin 2θ` theorem either `‖H‖ < δ/2` or `‖R‖ < δ/2`, assume
`spec(A₀) ⊆ [β − δ/2, α + δ/2]`, and then **both** conclusions hold — the
double-angle estimate remains valid, *and* the comparison is on the acute branch.

The four theorems below are that theorem, one per alternative and scalar field,
at the ambient scope Section 8 inherits: `A` is a possibly unbounded self-adjoint
partial map and `H` is a bounded self-adjoint perturbation.  They are façades.
Each conclusion is an existing theorem:

* the retained perturbation estimate is
  `sinTwoTheta_ambient_unbounded_perturbedGap_sourceExact_{complex,real}`, the
  Section 2 endpoint, with the printed spectral placement converted to the
  `FormBoundedSylvesterGap` it takes by `intervalExterior`;
* the retained residual estimate is
  `sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_{complex,real}`
  lifted to an arbitrary normalized unitarily invariant norm the same way the
  Section 2 endpoint is;
* the acute conclusion is
  `theorem8_2_{perturbation,residual}HalfGap_maximalAngle_lt_unbounded_{complex,real}`.

## The residual

In Section 8's context `P` reduces `A`, so the Ritz block of the trial subspace
`P` is `A₀ = A|_P` and the residual of `P` for `A + H` is `R = H|_P`.  The
residual branch below takes the `sin 2θ` theorem's own residual data `(M, R)`
with its defining equation, plus the source's identification of `M` as the block
`A₀`; `R = H ∘ P.subtypeL` is then forced, which is what the acute half consumes.
Nothing about `R` is assumed beyond the printed `‖R‖ < δ/2`.
-/

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open TauCeti.DavisKahan.Sylvester
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe v

/-! ### The perturbation alternative -/

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, at the printed
source scope over `ℂ`.**

`A` is self-adjoint and possibly unbounded, `H` bounded self-adjoint, `P` reduces
`A`, `Q` reduces `A + H` with the printed spectral placement, `A₀`'s spectrum
lies in the central band `[β − δ/2, α + δ/2]`, and `‖H‖ < δ/2`.  Then the
double-angle estimate is retained and the comparison is on the acute branch. -/
theorem theorem8_2_perturbation_sourceExact_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : DavisKahan.IsSelfAdjointOperator Hop)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2)
    (hHmem : N.Mem Hop) :
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gauge Hop) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine ⟨?_, theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex hA Hop hHop
    hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall⟩
  exact sinTwoTheta_ambient_unbounded_perturbedGap_sourceExact_complex N hA Hop hHop
    hPred hQred hdelta (.intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)) hHmem

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, at the printed
source scope over `ℝ`.** -/
theorem theorem8_2_perturbation_sourceExact_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : DavisKahan.IsSelfAdjointOperator Hop)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2)
    (hHmem : N.Mem Hop) :
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gauge Hop) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine ⟨?_, theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real hA Hop hHop
    hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall⟩
  exact sinTwoTheta_ambient_unbounded_perturbedGap_sourceExact_real N hA Hop hHop
    hPred hQred hdelta (.intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)) hHmem

/-! ### The residual alternative -/

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, at the printed source
scope over `ℂ`.**

The smallness hypothesis is the printed `‖R‖ < δ/2` on the residual itself, and
does not become `‖H‖ < δ/2`. -/
theorem theorem8_2_residual_sourceExact_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : DavisKahan.IsSelfAdjointOperator Hop)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    {M : P →L[ℂ] P} {R : P →L[ℂ] Hc}
    (hPdom : ∀ v : P, (v : Hc) ∈ A.domain)
    (hRitz : ∀ v : P, ((M v : P) : Hc) = A ⟨(v : Hc), hPdom v⟩)
    (hres : ∀ v : P, TauCeti.LinearPMap.addBounded A Hop ⟨(v : Hc), hPdom v⟩
      = R v + ((M v : P) : Hc))
    (hsmall : ‖R‖ < delta / 2)
    (hRmem : N.Mem R) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gauge R) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) delta :=
    .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
  -- the residual is `H` restricted to `P`, because `M` is the block `A₀`
  have hReq : Hop ∘L (P.subtypeL : P →L[ℂ] Hc) = R := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h := hres v
    rw [TauCeti.LinearPMap.addBounded_apply, hRitz v] at h
    have := add_right_cancel (a := Hop (v : Hc)) (b := (A ⟨(v : Hc), hPdom v⟩ : Hc))
      (c := R v) (by rw [add_comm]; exact h)
    exact this
  refine ⟨?_, ?_⟩
  · exact normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos hRmem
      fun Msnf hM =>
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex Msnf
          hAH hQred hPdom hres hdelta hgap hM
  · refine theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_complex hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross ?_
    rw [hReq]
    exact hsmall

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, at the printed source
scope over `ℝ`.** -/
theorem theorem8_2_residual_sourceExact_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : DavisKahan.IsSelfAdjointOperator Hop)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    {M : P →L[ℝ] P} {R : P →L[ℝ] Er}
    (hPdom : ∀ v : P, (v : Er) ∈ A.domain)
    (hRitz : ∀ v : P, ((M v : P) : Er) = A ⟨(v : Er), hPdom v⟩)
    (hres : ∀ v : P, TauCeti.LinearPMap.addBounded A Hop ⟨(v : Er), hPdom v⟩
      = R v + ((M v : P) : Er))
    (hsmall : ‖R‖ < delta / 2)
    (hRmem : N.Mem R) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gauge R) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) delta :=
    .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
  have hReq : Hop ∘L (P.subtypeL : P →L[ℝ] Er) = R := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h := hres v
    rw [TauCeti.LinearPMap.addBounded_apply, hRitz v] at h
    have := add_right_cancel (a := Hop (v : Er)) (b := (A ⟨(v : Er), hPdom v⟩ : Er))
      (c := R v) (by rw [add_comm]; exact h)
    exact this
  refine ⟨?_, ?_⟩
  · exact normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos hRmem
      fun Msnf hM =>
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real Msnf
          hAH hQred hPdom hres hdelta hgap hM
  · refine theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_real hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross ?_
    rw [hReq]
    exact hsmall

end

end Section8
end DavisKahan1970
end TauCeti
