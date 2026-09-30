/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.TanThetaScalarGeneric
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaScalarGeneric
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaCommonDomain
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedAngle
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import DavisKahan.OperatorIdeal.ComplexificationApproximation
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.TangentTransfer
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
import ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-!
# Literal directed trigonometric presentation objects

The Section 2 directed tangent and directed double-angle sine estimates were
proved using representatives that are convenient for the analytic argument:

* `tan Theta_0` was represented by an arbitrary rectangular operator with the
  prescribed complete approximation-number sequence;
* `sin 2 Theta_0` was represented by the positive product
  `2 sin Theta_0 cos Theta_0`.

Those are useful proof APIs, but they are not the literal functional-calculus
expressions printed in Davis--Kahan.  This module adds the presentation layer:

`Theta_0 = arcsin (directedSinAngleOperator U V)`,

`tan Theta_0 = cfc tan Theta_0`, and

`sin 2 Theta_0 = cfc (fun t => sin (2*t)) Theta_0`.

The tangent theorem is transported from the rectangular representative through
an explicit equality of complete approximation-number sequences.  The doubled
sine is stronger: its literal CFC object is proved *equal as an operator* to the
existing positive `2 sin Theta_0 cos Theta_0` object.  That exact equality is
important at the where-defined norm boundary, where matching singular values
alone does not transfer ideal membership.
-/

open scoped InnerProductSpace BigOperators TauCeti.CompleteSubspace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.Angle
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.DavisKahan.Sylvester
open TauCeti.DavisKahan.RealSpectralRestriction
open TauCeti.RealComplexification

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

noncomputable section

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]

/-- The zero-extended source-directed angle `Theta_0` for an ordered pair of
subspaces.  It is reconstructed from the positive directed sine on the
canonical interval `[0, pi/2]`.

The extension is zero on the orthogonal complement of the source subspace;
this does not alter the directed singular-value sequence and makes the object
an endomorphism of the ambient Hilbert space. -/
noncomputable def sourceDirectedSubspaceThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[K] E :=
  cfc Real.arcsin (directedSinAngleOperator U V)

/-- The literal directed `tan Theta_0`: tangent applied by continuous
functional calculus to the source-directed angle. -/
noncomputable def sourceDirectedTanThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[K] E :=
  cfc Real.tan (sourceDirectedSubspaceThetaOperator U V)

/-- The literal directed `sin 2 Theta_0`: the scalar function
`t |-> sin (2*t)` applied to the source-directed angle. -/
noncomputable def sourceDirectedSinTwoThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[K] E :=
  cfc (fun t : Real => Real.sin (2 * t)) (sourceDirectedSubspaceThetaOperator U V)

/-- The literal directed `tan 2 Theta_0`: the scalar function
`t |-> tan (2*t)` applied to the source-directed angle. -/
noncomputable def sourceDirectedTanTwoThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    E →L[K] E :=
  cfc (fun t : Real => Real.tan (2 * t)) (sourceDirectedSubspaceThetaOperator U V)

/-- The reconstructed directed angle is self-adjoint. -/
theorem isSelfAdjoint_sourceDirectedSubspaceThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sourceDirectedSubspaceThetaOperator U V) := by
  rw [sourceDirectedSubspaceThetaOperator]
  exact cfc_predicate Real.arcsin (directedSinAngleOperator U V)

/-- The literal directed tangent is self-adjoint. -/
theorem isSelfAdjoint_sourceDirectedTanThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sourceDirectedTanThetaOperator U V) := by
  rw [sourceDirectedTanThetaOperator]
  exact cfc_predicate Real.tan (sourceDirectedSubspaceThetaOperator U V)

/-- The literal directed doubled sine is self-adjoint. -/
theorem isSelfAdjoint_sourceDirectedSinTwoThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sourceDirectedSinTwoThetaOperator U V) := by
  rw [sourceDirectedSinTwoThetaOperator]
  exact cfc_predicate (fun t : Real => Real.sin (2 * t))
    (sourceDirectedSubspaceThetaOperator U V)

/-- The literal directed doubled tangent is self-adjoint. -/
theorem isSelfAdjoint_sourceDirectedTanTwoThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sourceDirectedTanTwoThetaOperator U V) := by
  rw [sourceDirectedTanTwoThetaOperator]
  exact cfc_predicate (fun t : Real => Real.tan (2 * t))
    (sourceDirectedSubspaceThetaOperator U V)

private theorem norm_directedSinAngleOperator_le_one
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖directedSinAngleOperator U V‖ ≤ 1 := by
  rw [directedSinAngleOperator, ContinuousLinearMap.norm_modulus]
  calc
    ‖Vᗮ.starProjection ∘L U.starProjection‖
        ≤ ‖Vᗮ.starProjection‖ * ‖U.starProjection‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
      mul_le_mul Vᗮ.starProjection_norm_le U.starProjection_norm_le
        (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- The positive directed sine has spectrum in the canonical interval. -/
theorem spectrum_directedSinAngleOperator_subset_Icc
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum Real (directedSinAngleOperator U V) ⊆ Set.Icc 0 1 := by
  intro x hx
  have hx0 : 0 ≤ x :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg
      (R := Real) _ (isSelfAdjoint_directedSinAngleOperator U V)).mp
        (directedSinAngleOperator_nonneg U V) x hx
  have hnormK : ‖((x : K))‖ ≤
      ‖directedSinAngleOperator U V‖ * ‖(1 : E →L[K] E)‖ :=
    spectrum.norm_le_norm_mul_of_mem hx
  have hnorm : |x| ≤
      ‖directedSinAngleOperator U V‖ * ‖(1 : E →L[K] E)‖ := by
    rwa [RCLike.norm_ofReal] at hnormK
  have hone : ‖(1 : E →L[K] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have habs : |x| ≤ ‖directedSinAngleOperator U V‖ := by
    calc
      |x| ≤ ‖directedSinAngleOperator U V‖ * ‖(1 : E →L[K] E)‖ := hnorm
      _ ≤ ‖directedSinAngleOperator U V‖ * 1 :=
        mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = ‖directedSinAngleOperator U V‖ := mul_one _
  exact ⟨hx0, ((le_abs_self x).trans habs).trans
    (norm_directedSinAngleOperator_le_one U V)⟩

/-- The reconstructed source-directed angle has spectrum in `[0, pi/2]`. -/
theorem spectrum_sourceDirectedSubspaceThetaOperator_subset_Icc
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum Real (sourceDirectedSubspaceThetaOperator U V) ⊆
      Set.Icc 0 (Real.pi / 2) := by
  intro y hy
  rw [sourceDirectedSubspaceThetaOperator,
    cfc_map_spectrum (R := Real) Real.arcsin (directedSinAngleOperator U V)
      (isSelfAdjoint_directedSinAngleOperator U V)
      Real.continuous_arcsin.continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxi := spectrum_directedSinAngleOperator_subset_Icc U V hx
  exact ⟨Real.arcsin_nonneg.mpr hxi.1, Real.arcsin_le_pi_div_two x⟩

/-- Applying sine to the reconstructed directed angle recovers exactly the
positive directed sine used to define it. -/
theorem cfc_sin_sourceDirectedSubspaceThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    cfc Real.sin (sourceDirectedSubspaceThetaOperator U V) =
      directedSinAngleOperator U V := by
  have hsa : IsSelfAdjoint (directedSinAngleOperator U V) :=
    isSelfAdjoint_directedSinAngleOperator U V
  rw [sourceDirectedSubspaceThetaOperator,
    ← cfc_comp Real.sin Real.arcsin (directedSinAngleOperator U V)
      hsa Real.continuous_sin.continuousOn Real.continuous_arcsin.continuousOn]
  calc
    cfc (Real.sin ∘ Real.arcsin) (directedSinAngleOperator U V) =
        cfc (fun x : Real => x) (directedSinAngleOperator U V) := by
      apply cfc_congr
      intro x hx
      have hxi := spectrum_directedSinAngleOperator_subset_Icc U V hx
      exact Real.sin_arcsin (by linarith [hxi.1]) hxi.2
    _ = directedSinAngleOperator U V := cfc_id' Real _

/-- The literal directed double-angle sine is nonnegative. -/
theorem sourceDirectedSinTwoThetaOperator_nonneg
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sourceDirectedSinTwoThetaOperator U V := by
  rw [sourceDirectedSinTwoThetaOperator]
  refine cfc_nonneg fun t ht => ?_
  have h := spectrum_sourceDirectedSubspaceThetaOperator_subset_Icc U V ht
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

/-- **Literal/product bridge for directed `sin 2 Theta_0`.**

The existing proof-facing object `directedSinTwoAngleOperator` is not merely
assigned the same name or shown to have the same norm: it is exactly the
functional-calculus `sin (2 Theta_0)` defined above.  This is the presentation
bridge used by the source-facing theorem below. -/
theorem sourceDirectedSinTwoThetaOperator_eq_directedSinTwoAngleOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sourceDirectedSinTwoThetaOperator U V = directedSinTwoAngleOperator U V := by
  let S : E →L[K] E := directedSinAngleOperator U V
  let L : E →L[K] E := sourceDirectedSinTwoThetaOperator U V
  let D : E →L[K] E := directedSinTwoAngleOperator U V
  have hSsa : IsSelfAdjoint S := by
    simpa [S] using isSelfAdjoint_directedSinAngleOperator U V
  have h4 : S ^ 4 = (S * S) * (S * S) := by
    rw [show (4 : Nat) = 2 + 2 from rfl, pow_add, pow_two]
  have hW : cfc (fun s : Real => s ^ 2 - s ^ 4) S =
      S * S - (S * S) * (S * S) := by
    rw [cfc_sub (fun s : Real => s ^ 2) (fun s : Real => s ^ 4) S
        (by fun_prop) (by fun_prop),
      cfc_pow_id S 2, cfc_pow_id S 4, h4, pow_two]
  have hLsquare : L * L = (4 : Real) • (S * S - (S * S) * (S * S)) := by
    have hcont : ContinuousOn (fun t : Real => Real.sin (2 * t))
        (spectrum Real (sourceDirectedSubspaceThetaOperator U V)) := by fun_prop
    have harcsin : ContinuousOn Real.arcsin (spectrum Real S) :=
      Real.continuous_arcsin.continuousOn
    have hcomp : ContinuousOn
        (fun t : Real => Real.sin (2 * t) * Real.sin (2 * t))
        (Real.arcsin '' spectrum Real S) := by fun_prop
    rw [show L = sourceDirectedSinTwoThetaOperator U V from rfl,
      sourceDirectedSinTwoThetaOperator, ← cfc_mul (fun t : Real => Real.sin (2 * t))
        (fun t : Real => Real.sin (2 * t))
        (sourceDirectedSubspaceThetaOperator U V) hcont hcont]
    rw [sourceDirectedSubspaceThetaOperator, ← show S = directedSinAngleOperator U V by rfl,
      ← cfc_comp (fun t : Real => Real.sin (2 * t) * Real.sin (2 * t))
        Real.arcsin S hSsa hcomp harcsin]
    have hcongr : cfc
        ((fun t : Real => Real.sin (2 * t) * Real.sin (2 * t)) ∘ Real.arcsin) S =
        cfc (fun s : Real =>
          (s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4) +
            ((s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4))) S := by
      refine cfc_congr fun s hs => ?_
      have hsi : s ∈ Set.Icc (0 : Real) 1 := by
        simpa [S] using spectrum_directedSinAngleOperator_subset_Icc U V hs
      have hsq := TauCeti.sin_two_mul_arcsin_sq (s := s)
        (by linarith [hsi.1]) hsi.2
      have hsquare : Real.sin (2 * Real.arcsin s) * Real.sin (2 * Real.arcsin s) =
          4 * s ^ 2 * (1 - s ^ 2) := by
        rw [← pow_two]
        exact hsq
      simp only [Function.comp_apply]
      rw [hsquare]
      ring
    rw [hcongr]
    have hc2 : ContinuousOn (fun s : Real => s ^ 2 - s ^ 4) (spectrum Real S) := by
      fun_prop
    rw [cfc_add (a := S)
        (fun s : Real => (s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4))
        (fun s : Real => (s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4))
        (by fun_prop) (by fun_prop),
      cfc_add (a := S) (fun s : Real => s ^ 2 - s ^ 4)
        (fun s : Real => s ^ 2 - s ^ 4) hc2 hc2, hW]
    module
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    (U.isIdempotentElem_starProjection).eq
  have hSsquare : S * S =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
    rw [show S = directedSinAngleOperator U V from rfl,
      directedSinAngleOperator_mul_self, Submodule.starProjection_orthogonal' V]
    noncomm_ring [hP]
  have hAleft :
      U.starProjection *
          (U.starProjection * V.starProjection * U.starProjection) =
        U.starProjection * V.starProjection * U.starProjection := by
    calc
      U.starProjection *
          (U.starProjection * V.starProjection * U.starProjection) =
          (U.starProjection * U.starProjection) * V.starProjection *
            U.starProjection := by noncomm_ring
      _ = U.starProjection * V.starProjection * U.starProjection := by rw [hP]
  have hAright :
      (U.starProjection * V.starProjection * U.starProjection) *
          U.starProjection =
        U.starProjection * V.starProjection * U.starProjection := by
    calc
      (U.starProjection * V.starProjection * U.starProjection) *
          U.starProjection =
          U.starProjection * V.starProjection *
            (U.starProjection * U.starProjection) := by noncomm_ring
      _ = U.starProjection * V.starProjection * U.starProjection := by rw [hP]
  have hpoly :
      S * S - (S * S) * (S * S) =
        U.starProjection * V.starProjection * U.starProjection -
          (U.starProjection * V.starProjection * U.starProjection) *
            (U.starProjection * V.starProjection * U.starProjection) := by
    rw [hSsquare]
    calc
      (U.starProjection -
            U.starProjection * V.starProjection * U.starProjection) -
          (U.starProjection -
              U.starProjection * V.starProjection * U.starProjection) *
            (U.starProjection -
              U.starProjection * V.starProjection * U.starProjection) =
          U.starProjection -
            U.starProjection * V.starProjection * U.starProjection -
            U.starProjection * U.starProjection +
            U.starProjection *
              (U.starProjection * V.starProjection * U.starProjection) +
            (U.starProjection * V.starProjection * U.starProjection) *
              U.starProjection -
            (U.starProjection * V.starProjection * U.starProjection) *
              (U.starProjection * V.starProjection * U.starProjection) := by
        noncomm_ring
      _ = U.starProjection * V.starProjection * U.starProjection -
          (U.starProjection * V.starProjection * U.starProjection) *
            (U.starProjection * V.starProjection * U.starProjection) := by
        rw [hP, hAleft, hAright]
        module
  have hDsquare : D * D = (4 : Real) • (S * S - (S * S) * (S * S)) := by
    rw [show D = directedSinTwoAngleOperator U V from rfl,
      directedSinTwoAngleOperator_mul_self, hpoly]
  have hsameSquare : L * L = D * D := hLsquare.trans hDsquare.symm
  have hLnonneg : (0 : E →L[K] E) ≤ L := by
    simpa [L] using sourceDirectedSinTwoThetaOperator_nonneg U V
  have hDnonneg : (0 : E →L[K] E) ≤ D := by
    simpa [D] using directedSinTwoAngleOperator_nonneg U V
  have hLsqrt : L = CFC.sqrt (D * D) :=
    (CFC.sqrt_unique hsameSquare hLnonneg).symm
  have hDsqrt : D = CFC.sqrt (D * D) :=
    (CFC.sqrt_unique rfl hDnonneg).symm
  exact hLsqrt.trans hDsqrt.symm

/-! ## Tangent approximation-number bridge -/

private theorem approximationNumber_eq_tanArcsin_real
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    {S Tg : F →L[Real] F} (hS : IsSelfAdjoint S) (hTg : IsSelfAdjoint Tg)
    (hSlt : ‖S‖ < 1)
    (hrel : Tg * Tg = S * S + Tg * Tg * (S * S)) (n : Nat) :
    Tg.approximationNumber n = Real.tan (Real.arcsin (S.approximationNumber n)) := by
  have hSC : IsSelfAdjoint (complexify S) := (complexify_isSelfAdjoint_iff S).2 hS
  have hTC : IsSelfAdjoint (complexify Tg) := (complexify_isSelfAdjoint_iff Tg).2 hTg
  have hSltC : ‖complexify S‖ < 1 := by
    rwa [norm_complexify]
  have hrelC : complexify Tg * complexify Tg =
      complexify S * complexify S + complexify Tg * complexify Tg *
        (complexify S * complexify S) := by
    have h := congrArg complexify hrel
    simpa only [ContinuousLinearMap.mul_def, complexify_comp, complexify_add] using h
  have hc := TauCeti.ApproximationNumber.approximationNumber_eq_tanArcsin
    hSC hTC hSltC hrelC n
  calc
    Tg.approximationNumber n = (complexify Tg).approximationNumber n :=
      (ComplexificationApproximation.approximationNumber_complexify Tg n).symm
    _ = Real.tan (Real.arcsin ((complexify S).approximationNumber n)) := hc
    _ = Real.tan (Real.arcsin (S.approximationNumber n)) := by
      rw [ComplexificationApproximation.approximationNumber_complexify S n]

private theorem approximationNumber_eq_tanArcsin_rclike
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]
    {S Tg : F →L[K] F} (hS : IsSelfAdjoint S) (hTg : IsSelfAdjoint Tg)
    (hSlt : ‖S‖ < 1)
    (hrel : Tg * Tg = S * S + Tg * Tg * (S * S)) (n : Nat) :
    Tg.approximationNumber n = Real.tan (Real.arcsin (S.approximationNumber n)) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := K) with h | h
  · let e := RCLikeIso.real h
    have hS' : IsSelfAdjoint (TauCeti.ScalarTransport.clm (e := e) S) :=
      (TauCeti.ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hS
    have hT' : IsSelfAdjoint (TauCeti.ScalarTransport.clm (e := e) Tg) :=
      (TauCeti.ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hTg
    have hSlt' : ‖TauCeti.ScalarTransport.clm (e := e) S‖ < 1 := by
      simpa using hSlt
    have hrel' :
        TauCeti.ScalarTransport.clm (e := e) Tg *
            TauCeti.ScalarTransport.clm (e := e) Tg =
          TauCeti.ScalarTransport.clm (e := e) S *
              TauCeti.ScalarTransport.clm (e := e) S +
            TauCeti.ScalarTransport.clm (e := e) Tg *
              TauCeti.ScalarTransport.clm (e := e) Tg *
                (TauCeti.ScalarTransport.clm (e := e) S *
                  TauCeti.ScalarTransport.clm (e := e) S) := by
      have ht := congrArg (TauCeti.ScalarTransport.clm (e := e)) hrel
      simpa only [TauCeti.ScalarTransport.clm_mul,
        TauCeti.ScalarTransport.clm_add] using ht
    have hr := approximationNumber_eq_tanArcsin_real hS' hT' hSlt' hrel' n
    calc
      Tg.approximationNumber n =
          (TauCeti.ScalarTransport.clm (e := e) Tg).approximationNumber n :=
        (TauCeti.ScalarTransport.approximationNumber_clm (e := e) Tg n).symm
      _ = Real.tan (Real.arcsin
          ((TauCeti.ScalarTransport.clm (e := e) S).approximationNumber n)) := hr
      _ = Real.tan (Real.arcsin (S.approximationNumber n)) := by
        rw [TauCeti.ScalarTransport.approximationNumber_clm (e := e) S n]
  · let e := RCLikeIso.complex h
    have hS' : IsSelfAdjoint (TauCeti.ScalarTransport.clm (e := e) S) :=
      (TauCeti.ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hS
    have hT' : IsSelfAdjoint (TauCeti.ScalarTransport.clm (e := e) Tg) :=
      (TauCeti.ScalarTransport.isSelfAdjoint_clm_iff (e := e)).2 hTg
    have hSlt' : ‖TauCeti.ScalarTransport.clm (e := e) S‖ < 1 := by
      simpa using hSlt
    have hrel' :
        TauCeti.ScalarTransport.clm (e := e) Tg *
            TauCeti.ScalarTransport.clm (e := e) Tg =
          TauCeti.ScalarTransport.clm (e := e) S *
              TauCeti.ScalarTransport.clm (e := e) S +
            TauCeti.ScalarTransport.clm (e := e) Tg *
              TauCeti.ScalarTransport.clm (e := e) Tg *
                (TauCeti.ScalarTransport.clm (e := e) S *
                  TauCeti.ScalarTransport.clm (e := e) S) := by
      have ht := congrArg (TauCeti.ScalarTransport.clm (e := e)) hrel
      simpa only [TauCeti.ScalarTransport.clm_mul,
        TauCeti.ScalarTransport.clm_add] using ht
    have hc := TauCeti.ApproximationNumber.approximationNumber_eq_tanArcsin
      hS' hT' hSlt' hrel' n
    calc
      Tg.approximationNumber n =
          (TauCeti.ScalarTransport.clm (e := e) Tg).approximationNumber n :=
        (TauCeti.ScalarTransport.approximationNumber_clm (e := e) Tg n).symm
      _ = Real.tan (Real.arcsin
          ((TauCeti.ScalarTransport.clm (e := e) S).approximationNumber n)) := hc
      _ = Real.tan (Real.arcsin (S.approximationNumber n)) := by
        rw [TauCeti.ScalarTransport.approximationNumber_clm (e := e) S n]

private theorem spectrum_directedSinAngleOperator_lt_one
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htr : ‖directedSinAngleOperator U V‖ < 1)
    {t : Real} (ht : t ∈ spectrum Real (directedSinAngleOperator U V)) :
    0 ≤ t ∧ t < 1 := by
  refine ⟨(spectrum_directedSinAngleOperator_subset_Icc U V ht).1, ?_⟩
  have habs : |t| ≤ ‖directedSinAngleOperator U V‖ * ‖(1 : E →L[K] E)‖ := by
    have hk : ‖((t : K))‖ ≤
        ‖directedSinAngleOperator U V‖ * ‖(1 : E →L[K] E)‖ :=
      spectrum.norm_le_norm_mul_of_mem ht
    rwa [RCLike.norm_ofReal] at hk
  have hone : ‖(1 : E →L[K] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hle : t ≤ ‖directedSinAngleOperator U V‖ := by
    refine (le_abs_self t).trans (habs.trans ?_)
    calc
      ‖directedSinAngleOperator U V‖ * ‖(1 : E →L[K] E)‖ ≤
          ‖directedSinAngleOperator U V‖ * 1 :=
        mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = ‖directedSinAngleOperator U V‖ := mul_one _
  linarith

private theorem continuousOn_tan_arcsin_image_directedSin
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htr : ‖directedSinAngleOperator U V‖ < 1) :
    ContinuousOn Real.tan
      (Real.arcsin '' spectrum Real (directedSinAngleOperator U V)) := by
  refine Real.continuousOn_tan.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  have h := spectrum_directedSinAngleOperator_lt_one U V htr ht
  refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · linarith [Real.pi_pos, Real.arcsin_nonneg.mpr h.1]
  · exact Real.arcsin_lt_pi_div_two.mpr h.2

private theorem continuousOn_tanArcsin_directedSin
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htr : ‖directedSinAngleOperator U V‖ < 1) :
    ContinuousOn (Real.tan ∘ Real.arcsin)
      (spectrum Real (directedSinAngleOperator U V)) :=
  (continuousOn_tan_arcsin_image_directedSin U V htr).comp
    Real.continuous_arcsin.continuousOn (Set.mapsTo_image _ _)

private theorem sourceDirectedTanThetaOperator_eq_cfc_tanArcsin
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htr : ‖directedSinAngleOperator U V‖ < 1) :
    sourceDirectedTanThetaOperator U V =
      cfc (Real.tan ∘ Real.arcsin) (directedSinAngleOperator U V) := by
  rw [sourceDirectedTanThetaOperator, sourceDirectedSubspaceThetaOperator,
    ← cfc_comp Real.tan Real.arcsin (directedSinAngleOperator U V)
      (isSelfAdjoint_directedSinAngleOperator U V)
      (continuousOn_tan_arcsin_image_directedSin U V htr)
      Real.continuous_arcsin.continuousOn]

private theorem sourceDirectedTanThetaOperator_pythagorean
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htr : ‖directedSinAngleOperator U V‖ < 1) :
    sourceDirectedTanThetaOperator U V * sourceDirectedTanThetaOperator U V *
        (1 - directedSinAngleOperator U V * directedSinAngleOperator U V) =
      directedSinAngleOperator U V * directedSinAngleOperator U V := by
  have hf := continuousOn_tanArcsin_directedSin U V htr
  have hSsa : IsSelfAdjoint (directedSinAngleOperator U V) :=
    isSelfAdjoint_directedSinAngleOperator U V
  have hid : ContinuousOn (fun t : Real => t)
      (spectrum Real (directedSinAngleOperator U V)) := continuousOn_id
  have hsq : ContinuousOn (fun t : Real => t * t)
      (spectrum Real (directedSinAngleOperator U V)) := hid.mul hid
  have hone : ContinuousOn (fun _ : Real => (1 : Real))
      (spectrum Real (directedSinAngleOperator U V)) := continuousOn_const
  have hSS :
      directedSinAngleOperator U V * directedSinAngleOperator U V =
        cfc (fun t : Real => t * t) (directedSinAngleOperator U V) := by
    rw [cfc_mul (fun t : Real => t) (fun t : Real => t)
      (directedSinAngleOperator U V) hid hid,
      cfc_id' Real (directedSinAngleOperator U V)]
  have hcos :
      1 - directedSinAngleOperator U V * directedSinAngleOperator U V =
        cfc (fun t : Real => 1 - t * t) (directedSinAngleOperator U V) := by
    rw [cfc_sub (fun _ : Real => (1 : Real)) (fun t : Real => t * t)
      (directedSinAngleOperator U V) hone hsq,
      cfc_const_one Real (directedSinAngleOperator U V), ← hSS]
  rw [sourceDirectedTanThetaOperator_eq_cfc_tanArcsin U V htr, hcos,
    ← cfc_mul (Real.tan ∘ Real.arcsin) (Real.tan ∘ Real.arcsin)
      (directedSinAngleOperator U V) hf hf,
    ← cfc_mul
      (fun x : Real => (Real.tan ∘ Real.arcsin) x * (Real.tan ∘ Real.arcsin) x)
      (fun t : Real => 1 - t * t) (directedSinAngleOperator U V)
      (hf.mul hf) (hone.sub hsq), hSS]
  refine cfc_congr fun t ht => ?_
  have h := spectrum_directedSinAngleOperator_lt_one U V htr ht
  have h1 : (0 : Real) < 1 - t ^ 2 := by nlinarith [h.1, h.2]
  have hsqrt : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
    Real.mul_self_sqrt h1.le
  have hne : Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h1)
  simp only [Function.comp_apply, Real.tan_arcsin]
  field_simp
  nlinarith [hsqrt]

/-- The literal directed tangent has exactly the complete tangent singular-value
sequence `tan (arcsin a_n(sin Theta_0))`. -/
theorem approximationNumber_sourceDirectedTanThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (htr : ‖directedSinAngleOperator U V‖ < 1) (n : Nat) :
    (sourceDirectedTanThetaOperator U V).approximationNumber n =
      Real.tan (Real.arcsin ((directedSinAngleOperator U V).approximationNumber n)) := by
  refine approximationNumber_eq_tanArcsin_rclike
    (isSelfAdjoint_directedSinAngleOperator U V)
    (isSelfAdjoint_sourceDirectedTanThetaOperator U V) htr ?_ n
  have h := sourceDirectedTanThetaOperator_pythagorean U V htr
  rw [mul_sub, mul_one] at h
  exact sub_eq_iff_eq_add.mp h

/-- A strict contraction of the literal directed `sin 2 Theta_0` excludes
all quarter-turn poles from the source-directed angle spectrum. -/
private theorem sourceDirectedHasDefinedDoubleTangent_of_norm_sinTwo_lt_one
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : ‖sourceDirectedSinTwoThetaOperator U V‖ < 1) :
    ∀ t ∈ spectrum Real (sourceDirectedSubspaceThetaOperator U V),
      Real.cos (2 * t) ≠ 0 := by
  intro t ht hcos
  have hs : Real.sin (2 * t) ∈
      spectrum Real (sourceDirectedSinTwoThetaOperator U V) := by
    rw [sourceDirectedSinTwoThetaOperator,
      cfc_map_spectrum (R := Real) (f := fun s : Real => Real.sin (2 * s))
        (a := sourceDirectedSubspaceThetaOperator U V)
        (isSelfAdjoint_sourceDirectedSubspaceThetaOperator U V)
        (by fun_prop : ContinuousOn (fun s : Real => Real.sin (2 * s)) _)]
    exact ⟨t, ht, rfl⟩
  have hspec : |Real.sin (2 * t)| ≤ ‖sourceDirectedSinTwoThetaOperator U V‖ := by
    have hk : ‖((Real.sin (2 * t) : K))‖ ≤
        ‖sourceDirectedSinTwoThetaOperator U V‖ * ‖(1 : E →L[K] E)‖ :=
      spectrum.norm_le_norm_mul_of_mem hs
    have hr : |Real.sin (2 * t)| ≤
        ‖sourceDirectedSinTwoThetaOperator U V‖ * ‖(1 : E →L[K] E)‖ := by
      rwa [RCLike.norm_ofReal] at hk
    calc
      |Real.sin (2 * t)| ≤
          ‖sourceDirectedSinTwoThetaOperator U V‖ * ‖(1 : E →L[K] E)‖ := hr
      _ ≤ ‖sourceDirectedSinTwoThetaOperator U V‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖sourceDirectedSinTwoThetaOperator U V‖ := mul_one _
  have hpyth := Real.sin_sq_add_cos_sq (2 * t)
  rw [hcos] at hpyth
  norm_num at hpyth
  have habs : |Real.sin (2 * t)| = 1 := by
    rcases hpyth with hsin | hsin <;> rw [hsin] <;> norm_num
  rw [habs] at hspec
  exact (not_le_of_gt h) hspec

private theorem sourceDirectedTanTwoThetaOperator_pythagorean
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hSlt : ‖sourceDirectedSinTwoThetaOperator U V‖ < 1) :
    sourceDirectedTanTwoThetaOperator U V * sourceDirectedTanTwoThetaOperator U V =
      sourceDirectedSinTwoThetaOperator U V * sourceDirectedSinTwoThetaOperator U V +
        sourceDirectedTanTwoThetaOperator U V * sourceDirectedTanTwoThetaOperator U V *
          (sourceDirectedSinTwoThetaOperator U V * sourceDirectedSinTwoThetaOperator U V) := by
  let Th : E →L[K] E := sourceDirectedSubspaceThetaOperator U V
  have hTh : IsSelfAdjoint Th := by
    simpa [Th] using isSelfAdjoint_sourceDirectedSubspaceThetaOperator U V
  have hdef := sourceDirectedHasDefinedDoubleTangent_of_norm_sinTwo_lt_one U V hSlt
  have htan : ContinuousOn (fun t : Real => Real.tan (2 * t)) (spectrum Real Th) := by
    refine Real.continuousOn_tan.comp (by fun_prop) ?_
    intro t ht
    exact hdef t (by simpa [Th] using ht)
  have hsin : ContinuousOn (fun t : Real => Real.sin (2 * t)) (spectrum Real Th) := by
    fun_prop
  rw [sourceDirectedTanTwoThetaOperator, sourceDirectedSinTwoThetaOperator,
    show sourceDirectedSubspaceThetaOperator U V = Th from rfl,
    ← cfc_mul (fun t : Real => Real.tan (2 * t))
      (fun t : Real => Real.tan (2 * t)) Th htan htan,
    ← cfc_mul (fun t : Real => Real.sin (2 * t))
      (fun t : Real => Real.sin (2 * t)) Th hsin hsin,
    ← cfc_mul
      (fun t : Real => Real.tan (2 * t) * Real.tan (2 * t))
      (fun t : Real => Real.sin (2 * t) * Real.sin (2 * t)) Th
      (htan.mul htan) (hsin.mul hsin),
    ← cfc_add (a := Th)
      (fun t : Real => Real.sin (2 * t) * Real.sin (2 * t))
      (fun t : Real =>
        (Real.tan (2 * t) * Real.tan (2 * t)) *
          (Real.sin (2 * t) * Real.sin (2 * t)))
      (hsin.mul hsin) ((htan.mul htan).mul (hsin.mul hsin))]
  refine cfc_congr fun t ht => ?_
  have hcos : Real.cos (2 * t) ≠ 0 := hdef t (by simpa [Th] using ht)
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (2 * t)]

/-- The literal directed doubled tangent has exactly the complete singular-value
sequence `tan (arcsin a_n(sin 2 Theta_0))`. -/
theorem approximationNumber_sourceDirectedTanTwoThetaOperator
    (U V : Submodule K E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hSlt : ‖sourceDirectedSinTwoThetaOperator U V‖ < 1) (n : Nat) :
    (sourceDirectedTanTwoThetaOperator U V).approximationNumber n =
      Real.tan (Real.arcsin
        ((sourceDirectedSinTwoThetaOperator U V).approximationNumber n)) := by
  exact approximationNumber_eq_tanArcsin_rclike
    (isSelfAdjoint_sourceDirectedSinTwoThetaOperator U V)
    (isSelfAdjoint_sourceDirectedTanTwoThetaOperator U V) hSlt
    (sourceDirectedTanTwoThetaOperator_pythagorean U V hSlt) n

/-- The ambient positive directed sine and the rectangular trial-side sine block
have the same complete approximation-number sequence.  This is the explicit
zero-extension/modulus bridge used by the tangent presentation theorem. -/
theorem sourceDirectedSine_hasSameApproximationNumbers_directedSineBlock
    (Z V : Submodule K E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [CompleteSpace Z] :
    SameApproximationSingularSequence
      (directedSinAngleOperator Z V) (TanTheta.directedSineBlock Z V) := by
  let B : Z →L[K] E := TanTheta.directedSineBlock Z V
  have hproj : Z.subtypeL ∘L Z.subtypeL.adjoint = Z.starProjection := by
    rw [Submodule.adjoint_subtypeL]
    rfl
  have hcross : B ∘L Z.subtypeL.adjoint =
      Vᗮ.starProjection ∘L Z.starProjection := by
    rw [show B = TanTheta.directedSineBlock Z V from rfl,
      TanTheta.directedSineBlock, ContinuousLinearMap.comp_assoc, hproj]
  have hmod := modulus_hasSameApproximationNumbers_rclike
    (Vᗮ.starProjection ∘L Z.starProjection)
  have hzero := sameApproximationSingularValues_extendDomainByZero Z B
  rw [directedSinAngleOperator]
  refine hmod.trans ?_
  rw [← hcross]
  simpa [B] using hzero

/-- **Davis--Kahan Section 2 directed `tan Theta_0`, presentation form.**

The conclusion is stated directly on `cfc tan Theta_0`.  The existing
rectangular representative remains the proof engine; the proof below transports
its membership and gauge through the explicitly proved equality of complete
approximation-number sequences. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_presentation_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[K] E} {Z V : Submodule K E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : Real} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_K)
    (hResidual : N.Mem D.trial.residual) :
    (∀ n, (TanTheta.directedSineBlock Z V).approximationNumber n < 1) ∧
      N.Mem (sourceDirectedTanThetaOperator Z V) ∧
      delta * N.gauge (sourceDirectedTanThetaOperator Z V) ≤
        N.gauge D.trial.residual := by
  obtain ⟨hlt, T, hTseq, hTmem, hTbound⟩ :=
    tanTheta_directed_unboundedRitz_symmetricNorming_exists_rclike
      N D hV hdelta hupper hUnwanted hResidual
  have hSseq := sourceDirectedSine_hasSameApproximationNumbers_directedSineBlock Z V
  have htr : ‖directedSinAngleOperator Z V‖ < 1 := by
    rw [← (directedSinAngleOperator Z V).approximationNumber_index_zero, hSseq 0]
    exact hlt 0
  have hTanSeq : SameApproximationSingularSequence
      (sourceDirectedTanThetaOperator Z V) T := by
    intro n
    rw [approximationNumber_sourceDirectedTanThetaOperator Z V htr n,
      hSseq n, hTseq n]
  have htransport := hTanSeq.normingMem_iff_and_gauge_eq N
  refine ⟨hlt, htransport.1.mpr hTmem, ?_⟩
  rw [htransport.2]
  exact hTbound

/-- **Davis--Kahan Section 2 directed `tan 2 Theta_0`, presentation form.**

The conclusion is on the literal functional-calculus
`cfc (fun t => tan (2*t)) Theta_0` on the trial-side ordered pair `(V,U)`.  The existing rectangular corner theorem
remains the analytic engine.  The bridge above proves that the literal operator
has exactly the same complete approximation-number sequence as the constructed
corner, so ideal membership and every symmetric-norming gauge transport
explicitly. -/
theorem tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[K] E} {B : E →L[K] E} {a b : Real}
    {U : Submodule K E} [U.HasOrthogonalProjection]
    (V : Submodule K E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_K ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_K)
    (hab : a < b)
    (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    (∀ n : Nat, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      N.Mem (sourceDirectedTanTwoThetaOperator V U) ∧
      (b - a) * N.gauge (sourceDirectedTanTwoThetaOperator V U) ≤
        2 * N.gauge (blockCompression Uᗮ U B) := by
  obtain ⟨hlt, T, hTseq, hTmem, hTbound⟩ :=
    tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_rclike
      N V hA hred hB hV hUa hUb hab hRmem
  have hSseq : SameApproximationSingularSequence
      (sourceDirectedSinTwoThetaOperator V U)
      (DavisKahan.sinTwoThetaIdealBlock U V) := by
    rw [sourceDirectedSinTwoThetaOperator_eq_directedSinTwoAngleOperator V U]
    exact (Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide U V).symm
  have hSlt : ‖sourceDirectedSinTwoThetaOperator V U‖ < 1 := by
    rw [← (sourceDirectedSinTwoThetaOperator V U).approximationNumber_index_zero,
      hSseq 0]
    exact hlt 0
  have hTanSeq : SameApproximationSingularSequence
      (sourceDirectedTanTwoThetaOperator V U) T := by
    intro n
    rw [approximationNumber_sourceDirectedTanTwoThetaOperator V U hSlt n,
      hSseq n, hTseq n]
  have htransport := hTanSeq.normingMem_iff_and_gauge_eq N
  refine ⟨hlt, htransport.1.mpr hTmem, ?_⟩
  rw [htransport.2]
  exact hTbound

/-- **Davis--Kahan Section 2 directed `sin 2 Theta_0`, presentation form.**

This is the existing common-domain where-defined theorem rewritten through the
exact operator identity
`sourceDirectedSinTwoThetaOperator = directedSinTwoAngleOperator`.  The theorem
therefore exposes a literal `cfc (sin o (2 * .)) Theta_0` object without changing
or weakening the analytic engine. -/
theorem sinTwoTheta_directed_commonDomain_presentation_whereDefinedUIN_rclike
    {A T : E →ₗ.[K] E}
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} K)
    (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule K E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hP : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQ : TauCeti.LinearPMap.ReducesSubspace T Q)
    (R : P →L[K] E)
    (hres : ∀ p : P, ∀ hp : (p : E) ∈ T.domain,
      T (⟨(p : E), hp⟩) =
        A (⟨(p : E), by rw [← hdom]; exact hp⟩) + R p)
    {gap : Real} (hgapPos : 0 < gap)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQ)
      (TauCeti.LinearPMap.reducingRestriction T Q.orthogonal hQ.orthogonal) gap) :
    N.Mem (sourceDirectedSinTwoThetaOperator P Q) → N.Mem R →
      gap * N.gaugeReal (sourceDirectedSinTwoThetaOperator P Q) ≤
        2 * N.gaugeReal R := by
  rw [sourceDirectedSinTwoThetaOperator_eq_directedSinTwoAngleOperator P Q]
  exact sinTwoTheta_directed_commonDomain_whereDefinedUIN_rclike
    N hT hdom hP hQ R hres hgapPos hgap

/-- **Davis--Kahan Section 2 complete `sin 2 Theta`, presentation form.**

The directed clause is stated on the literal functional-calculus
`sourceDirectedSinTwoThetaOperator P Q`; the ambient clause is unchanged.  This
is the whole-result presentation theorem used by the short Section 2 API. -/
theorem sinTwoTheta_commonDomain_presentation_whereDefinedUIN_rclike
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedSymmetricOperatorIdealFamily.{u, v} K)
    {A T : E →ₗ.[K] E} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule K E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hP : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQ : TauCeti.LinearPMap.ReducesSubspace T Q)
    {gap : Real} (hgapPos : 0 < gap)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQ)
      (TauCeti.LinearPMap.reducingRestriction T Q.orthogonal hQ.orthogonal) gap) :
    (∀ R : P →L[K] E,
      (∀ p : P, ∀ hp : (p : E) ∈ T.domain,
        T (⟨(p : E), hp⟩) = A (⟨(p : E), by rw [← hdom]; exact hp⟩) + R p) ->
      N.Mem (sourceDirectedSinTwoThetaOperator P Q) → N.Mem R ->
        gap * N.gaugeReal (sourceDirectedSinTwoThetaOperator P Q) ≤
          2 * N.gaugeReal R) ∧
    (∀ Hop : E →L[K] E, Hop.IsSymmetric ->
      T = TauCeti.LinearPMap.addBounded A Hop ->
      N.Mem (Angle.sinTwoAngleOperator P Q) → N.Mem Hop ->
        gap * N.gaugeReal (Angle.sinTwoAngleOperator P Q) ≤ 2 * N.gaugeReal Hop) := by
  constructor
  · intro R hres
    exact sinTwoTheta_directed_commonDomain_presentation_whereDefinedUIN_rclike
      N hT hdom hP hQ R hres hgapPos hgap
  · intro Hop hHop hEq hAngle hHopMem
    exact (sinTwoTheta_commonDomain_whereDefinedUIN_rclike
      N hA hT hdom hP hQ hgapPos hgap).2 Hop hHop hEq hAngle hHopMem


/-! ## Fixed-field presentation specializations

These wrappers keep the convenient field-specific Section 2 entry points while
ensuring that their displayed trigonometric objects are the same literal CFC
objects as the scalar-generic presentation API.  The older fixed-field theorems
remain available under their long proof-facing names. -/

/-- Complex specialization of the literal directed `tan Theta_0` presentation. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_presentation_complex
    {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec] [CompleteSpace Ec]
    (N : SymmetricNormingFunction)
    {A : Ec →ₗ.[ℂ] Ec} {Z V : Submodule ℂ Ec}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : Real} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hResidual : N.Mem D.trial.residual) :
    (∀ n, (TanTheta.directedSineBlock Z V).approximationNumber n < 1) ∧
      N.Mem (sourceDirectedTanThetaOperator Z V) ∧
      delta * N.gauge (sourceDirectedTanThetaOperator Z V) ≤
        N.gauge D.trial.residual :=
  tanTheta_directed_unboundedRitz_symmetricNorming_presentation_rclike
    N D hV hdelta hupper hUnwanted hResidual

/-- Real specialization of the literal directed `tan Theta_0` presentation. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_presentation_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} {Z V : Submodule ℝ Er}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : Real} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hResidual : N.Mem D.trial.residual) :
    (∀ n, (TanTheta.directedSineBlock Z V).approximationNumber n < 1) ∧
      N.Mem (sourceDirectedTanThetaOperator Z V) ∧
      delta * N.gauge (sourceDirectedTanThetaOperator Z V) ≤
        N.gauge D.trial.residual :=
  tanTheta_directed_unboundedRitz_symmetricNorming_presentation_rclike
    N D hV hdelta hupper hUnwanted hResidual

/-- Complex fixed-field where-defined presentation of directed `sin 2 Theta_0`. -/
theorem sinTwoTheta_directed_unboundedResidual_presentation_whereDefinedUIN_complex
    {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec] [CompleteSpace Ec]
    {V : Submodule ℂ Ec} [V.HasOrthogonalProjection]
    {M : V →L[ℂ] V} {R : V →L[ℂ] Ec} {A : Ec →ₗ.[ℂ] Ec}
    [TopologicalSpace.SeparableSpace Ec]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : Ec) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : Ec), hVdom v⟩ = R v + ((M v : V) : Ec))
    {delta : Real} (hdelta : 0 < delta)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) delta) :
    N.Mem (sourceDirectedSinTwoThetaOperator V
        (selfAdjointSpectralSubspace A hA B hB)) →
    N.Mem R →
      delta * N.gaugeReal (sourceDirectedSinTwoThetaOperator V
          (selfAdjointSpectralSubspace A hA B hB)) ≤ 2 * N.gaugeReal R := by
  rw [sourceDirectedSinTwoThetaOperator_eq_directedSinTwoAngleOperator]
  exact sinTwoTheta_directed_unboundedResidual_whereDefinedUIN_complex
    N hA B hB hVdom hres hdelta hgap

/-- Real fixed-field where-defined presentation of directed `sin 2 Theta_0`. -/
theorem sinTwoTheta_directed_unboundedResidual_presentation_whereDefinedUIN_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    {V : Submodule ℝ Er} [V.HasOrthogonalProjection]
    {M : V →L[ℝ] V} {R : V →L[ℝ] Er} {A : Er →ₗ.[ℝ] Er}
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℝ)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : Er) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : Er), hVdom v⟩ = R v + ((M v : V) : Er))
    {delta : Real} (hdelta : 0 < delta)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) delta) :
    N.Mem (sourceDirectedSinTwoThetaOperator V
        (realSelfAdjointSpectralSubspace A hA B hB)) →
    N.Mem R →
      delta * N.gaugeReal (sourceDirectedSinTwoThetaOperator V
          (realSelfAdjointSpectralSubspace A hA B hB)) ≤ 2 * N.gaugeReal R := by
  rw [sourceDirectedSinTwoThetaOperator_eq_directedSinTwoAngleOperator]
  exact sinTwoTheta_directed_unboundedResidual_whereDefinedUIN_real
    N hA B hB hVdom hres hdelta hgap

/-- Complex specialization of the trial-side literal directed `tan 2 Theta_0` presentation. -/
theorem tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_complex
    {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec] [CompleteSpace Ec]
    (N : SymmetricNormingFunction)
    {A : Ec →ₗ.[ℂ] Ec} {B : Ec →L[ℂ] Ec} {a b : Real}
    {U : Submodule ℂ Ec} [U.HasOrthogonalProjection]
    (V : Submodule ℂ Ec) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Ec) ∈ U →
      RCLike.re ⟪A x, (x : Ec)⟫_ℂ ≤ a * ‖(x : Ec)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Ec) ∈ Uᗮ →
      b * ‖(x : Ec)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Ec)⟫_ℂ)
    (hab : a < b)
    (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    (∀ n : Nat, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      N.Mem (sourceDirectedTanTwoThetaOperator V U) ∧
      (b - a) * N.gauge (sourceDirectedTanTwoThetaOperator V U) ≤
        2 * N.gauge (blockCompression Uᗮ U B) :=
  tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_rclike
    N V hA hred hB hV hUa hUb hab hRmem

/-- Real specialization of the trial-side literal directed `tan 2 Theta_0` presentation. -/
theorem tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} {B : Er →L[ℝ] Er} {a b : Real}
    {U : Submodule ℝ Er} [U.HasOrthogonalProjection]
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Er) ∈ U →
      RCLike.re ⟪A x, (x : Er)⟫_ℝ ≤ a * ‖(x : Er)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Er) ∈ Uᗮ →
      b * ‖(x : Er)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Er)⟫_ℝ)
    (hab : a < b)
    (hRmem : N.Mem (blockCompression Uᗮ U B)) :
    (∀ n : Nat, (DavisKahan.sinTwoThetaIdealBlock U V).approximationNumber n < 1) ∧
      N.Mem (sourceDirectedTanTwoThetaOperator V U) ∧
      (b - a) * N.gauge (sourceDirectedTanTwoThetaOperator V U) ≤
        2 * N.gauge (blockCompression Uᗮ U B) :=
  tanTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_presentation_rclike
    N V hA hred hB hV hUa hUb hab hRmem

/-- Complex specialization of the signed literal ambient `tan 2 Theta` presentation. -/
theorem tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_presentation_complex
    {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec] [CompleteSpace Ec]
    (N : SymmetricNormingFunction)
    {A : Ec →ₗ.[ℂ] Ec} {B : Ec →L[ℂ] Ec} {a b : Real}
    {U : Submodule ℂ Ec} [U.HasOrthogonalProjection]
    (V : Submodule ℂ Ec) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Ec) ∈ U →
      RCLike.re ⟪A x, (x : Ec)⟫_ℂ ≤ a * ‖(x : Ec)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Ec) ∈ Uᗮ →
      b * ‖(x : Ec)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Ec)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    Angle.HasDefinedDoubleTangent U V ∧
      N.Mem (Angle.tanTwoAngleOperator U V) ∧
      (b - a) * N.gauge (Angle.tanTwoAngleOperator U V) ≤ 2 * N.gauge B :=
  tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_presentation_rclike
    N V hA hred hBsa hB hV hUa hUb hab hBmem

/-- Real specialization of the signed literal ambient `tan 2 Theta` presentation. -/
theorem tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_presentation_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} {B : Er →L[ℝ] Er} {a b : Real}
    {U : Submodule ℝ Er} [U.HasOrthogonalProjection]
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor U B)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : Er) ∈ U →
      RCLike.re ⟪A x, (x : Er)⟫_ℝ ≤ a * ‖(x : Er)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : Er) ∈ Uᗮ →
      b * ‖(x : Er)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : Er)⟫_ℝ)
    (hab : a < b) (hBmem : N.Mem B) :
    Angle.HasDefinedDoubleTangent U V ∧
      N.Mem (Angle.tanTwoAngleOperator U V) ∧
      (b - a) * N.gauge (Angle.tanTwoAngleOperator U V) ≤ 2 * N.gauge B :=
  tanTwoTheta_ambient_unbounded_reducing_symmetricNorming_presentation_rclike
    N V hA hred hBsa hB hV hUa hUb hab hBmem

end
end DavisKahan1970
end TauCeti
