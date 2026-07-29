/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.FunctionalCalculus.DoubleAngleTangent
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalRiccati
import DavisKahan.Geometry.Angle.OperatorAngleComplex
import DavisKahan.SpectralTheory.GraphSubspace
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport

/-!
# Canonical ambient tangent versus the graph-coordinate tangent

For a quarter-acute pair `U,V`, let `Y` be the canonical ambient angular
operator and `X : U -> U-perp` its rectangular coordinate.  The projection
onto `V = graph(Y)` has the normal-equation formula

`Q = (P+Y) (1+Y*Y)^-1 (P+Y*)`.

Writing `G=Y*Y`, its two source compressions are

`PQP = (1+G)^-1 P`,
`P(1-Q)P = G(1+G)^-1 P`.

Consequently, on `U`,

`sin(2Theta) = 2 sqrt(G) (1+G)^-1`,
`cos(2Theta) = (1-G)(1+G)^-1`,

and both operators vanish on `U-perp`.  Since `||Y||<1`, the extended cosine
is invertible and therefore

`tan(2Theta) = 2 sqrt(G) (1-G)^-1`.

The right side is exactly the modulus of the ambient graph-coordinate operator
`2Y(1-Y*Y)^-1`.  Extending the rectangular coordinate operator by zero gives
that ambient operator, so the canonical tangent and the rectangular graph
tangent have the same complete approximation-number sequence.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.Experimental.ExactSinTheta
-- `doubleAngleTangentOperator` and its denominator API live in the *sibling*
-- namespace `TauCeti.FinishTanTwoTheta` (see `FunctionalCalculus/DoubleAngleTangent.lean`),
-- not under `TauCeti.DavisKahan.FinishTanTwoTheta`, so they are not in scope here by
-- enclosure. `SharpIdeal.lean` fully qualifies every use instead; this open is the
-- same fix in one line. The namespace split itself is a library-organisation defect.
open TauCeti.FinishTanTwoTheta

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- An orthogonally complemented subspace is complete.  `DavisKahan.SinTheta.Natural.Reducing`
declares the same instance, but `local`, so it is not exported to importing modules and has to
be repeated here.  Without it every `ContinuousLinearMap.adjoint` on a subspace in this file
fails to elaborate with `failed to synthesize CompleteSpace ↥U`. -/
noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

private theorem ambientAngularOperator_eq_extendCoordinate
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (Y : E →L[ℂ] E) (hY : IsAngularOperator U Y) :
    Y = Uᗮ.subtypeL ∘L subspaceAngularCoordinate U Y ∘L U.subtypeL.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  have hYP : Y (U.starProjection x) = Y x := by
    have h := DFunLike.congr_fun hY.1 x
    simpa only [ContinuousLinearMap.comp_apply] using h.symm
  have hcoord := coe_subspaceAngularCoordinate_apply U Y hY
    ⟨U.starProjection x, U.starProjection_apply_mem x⟩
  change Y x = (((subspaceAngularCoordinate U Y)
    ⟨U.starProjection x, U.starProjection_apply_mem x⟩ : Uᗮ) : E)
  rw [← hcoord, hYP]

private theorem ambient_doubleAngleTangent_eq_extendCoordinate
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (Y : E →L[ℂ] E) (hY : IsAngularOperator U Y)
    (hcontractive : ‖Y‖ < 1) :
    doubleAngleTangentOperator Y hcontractive =
      Uᗮ.subtypeL ∘L
        doubleAngleTangentOperator (subspaceAngularCoordinate U Y)
          ((norm_subspaceAngularCoordinate_le U Y).trans_lt hcontractive) ∘L
        U.subtypeL.adjoint := by
  let X : U →L[ℂ] Uᗮ := subspaceAngularCoordinate U Y
  let P : E →L[ℂ] E := U.starProjection
  have hYext : Y = Uᗮ.subtypeL ∘L X ∘L U.subtypeL.adjoint :=
    ambientAngularOperator_eq_extendCoordinate U Y hY
  have hYP : Y ∘L P = Y := hY.1
  have hPY : P ∘L Y = 0 := hY.2
  -- `star_mul` cannot fire on `P ∘L Y`: for endomorphisms `∘L` is *defeq* to `*`
  -- but not syntactically equal, so `simp only` never matches.  Go through
  -- `adjoint_comp`, which is stated for `∘L` directly.
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (isSelfAdjoint_starProjection U).star_eq
  have hYstarP : Y.adjoint ∘L P = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hPY
    rwa [ContinuousLinearMap.adjoint_comp, hPadj, map_zero] at h
  have hPYstar : P ∘L Y.adjoint = Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hYP
    rwa [ContinuousLinearMap.adjoint_comp, hPadj] at h
  let G : E →L[ℂ] E := Y.adjoint ∘L Y
  let D : E →L[ℂ] E := doubleAngleDenominator Y
  let DX : U →L[ℂ] U := doubleAngleDenominator X
  have hGP : G ∘L P = G := by
    dsimp [G]
    rw [ContinuousLinearMap.comp_assoc, hYP]
  have hPG : P ∘L G = G := by
    dsimp [G]
    rw [← ContinuousLinearMap.comp_assoc, hPYstar]
  have hDblock : D =
      U.subtypeL ∘L DX ∘L U.subtypeL.adjoint + Uᗮ.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change x - Y.adjoint (Y x) =
      ((U.subtypeL ∘L DX ∘L U.subtypeL.adjoint) x) + Uᗮ.starProjection x
    have hsplit : x = U.starProjection x + Uᗮ.starProjection x := by
      rw [U.starProjection_add_starProjection_orthogonal]
    have hYperp : Y (Uᗮ.starProjection x) = 0 := by
      have h := DFunLike.congr_fun hYP (Uᗮ.starProjection x)
      rw [ContinuousLinearMap.comp_apply,
        Submodule.starProjection_apply_eq_zero_iff.mpr
          (Uᗮ.starProjection_apply_mem x)] at h
      simpa using h.symm
    rw [hsplit, map_add, hYperp, map_zero, add_zero]
    apply congrArg (fun z : U => (z : E))
    ext
    simp only [DX, D, doubleAngleDenominator,
      ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
      Submodule.coe_sub, Submodule.coe_mk]
    rw [coe_subspaceAngularCoordinate_apply U Y hY]
    have hAdj :
        (((X.adjoint (X
          ⟨U.starProjection x, U.starProjection_apply_mem x⟩) : U) : E)) =
          Y.adjoint (Y (U.starProjection x)) := by
      apply Subtype.ext
      intro
      rw [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left]
      simp only [X]
      rw [coe_subspaceAngularCoordinate_apply U Y hY]
      rfl
    rw [hAdj]
  have hDunit := isUnit_doubleAngleDenominator Y hcontractive
  have hDXcontractive : ‖X‖ < 1 :=
    (norm_subspaceAngularCoordinate_le U Y).trans_lt hcontractive
  have hDXunit := isUnit_doubleAngleDenominator X hDXcontractive
  have hDinvblock : Ring.inverse D =
      U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
        Uᗮ.starProjection := by
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp hDunit).1
    have hmul := Ring.mul_inverse_cancel D hDunit
    have hcandidate :
        D ∘L (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
          Uᗮ.starProjection) = ContinuousLinearMap.id ℂ E := by
      rw [hDblock, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_add]
      have hUU : U.subtypeL.adjoint ∘L U.subtypeL =
          ContinuousLinearMap.id ℂ U := by
        ext x
        apply Subtype.ext
        simp
      have hXX := Ring.mul_inverse_cancel DX hDXunit
      have hcross1 :
          (U.subtypeL ∘L DX ∘L U.subtypeL.adjoint) ∘L
            Uᗮ.starProjection = 0 := by
        ext x
        simp
      have hcross2 : Uᗮ.starProjection ∘L
          (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint) = 0 := by
        ext x
        simp
      rw [hcross1, hcross2, add_zero, zero_add,
        ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc DX,
        hUU, ContinuousLinearMap.id_comp, hXX,
        ContinuousLinearMap.comp_assoc,
        U.isIdempotentElem_starProjection_orthogonal.eq]
      ext x
      simp
    have hcand := congrArg (fun T : E →L[ℂ] E => T) hcandidate
    rw [← hmul] at hcand
    exact hcand
  unfold doubleAngleTangentOperator
  rw [hYext, hDinvblock]
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply]
  have hcross : X (U.subtypeL.adjoint (Uᗮ.starProjection x)) = 0 := by
    simp
  rw [hcross, map_zero, add_zero]
  rfl

/-- The canonical ambient double-angle tangent is the modulus of the ambient
extension of the graph-coordinate double-angle tangent. -/
private theorem tanTwoAngleOperatorC_eq_modulus_ambientGraphTangent
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    tanTwoAngleOperatorC U V hquarter =
      ContinuousLinearMap.modulus
        (doubleAngleTangentOperator
          (quarterAcuteAngularOperator U V hquarter)
          (norm_quarterAcuteAngularOperator_lt_one U V hquarter)) := by
  let Y : E →L[ℂ] E := quarterAcuteAngularOperator U V hquarter
  let P : E →L[ℂ] E := U.starProjection
  let Q : E →L[ℂ] E := V.starProjection
  let G : E →L[ℂ] E := Y.adjoint ∘L Y
  let N : E →L[ℂ] E := ContinuousLinearMap.id ℂ E + G
  let R : E →L[ℂ] E := Ring.inverse N
  let D : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - G
  let M : E →L[ℂ] E := ContinuousLinearMap.modulus
    (doubleAngleTangentOperator Y
      (norm_quarterAcuteAngularOperator_lt_one U V hquarter))
  have hY : IsAngularOperator U Y :=
    quarterAcuteAngularOperator_isAngularOperator U V hquarter
  have hYP : Y ∘L P = Y := hY.1
  have hPY : P ∘L Y = 0 := hY.2
  -- See the note on the same pair in `ambientAngularOperator_eq_extendCoordinate`:
  -- `star_mul` does not match `P ∘L Y`, so route through `adjoint_comp`.
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (isSelfAdjoint_starProjection U).star_eq
  have hYstarP : Y.adjoint ∘L P = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hPY
    rwa [ContinuousLinearMap.adjoint_comp, hPadj, map_zero] at h
  have hPYstar : P ∘L Y.adjoint = Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hYP
    rwa [ContinuousLinearMap.adjoint_comp, hPadj] at h
  have hGnonneg : (0 : E →L[ℂ] E) ≤ G := by
    dsimp [G]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Y)
  have hGP : G ∘L P = G := by
    dsimp [G]
    rw [ContinuousLinearMap.comp_assoc, hYP]
  have hPG : P ∘L G = G := by
    dsimp [G]
    rw [← ContinuousLinearMap.comp_assoc, hPYstar]
  have hNunit : IsUnit N := by
    refine ForMathlib.ContinuousLinearMap.isUnit_of_coercive one_pos ?_
    intro x
    dsimp [N, G]
    rw [add_apply, ContinuousLinearMap.id_apply, inner_add_left, map_add,
      ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖Y x‖]
  have hNR : N ∘L R = ContinuousLinearMap.id ℂ E :=
    Ring.mul_inverse_cancel N hNunit
  have hRN : R ∘L N = ContinuousLinearMap.id ℂ E :=
    Ring.inverse_mul_cancel N hNunit
  have hPR : P ∘L R = R ∘L P := by
    have hPN : P ∘L N = N ∘L P := by
      dsimp [N]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, hPG, hGP]
    calc
      P ∘L R = (R ∘L N) ∘L (P ∘L R) := by rw [hRN, ContinuousLinearMap.id_comp]
      _ = R ∘L ((N ∘L P) ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L ((P ∘L N) ∘L R) := by rw [hPN]
      _ = (R ∘L P) ∘L (N ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L P := by rw [hNR, ContinuousLinearMap.comp_id]
  have hGR : G ∘L R = R ∘L G := by
    have hGN : G ∘L N = N ∘L G := by
      dsimp [N]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
    calc
      G ∘L R = (R ∘L N) ∘L (G ∘L R) := by rw [hRN, ContinuousLinearMap.id_comp]
      _ = R ∘L ((N ∘L G) ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L ((G ∘L N) ∘L R) := by rw [hGN]
      _ = (R ∘L G) ∘L (N ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L G := by rw [hNR, ContinuousLinearMap.comp_id]
  have hQformula : Q = (P + Y) ∘L R ∘L (P + Y.adjoint) := by
    have hgraph := projection_graphSubspace_formula U Y hY
    rw [graphSubspace_quarterAcuteAngularOperator U V hquarter] at hgraph
    dsimp [Q, graphProjectionFormula, P, N, R, G] at hgraph ⊢
    simpa only [hYP, ContinuousLinearMap.star_eq_adjoint,
      (isSelfAdjoint_starProjection U).star_eq, star_add, star_mul] using hgraph
  have hPQP : P ∘L Q ∘L P = R ∘L P := by
    rw [hQformula]
    have hPP : P ∘L P = P := U.isIdempotentElem_starProjection
    simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_assoc, hPY, hYstarP, hPP,
      zero_add, add_zero, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero]
    rw [hPR]
  have hPQperpP : P ∘L Vᗮ.starProjection ∘L P = G ∘L R ∘L P := by
    rw [Submodule.starProjection_orthogonal' V,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, hPQP]
    have hidentity : P - R ∘L P = G ∘L R ∘L P := by
      have hNRP := congrArg (fun T : E →L[ℂ] E => T ∘L P) hNR
      dsimp [N] at hNRP
      simp only [ContinuousLinearMap.add_comp,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc] at hNRP
      rw [hGR] at hNRP
      module
    exact hidentity
  let Cang : E →L[ℂ] E := cosAngleOperatorC U V
  let Sang : E →L[ℂ] E := sinAngleOperatorDirectedC U V
  have hCangSq : Cang ∘L Cang = R ∘L P := by
    dsimp [Cang, cosAngleOperatorC]
    rw [ContinuousLinearMap.modulus_mul_self]
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hPQP
  have hSangSq : Sang ∘L Sang = G ∘L R ∘L P := by
    dsimp [Sang, sinAngleOperatorDirectedC]
    rw [ContinuousLinearMap.modulus_mul_self]
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hPQperpP
  have hSCcomm : Commute Sang Cang :=
    commute_sinAngleOperatorDirectedC_cosAngleOperatorC U V
  have hSinTwo : sinTwoAngleOperatorC U V = (2 : ℂ) • (Sang ∘L Cang) := rfl
  have hCosTwo : cosTwoAngleOperatorC U V = D ∘L R ∘L P := by
    dsimp [cosTwoAngleOperatorC, Cang, Sang, D]
    rw [hCangSq, hSangSq]
    rw [← ContinuousLinearMap.sub_comp, ← ContinuousLinearMap.comp_sub]
    dsimp [D]
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    congr 1
    rw [hGR]
  have hDunit : IsUnit D :=
    isUnit_doubleAngleDenominator Y
      (norm_quarterAcuteAngularOperator_lt_one U V hquarter)
  have hDcommG : D ∘L G = G ∘L D := by
    dsimp [D]
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  have hDinvcommG : Ring.inverse D ∘L G = G ∘L Ring.inverse D := by
    exact (show Commute D G from hDcommG).units_inv_left
  have hTformula :
      doubleAngleTangentOperator Y
          (norm_quarterAcuteAngularOperator_lt_one U V hquarter) =
        (2 : ℂ) • (Y ∘L Ring.inverse D) := rfl
  have hMsq : M ∘L M =
      (4 : ℂ) • (ContinuousLinearMap.modulus Y ∘L
        Ring.inverse D ∘L ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    dsimp [M]
    rw [ContinuousLinearMap.modulus_mul_self]
    rw [hTformula, star_smul, star_mul,
      ContinuousLinearMap.star_eq_adjoint,
      (CFC.rpow_nonneg (a := D) (y := (-1 : ℝ))).isSelfAdjoint.star_eq]
    simp only [map_ofNat, mul_smul_comm, smul_mul_assoc]
    rw [← ContinuousLinearMap.modulus_mul_self Y]
    noncomm_ring
  have hCandidateNonneg :
      (0 : E →L[ℂ] E) ≤
        (2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    have hmod : (0 : E →L[ℂ] E) ≤ ContinuousLinearMap.modulus Y :=
      ContinuousLinearMap.modulus_nonneg Y
    have hDinvNonneg : (0 : E →L[ℂ] E) ≤ Ring.inverse D := by
      have hDnonneg : (0 : E →L[ℂ] E) ≤ D := by
        rw [ContinuousLinearMap.nonneg_iff_isPositive]
        refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ?_, ?_⟩
        · dsimp [D, G]
          simpa only [map_one] using
            (IsSelfAdjoint.algebraMap (E →L[ℂ] E)
              (IsSelfAdjoint.all (1 : ℝ))).sub
              (ContinuousLinearMap.isPositive_adjoint_comp_self Y).isSelfAdjoint
        · intro x
          rw [ContinuousLinearMap.reApplyInnerSelf_apply]
          dsimp [D, G]
          rw [sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
            map_sub, ContinuousLinearMap.adjoint_inner_left,
            inner_self_eq_norm_sq]
          have hy := Y.le_opNorm x
          nlinarith [norm_quarterAcuteAngularOperator_lt_one U V hquarter,
            norm_nonneg x, norm_nonneg (Y x)]
      -- `Ring.inverse` of a strictly positive element is its CFC `(-1)`-power,
      -- which is nonnegative.  `IsStrictlyPositive` is by definition
      -- `0 ≤ D ∧ IsUnit D`, both of which are already in hand.
      have hDsp : IsStrictlyPositive D := ⟨hDnonneg, hDunit⟩
      rw [CFC.inverse_eq_rpow_neg_one hDsp]
      exact CFC.rpow_nonneg
    have hcomm : Commute (ContinuousLinearMap.modulus Y) (Ring.inverse D) := by
      have hmodG : Commute (ContinuousLinearMap.modulus Y) G := by
        show Commute (ContinuousLinearMap.modulus Y) (Y.adjoint ∘L Y)
        rw [← ContinuousLinearMap.modulus_mul_self Y]
        exact (Commute.refl _).mul_right (Commute.refl _)
      have hmodD : Commute (ContinuousLinearMap.modulus Y) D := by
        show Commute (ContinuousLinearMap.modulus Y)
          (ContinuousLinearMap.id ℂ E - G)
        exact (Commute.one_right _).sub_right hmodG
      exact hmodD.units_inv_right
    have hprod : (0 : E →L[ℂ] E) ≤
        ContinuousLinearMap.modulus Y ∘L Ring.inverse D :=
      hcomm.mul_nonneg hmod hDinvNonneg
    simpa only [Complex.ofReal_ofNat] using
      smul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hprod
  have hMformula :
      M = (2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    apply ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq hCandidateNonneg
    rw [hMsq]
    noncomm_ring
  have hSCformula : Sang ∘L Cang =
      ContinuousLinearMap.modulus Y ∘L R ∘L P := by
    have hleftNonneg : (0 : E →L[ℂ] E) ≤ Sang ∘L Cang :=
      hSCcomm.mul_nonneg (sinAngleOperatorDirectedC_nonneg U V)
        (cosAngleOperatorC_nonneg U V)
    have hrightNonneg : (0 : E →L[ℂ] E) ≤
        ContinuousLinearMap.modulus Y ∘L R ∘L P := by
      -- all three factors are nonnegative functions of `G` on `U`
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      refine ⟨?_, ?_⟩
      · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
        intro x y
        simp [ContinuousLinearMap.adjoint_inner_left]
      · intro x
        rw [ContinuousLinearMap.reApplyInnerSelf_apply]
        positivity
    apply CFC.sqrt_unique
    · rw [← hSCcomm.eq, ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc Sang, hSangSq,
        ContinuousLinearMap.comp_assoc, hCangSq]
      rw [hGR, hGP, hPR]
      noncomm_ring
    · exact hleftNonneg
    · rw [ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc (ContinuousLinearMap.modulus Y),
        ContinuousLinearMap.modulus_mul_self Y]
      rw [hGR, hGP, hPR]
      noncomm_ring
    · exact hrightNonneg
  have hCandidateComp :
      M ∘L cosTwoAngleExtendedC U V = sinTwoAngleOperatorC U V := by
    rw [hMformula, cosTwoAngleExtendedC, hCosTwo, hSinTwo, hSCformula]
    have hMperp : ContinuousLinearMap.modulus Y ∘L Uᗮ.starProjection = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.modulus_apply_eq_zero_iff]
      have hzero : Y (Uᗮ.starProjection x) = 0 := by
        have h := DFunLike.congr_fun hYP (Uᗮ.starProjection x)
        rw [ContinuousLinearMap.comp_apply,
          Submodule.starProjection_apply_eq_zero_iff.mpr
            (Uᗮ.starProjection_apply_mem x)] at h
        simpa using h.symm
      exact hzero
    rw [ContinuousLinearMap.comp_add, hMperp, add_zero]
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      Ring.inverse_mul_cancel D hDunit, ContinuousLinearMap.id_comp]
    noncomm_ring
  have hcanonical := tanTwoAngleOperatorC_comp_cosTwoAngleExtendedC U V hquarter
  have hcosSurj : Function.Surjective (cosTwoAngleExtendedC U V) := by
    rw [← LinearMap.range_eq_top]
    exact (cosTwoAngleExtendedC_ker_bot_range_top U V hquarter).2
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hcosSurj x
  have h1 := DFunLike.congr_fun hcanonical y
  have h2 := DFunLike.congr_fun hCandidateComp y
  exact h1.trans h2.symm

/-- The canonical ambient `tan 2Theta` and the rectangular graph-coordinate
operator have the same full approximation-number sequence. -/
theorem canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    (tanTwoAngleOperatorC U V hquarter).HasSameApproximationNumbers
      (doubleAngleTangentOperator
        (quarterAcuteAngularCoordinate U V hquarter)
        (norm_quarterAcuteAngularCoordinate_lt_one U V hquarter)) := by
  let Y : E →L[ℂ] E := quarterAcuteAngularOperator U V hquarter
  let X : U →L[ℂ] Uᗮ := quarterAcuteAngularCoordinate U V hquarter
  let hYc : ‖Y‖ < 1 := norm_quarterAcuteAngularOperator_lt_one U V hquarter
  let hXc : ‖X‖ < 1 := norm_quarterAcuteAngularCoordinate_lt_one U V hquarter
  have hcanonical : tanTwoAngleOperatorC U V hquarter =
      ContinuousLinearMap.modulus (doubleAngleTangentOperator Y hYc) := by
    simpa only [Y, hYc] using
      tanTwoAngleOperatorC_eq_modulus_ambientGraphTangent U V hquarter
  have hambient : doubleAngleTangentOperator Y hYc =
      Uᗮ.subtypeL ∘L doubleAngleTangentOperator X hXc ∘L U.subtypeL.adjoint := by
    simpa only [Y, X, hYc, hXc, quarterAcuteAngularCoordinate] using
      ambient_doubleAngleTangent_eq_extendCoordinate U Y
        (quarterAcuteAngularOperator_isAngularOperator U V hquarter) hYc
  rw [hcanonical]
  exact
    (sameApproximationSingularValues_rectangularOperatorModulus
      (doubleAngleTangentOperator Y hYc)).trans
      (by
        rw [hambient]
        exact sameApproximationSingularValues_ambientSubspaceBlock U Uᗮ
          (doubleAngleTangentOperator X hXc))

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
