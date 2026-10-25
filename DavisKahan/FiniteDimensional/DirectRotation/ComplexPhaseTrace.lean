/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.ComplexCrossedDefects
public import DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceFiniteModel
public import DavisKahan.Geometry.Angle.Proposition35Nonacute
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.PositiveTrace
public import ForTauCeti.Analysis.InnerProductSpace.Polar.CFCBridge

/-!
# Global complex trace-optimality via opposite phase corrections

The nonacute direct rotation `R` already exists whenever the two crossed defect
spaces are unitarily equivalent.  Finite equal-dimensional pairs automatically
satisfy that condition.  Put `C = cos Θ`, `S = sin Θ = |P_U - P_V|`, `K = R-C`
and `B = i K`.  The operator `B` is selfadjoint, and `|B| = S`.

The two phase-corrected rotations `T₊ = R(C+iS)` and `T₋ = R(C-iS)` are unitary
transports, including on the right-angle defect blocks.  Their displacements
have the factorizations

  `1 - T₊ = (S-B)(S-iC)`,
  `1 - T₋ = (S+B)(S+iC)`.

The right factors are unitary.  The left factors are positive, being twice the
negative and positive parts of the selfadjoint `B`.  Their sum is `2S`.
Thus the trace norms of the two displacements sum to `2 trace(S)`.  The
projection-distance lower bound forces each to equal `trace(S)` individually.
This avoids a singular-value enumeration and a CS-coordinate equivalence.
-/

public section

attribute [local instance] ContinuousLinearMap.realAlgebra ContinuousLinearMap.realIsScalarTower

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ComplexTraceOptimality

open scoped InnerProductSpace BigOperators
open Module (finrank)

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

private noncomputable instance finite_complete : CompleteSpace H :=
  FiniteDimensional.complete ℂ H

private abbrev BEnd (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] := H →L[ℂ] H

private noncomputable def imaginaryUnit : BEnd H :=
  algebraMap ℂ (BEnd H) Complex.I

omit [FiniteDimensional ℂ H] in
private theorem imaginaryUnit_sq :
    (imaginaryUnit : BEnd H) * imaginaryUnit = -1 := by
  unfold imaginaryUnit
  rw [← map_mul, Complex.I_mul_I]
  simp

omit [FiniteDimensional ℂ H] in
private theorem imaginaryUnit_comm (A : BEnd H) :
    (imaginaryUnit : BEnd H) * A = A * imaginaryUnit :=
  Algebra.commutes Complex.I A

private theorem imaginaryUnit_star :
    star (imaginaryUnit : BEnd H) = -imaginaryUnit := by
  have hz : (imaginaryUnit : BEnd H) = Complex.I • (1 : BEnd H) :=
    Algebra.algebraMap_eq_smul_one Complex.I
  rw [hz, star_smul, star_one, Complex.star_def, Complex.conj_I, neg_smul]

omit [FiniteDimensional ℂ H] in
/-- Move the central imaginary scalar past a bounded operator. -/
private theorem imaginaryUnit_left_switch (A B : BEnd H) :
    A * (imaginaryUnit * B) = imaginaryUnit * (A * B) := by
  calc
    A * (imaginaryUnit * B) = (A * imaginaryUnit) * B :=
      (mul_assoc A imaginaryUnit B).symm
    _ = (imaginaryUnit * A) * B := by rw [imaginaryUnit_comm A]
    _ = imaginaryUnit * (A * B) := mul_assoc imaginaryUnit A B

omit [FiniteDimensional ℂ H] in
/-- Two central imaginary factors contribute a minus sign. -/
private theorem imaginaryUnit_mul_imaginaryUnit (A B : BEnd H) :
    (imaginaryUnit * A) * (imaginaryUnit * B) = -(A * B) := by
  calc
    (imaginaryUnit * A) * (imaginaryUnit * B) =
        imaginaryUnit * (A * (imaginaryUnit * B)) :=
      mul_assoc imaginaryUnit A (imaginaryUnit * B)
    _ = imaginaryUnit * ((A * imaginaryUnit) * B) := by
      rw [← mul_assoc A imaginaryUnit B]
    _ = imaginaryUnit * ((imaginaryUnit * A) * B) := by
      rw [imaginaryUnit_comm A]
    _ = (imaginaryUnit * imaginaryUnit) * (A * B) := by
      simp only [mul_assoc]
    _ = -(A * B) := by rw [imaginaryUnit_sq]; simp

/-- The signed complex phases of `cos Θ` and `sin Θ`. -/
private noncomputable def phasePlus (C S : BEnd H) : BEnd H :=
  C + imaginaryUnit * S

private noncomputable def phaseMinus (C S : BEnd H) : BEnd H :=
  C - imaginaryUnit * S

/-- A commuting Pythagorean pair has two unitary complex phases. -/
private theorem phase_mem_unitary
    (C S : BEnd H)
    (hCstar : star C = C) (hSstar : star S = S)
    (hCS : C * S = S * C)
    (hpy : S * S + C * C = 1) :
    phasePlus C S ∈ unitary (BEnd H) ∧
      phaseMinus C S ∈ unitary (BEnd H) := by
  let z : BEnd H := imaginaryUnit
  have hzc : z * C = C * z := imaginaryUnit_comm C
  have hzs : z * S = S * z := imaginaryUnit_comm S
  have hzstar : star z = -z := imaginaryUnit_star
  have hpstar : star (phasePlus C S) = phaseMinus C S := by
    change star (C + z * S) = C - z * S
    rw [star_add, star_mul, hCstar, hSstar, hzstar, mul_neg, ← hzs]
    abel
  have hmstar : star (phaseMinus C S) = phasePlus C S := by
    change star (C - z * S) = C + z * S
    rw [star_sub, star_mul, hCstar, hSstar, hzstar, mul_neg, ← hzs]
    abel
  have hzcS : (z * S) * C = C * (z * S) := by
    calc
      (z * S) * C = z * (S * C) := mul_assoc z S C
      _ = z * (C * S) := by rw [hCS]
      _ = (z * C) * S := (mul_assoc z C S).symm
      _ = (C * z) * S := by rw [hzc]
      _ = C * (z * S) := mul_assoc C z S
  have hziS : (z * S) * (z * S) = -(S * S) :=
    imaginaryUnit_mul_imaginaryUnit S S
  have hpm : phasePlus C S * phaseMinus C S = 1 := by
    change (C + z * S) * (C - z * S) = 1
    calc
      (C + z * S) * (C - z * S) =
          C * C - C * (z * S) + ((z * S) * C - (z * S) * (z * S)) := by
        simp only [add_mul, mul_sub]
        abel
      _ = C * C - (z * S) * (z * S) := by rw [hzcS]; abel
      _ = C * C + S * S := by rw [hziS]; abel
      _ = 1 := by rw [add_comm (C * C) (S * S), hpy]
  have hmp : phaseMinus C S * phasePlus C S = 1 := by
    change (C - z * S) * (C + z * S) = 1
    calc
      (C - z * S) * (C + z * S) =
          C * C + C * (z * S) - ((z * S) * C + (z * S) * (z * S)) := by
        simp only [sub_mul, mul_add]
        abel
      _ = C * C - (z * S) * (z * S) := by rw [hzcS]; abel
      _ = C * C + S * S := by rw [hziS]; abel
      _ = 1 := by rw [add_comm (C * C) (S * S), hpy]
  exact ⟨⟨by rw [hpstar]; exact hmp, by rw [hpstar]; exact hpm⟩,
    ⟨by rw [hmstar]; exact hpm, by rw [hmstar]; exact hmp⟩⟩

omit [FiniteDimensional ℂ H] in
/-- The projection on either source or target commutes with both phases. -/
private theorem phase_commutes_projection
    (P C S : BEnd H)
    (hCP : C * P = P * C) (hSP : S * P = P * S) :
    phasePlus C S * P = P * phasePlus C S ∧
      phaseMinus C S * P = P * phaseMinus C S := by
  let z : BEnd H := imaginaryUnit
  have hzP : z * P = P * z := imaginaryUnit_comm P
  have hzSP : (z * S) * P = P * (z * S) := by
    calc
      (z * S) * P = z * (S * P) := mul_assoc z S P
      _ = z * (P * S) := by rw [hSP]
      _ = (z * P) * S := (mul_assoc z P S).symm
      _ = (P * z) * S := by rw [hzP]
      _ = P * (z * S) := mul_assoc P z S
  constructor
  · change (C + z * S) * P = P * (C + z * S)
    calc
      (C + z * S) * P = C * P + (z * S) * P := add_mul C (z * S) P
      _ = P * C + P * (z * S) := by rw [hCP, hzSP]
      _ = P * (C + z * S) := (mul_add P C (z * S)).symm
  · change (C - z * S) * P = P * (C - z * S)
    calc
      (C - z * S) * P = C * P - (z * S) * P := sub_mul C (z * S) P
      _ = P * C - P * (z * S) := by rw [hCP, hzSP]
      _ = P * (C - z * S) := (mul_sub P C (z * S)).symm

omit [FiniteDimensional ℂ H] in
/-- Two complementary displacement factorizations, purely in the operator ring.
The `i(R-C)` term is selfadjoint because `R-C` is skew-adjoint. -/
private theorem phase_displacement_factors
    (R C S : BEnd H)
    (hCS : C * S = S * C)
    (hpy : S * S + C * C = 1) :
    1 - R * phasePlus C S =
      (S - imaginaryUnit * (R - C)) * (S - imaginaryUnit * C) ∧
    1 - R * phaseMinus C S =
      (S + imaginaryUnit * (R - C)) * (S + imaginaryUnit * C) := by
  let z : BEnd H := imaginaryUnit
  have hsum : S * C + (R - C) * S = R * S := by
    calc
      S * C + (R - C) * S = S * C + (R * S - C * S) := by
        rw [sub_mul]
      _ = R * S := by rw [hCS]; abel
  have hterm :
      S * (z * C) + (z * (R - C)) * S = R * (z * S) := by
    have hleft : S * (z * C) = z * (S * C) :=
      imaginaryUnit_left_switch S C
    have hright : (z * (R - C)) * S = z * ((R - C) * S) :=
      mul_assoc z (R - C) S
    calc
      S * (z * C) + (z * (R - C)) * S =
          z * (S * C) + z * ((R - C) * S) := by rw [hleft, hright]
      _ = z * (S * C + (R - C) * S) := (mul_add z _ _).symm
      _ = z * (R * S) := by rw [hsum]
      _ = R * (z * S) := (imaginaryUnit_left_switch R S).symm
  have hziKC : (z * (R - C)) * (z * C) = -((R - C) * C) :=
    imaginaryUnit_mul_imaginaryUnit (R - C) C
  constructor
  · change 1 - R * (C + z * S) =
        (S - z * (R - C)) * (S - z * C)
    calc
      1 - R * (C + z * S) =
          (S * S + C * C) - R * (C + z * S) := by rw [hpy]
      _ = (S - z * (R - C)) * (S - z * C) := by
        symm
        calc
          (S - z * (R - C)) * (S - z * C) =
              S * S - (S * (z * C) + (z * (R - C)) * S) +
                (z * (R - C)) * (z * C) := by
            simp only [sub_mul, mul_sub]
            abel
          _ = S * S - R * (z * S) - (R - C) * C := by
            rw [hterm, hziKC]
            abel
          _ = (S * S + C * C) - R * (C + z * S) := by
            simp only [sub_mul, mul_add]
            abel
  · change 1 - R * (C - z * S) =
        (S + z * (R - C)) * (S + z * C)
    calc
      1 - R * (C - z * S) =
          (S * S + C * C) - R * (C - z * S) := by rw [hpy]
      _ = (S + z * (R - C)) * (S + z * C) := by
        symm
        calc
          (S + z * (R - C)) * (S + z * C) =
              S * S + (S * (z * C) + (z * (R - C)) * S) +
                (z * (R - C)) * (z * C) := by
            simp only [add_mul, mul_add]
            abel
          _ = S * S + R * (z * S) - (R - C) * C := by
            rw [hterm, hziKC]
            abel
          _ = (S * S + C * C) - R * (C - z * S) := by
            simp only [sub_mul, mul_sub]
            abel

/-- For a skew-adjoint `K` whose modulus is `S`, the imaginary multiple `iK`
is selfadjoint and has the same modulus. -/
private theorem imaginary_skew_modulus
    (K S : BEnd H)
    (hskew : star K = -K)
    (hmod : K.modulus = S)
    (hS0 : 0 ≤ S) :
    IsSelfAdjoint (imaginaryUnit * K) ∧
      CFC.abs (imaginaryUnit * K) = S := by
  let z : BEnd H := imaginaryUnit
  let B : BEnd H := z * K
  have hz2 : z * z = -1 := imaginaryUnit_sq
  have hzK : z * K = K * z := imaginaryUnit_comm K
  have hzstar : star z = -z := imaginaryUnit_star
  have hBstar : star B = B := by
    dsimp [B]
    rw [star_mul, hskew, hzstar]
    noncomm_ring [hzK]
  have hKgram : -(K * K) = S * S := by
    have h : K.modulus * K.modulus = star K * K := K.modulus_comp_modulus
    rw [hmod, hskew] at h
    simpa only [neg_mul] using h.symm
  have hBsq : B * B = S * S := by
    change (z * K) * (z * K) = S * S
    calc
      (z * K) * (z * K) = (z * z) * (K * K) := by
        calc
          (z * K) * (z * K) = z * (K * z) * K := by simp only [mul_assoc]
          _ = z * (z * K) * K := by rw [hzK]
          _ = (z * z) * (K * K) := by simp only [mul_assoc]
      _ = -(K * K) := by rw [hz2]; simp
      _ = S * S := hKgram
  have hBgram : star B * B = S * S := by
    rw [hBstar]
    exact hBsq
  have habs : CFC.abs B = S := by
    calc
      CFC.abs B = CFC.sqrt (star B * B) := rfl
      _ = CFC.sqrt (S * S) := by rw [hBgram]
      _ = S := CFC.sqrt_unique rfl hS0
  exact ⟨hBstar, habs⟩

/-- Absolute value dominates the positive and negative parts of a selfadjoint
operator.  Both `|B| + B` and `|B| - B` are positive. -/
private theorem abs_plus_minus_nonneg
    (B : BEnd H) (hB : IsSelfAdjoint B) (S : BEnd H)
    (habs : CFC.abs B = S) :
    0 ≤ S - B ∧ 0 ≤ S + B := by
  have hp : 0 ≤ B⁺ := CFC.posPart_nonneg B
  have hn : 0 ≤ B⁻ := CFC.negPart_nonneg B
  constructor
  · rw [← habs, CFC.abs_sub_self B hB, two_smul]
    exact add_nonneg hn hn
  · rw [← habs, CFC.abs_add_self B hB, two_smul]
    exact add_nonneg hp hp

/-- A unitary `T` transports `U` onto `V` if it intertwines their projections,
using equal finite ranks to establish surjectivity on the target. -/
private theorem unitary_transport_of_intertwines
    (U V : Submodule ℂ H) (hUV : finrank ℂ U = finrank ℂ V)
    (T : BEnd H) (hT : T ∈ unitary (BEnd H))
    (hintertwines : T * U.starProjection = V.starProjection * T) :
    U.map (Unitary.linearIsometryEquiv (⟨T, hT⟩ : unitary (BEnd H))).toLinearMap = V := by
  let W : H ≃ₗᵢ[ℂ] H :=
    Unitary.linearIsometryEquiv (⟨T, hT⟩ : unitary (BEnd H))
  have hmaple : U.map W.toLinearMap ≤ V := by
    rintro x ⟨y, hy, rfl⟩
    have hyproj : U.starProjection y = y :=
      Submodule.starProjection_eq_self_iff.mpr hy
    have hTw : W y = T y := rfl
    have hVproj : V.starProjection (T y) = T y := by
      have h := congrArg (fun A : BEnd H => A y) hintertwines
      simpa [mul_apply_eq_comp, hyproj] using h.symm
    rw [Submodule.starProjection_eq_self_iff] at hVproj
    simpa [hTw] using hVproj
  have hdim : finrank ℂ (U.map W.toLinearMap) = finrank ℂ U := by
    simpa using (LinearEquiv.finrank_map_eq W.toLinearEquiv U)
  exact Submodule.eq_of_le_of_finrank_eq hmaple (hdim.trans hUV)

/-- The nonacute completed rotation and its two complex phase corrections.
The datum `J` is supplied automatically for equal-dimensional subspaces. -/
private noncomputable def directRotationPhasePlus
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    BEnd H :=
  nonacuteDirectRotation U V J *
    phasePlus (Proposition35.section3CosAngleOperator U V)
      (Proposition35.section3SinAngleOperator U V)

private noncomputable def directRotationPhaseMinus
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    BEnd H :=
  nonacuteDirectRotation U V J *
    phaseMinus (Proposition35.section3CosAngleOperator U V)
      (Proposition35.section3SinAngleOperator U V)

/-- All geometric hypotheses for the paired phase construction are already
part of Davis--Kahan's verified nonacute operator-angle API. -/
private theorem nonacute_phase_geometry
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V) :
    let R := nonacuteDirectRotation U V J
    let C := Proposition35.section3CosAngleOperator U V
    let S := Proposition35.section3SinAngleOperator U V
    R ∈ unitary (BEnd H) ∧
      0 ≤ S ∧ star C = C ∧ star S = S ∧
      R * C = C * R ∧ R * S = S * R ∧ C * S = S * C ∧
      S * S + C * C = 1 ∧
      star (R - C) = -(R - C) ∧ (R - C).modulus = S ∧
      C * U.starProjection = U.starProjection * C ∧
      S * U.starProjection = U.starProjection * S := by
  dsimp
  have hS0 := Proposition35.section3SinAngleOperator_nonneg U V
  have hC0 := Proposition35.section3CosAngleOperator_nonneg U V
  have hpy := Proposition35.section3Sin_sq_add_cos_sq U V
  have hCSsq : Commute
      (Proposition35.section3CosAngleOperator U V *
        Proposition35.section3CosAngleOperator U V)
      (Proposition35.section3SinAngleOperator U V) := by
    have hCsq : Proposition35.section3CosAngleOperator U V *
        Proposition35.section3CosAngleOperator U V =
        1 - Proposition35.section3SinAngleOperator U V *
          Proposition35.section3SinAngleOperator U V :=
      eq_sub_of_add_eq' hpy
    rw [hCsq]
    exact (Commute.one_left _).sub_left
      ((Commute.refl _).mul_left (Commute.refl _))
  have hCS := TauCeti.commute_of_commute_mul_self hC0 hCSsq
  have hCP : Commute (Proposition35.section3CosAngleOperator U V)
      U.starProjection := by
    exact Commute.cfc_real
      (Proposition35.section3AngleOperator_comm_projection U V) Real.cos
  exact ⟨nonacuteDirectRotation_mem_unitary U V J,
    hS0,
    (cfc_predicate Real.cos (Proposition35.section3AngleOperator U V)).star_eq,
    (Proposition35.section3SinAngleOperator_isSelfAdjoint U V).star_eq,
    (Proposition35.nonacuteDirectRotation_comm_cosine U V J).eq,
    (Proposition35.nonacuteDirectRotation_comm_sine U V J).eq,
    hCS.eq, hpy,
    Proposition35.star_nonacuteDirectRotation_sub_cosine U V J,
    Proposition35.modulus_nonacuteDirectRotation_sub_cosine U V J,
    hCP.eq,
    (Proposition35.section3SinAngleOperator_comm_projection U V).eq⟩


/-- Full Ky Fan trace is additive for positive bounded endomorphisms. -/
private theorem kyFanSum_add_of_nonneg
    (A B : BEnd H) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    kyFanSum (finrank ℂ H) (A + B).toLinearMap =
      kyFanSum (finrank ℂ H) A.toLinearMap +
        kyFanSum (finrank ℂ H) B.toLinearMap := by
  have hA' : A.toLinearMap.IsPositive := by
    apply (LinearMap.isPositive_toContinuousLinearMap_iff A.toLinearMap).mpr
    exact (ContinuousLinearMap.nonneg_iff_isPositive).mp hA
  have hB' : B.toLinearMap.IsPositive := by
    apply (LinearMap.isPositive_toContinuousLinearMap_iff B.toLinearMap).mpr
    exact (ContinuousLinearMap.nonneg_iff_isPositive).mp hB
  have hmap : (A + B).toLinearMap = A.toLinearMap + B.toLinearMap := by
    ext x
    rfl
  rw [hmap]
  exact TauCeti.kyFanSum_add_of_isPositive
    A.toLinearMap B.toLinearMap hA' hB'

/-- A bounded-operator unitary produces the same linear-map Ky Fan sum. -/
private theorem kyFanSum_displacement_of_unitary
    (T : BEnd H) (hT : T ∈ unitary (BEnd H)) :
    kyFanSum (finrank ℂ H)
      (LinearMap.id -
        (Unitary.linearIsometryEquiv (⟨T, hT⟩ : unitary (BEnd H))).toLinearMap) =
      kyFanSum (finrank ℂ H) (1 - T).toLinearMap := by
  congr 1

/-- Multiplication on the right by a unitary preserves full Ky Fan trace. -/
private theorem kyFanSum_mul_unitary_right
    (A T : BEnd H) (hT : T ∈ unitary (BEnd H)) :
    kyFanSum (finrank ℂ H) (A * T).toLinearMap =
      kyFanSum (finrank ℂ H) A.toLinearMap := by
  let W : H ≃ₗᵢ[ℂ] H :=
    Unitary.linearIsometryEquiv (⟨T, hT⟩ : unitary (BEnd H))
  have hmul : (A * T).toLinearMap = A.toLinearMap ∘ₗ W.toLinearMap := by
    ext x
    rfl
  rw [hmul, kyFanSum_eq_linearMap_kyFanSum, kyFanSum_eq_linearMap_kyFanSum]
  exact LinearMap.kyFanSum_comp_linearIsometryEquiv A.toLinearMap W _

/-- The full Ky Fan trace norm of the ambient sine operator is exactly the
trace norm of the projector difference. -/
private theorem kyFanSum_projector_eq_nonacute_sine
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    kyFanSum (finrank ℂ H) (projection U - projection V) =
      kyFanSum (finrank ℂ H)
        (Proposition35.section3SinAngleOperator U V).toLinearMap := by
  let S : BEnd H := Proposition35.section3SinAngleOperator U V
  have hcont : (projection U - projection V).toContinuousLinearMap =
      (U.starProjection - V.starProjection : BEnd H) := by
    ext x
    rfl
  have habs := operatorAbs_toContinuousLinearMap_eq_modulus
    (projection U - projection V)
  rw [hcont] at habs
  have hS : S.toLinearMap = sinAngleOperator U V := by
    apply LinearMap.ext
    intro x
    simp only [S, Proposition35.section3SinAngleOperator]
    change ((U.starProjection - V.starProjection : BEnd H).modulus) x =
      (operatorAbs (projection U - projection V)).toContinuousLinearMap x
    exact congrArg (fun T : BEnd H => T x) habs.symm
  calc
    kyFanSum (finrank ℂ H) (projection U - projection V) =
        (UnitarilyInvariantSeminorm.kyFan ℂ H H (finrank ℂ H))
          (projection U - projection V) :=
      kyFanSum_eq_kyFan (finrank ℂ H) (projection U - projection V)
    _ = (UnitarilyInvariantSeminorm.kyFan ℂ H H (finrank ℂ H))
          (sinAngleOperator U V) :=
      uiNorm_projection_sub_eq_sinAngleOperator
        (UnitarilyInvariantSeminorm.kyFan ℂ H H (finrank ℂ H)) U V
    _ = kyFanSum (finrank ℂ H) S.toLinearMap := by
      rw [← hS]
      exact (kyFanSum_eq_kyFan (finrank ℂ H) S.toLinearMap).symm

/-- The phase-corrected completed rotation is trace optimal on *every*
finite-dimensional complex equal-rank pair, including right-angle defects.

Unlike the finite-model theorem, this conclusion assumes **no** coordinate
representation of the pair and no acuteness hypothesis. -/
theorem exists_trace_optimal_unitary_of_equal_finrank
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      AttainsProjectionTraceBound U V W := by
  classical
  let J := finiteCrossedDefectEquiv U V hUV
  let R : BEnd H := nonacuteDirectRotation U V J
  let C : BEnd H := Proposition35.section3CosAngleOperator U V
  let S : BEnd H := Proposition35.section3SinAngleOperator U V
  let K : BEnd H := R - C
  let z : BEnd H := imaginaryUnit
  let B : BEnd H := z * K
  let Fp : BEnd H := phasePlus C S
  let Fm : BEnd H := phaseMinus C S
  let Qp : BEnd H := phasePlus S C
  let Qm : BEnd H := phaseMinus S C
  let Tp : BEnd H := R * Fp
  let Tm : BEnd H := R * Fm
  obtain ⟨hRunit, hS0, hCstar, hSstar, hRC, hRS, hCS, hpy,
      hskew, hKmod, hCP, hSP⟩ := nonacute_phase_geometry U V J
  have hPhase := phase_mem_unitary C S hCstar hSstar hCS hpy
  have hQphase : Qp ∈ unitary (BEnd H) ∧
      Qm ∈ unitary (BEnd H) := by
    apply phase_mem_unitary S C hSstar hCstar hCS.symm
    simpa only [add_comm] using hpy
  have hTpunit : Tp ∈ unitary (BEnd H) := mul_mem hRunit hPhase.1
  have hTmunit : Tm ∈ unitary (BEnd H) := mul_mem hRunit hPhase.2
  have hFproj := phase_commutes_projection
    U.starProjection C S hCP hSP
  have hintertwinesR : R * U.starProjection = V.starProjection * R :=
    nonacuteDirectRotation_intertwines U V J
  have hintertwinesP : Tp * U.starProjection = V.starProjection * Tp := by
    dsimp [Tp, Fp]
    calc
      (R * phasePlus C S) * U.starProjection =
          R * (U.starProjection * phasePlus C S) := by
        rw [mul_assoc, hFproj.1]
      _ = (V.starProjection * R) * phasePlus C S := by
        rw [← mul_assoc, hintertwinesR]
      _ = V.starProjection * (R * phasePlus C S) := mul_assoc _ _ _
  have hintertwinesM : Tm * U.starProjection = V.starProjection * Tm := by
    dsimp [Tm, Fm]
    calc
      (R * phaseMinus C S) * U.starProjection =
          R * (U.starProjection * phaseMinus C S) := by
        rw [mul_assoc, hFproj.2]
      _ = (V.starProjection * R) * phaseMinus C S := by
        rw [← mul_assoc, hintertwinesR]
      _ = V.starProjection * (R * phaseMinus C S) := mul_assoc _ _ _
  let Wp : H ≃ₗᵢ[ℂ] H :=
    Unitary.linearIsometryEquiv (⟨Tp, hTpunit⟩ : unitary (BEnd H))
  let Wm : H ≃ₗᵢ[ℂ] H :=
    Unitary.linearIsometryEquiv (⟨Tm, hTmunit⟩ : unitary (BEnd H))
  have hmapP : U.map Wp.toLinearMap = V :=
    unitary_transport_of_intertwines U V hUV Tp hTpunit hintertwinesP
  have hmapM : U.map Wm.toLinearMap = V :=
    unitary_transport_of_intertwines U V hUV Tm hTmunit hintertwinesM
  have hB := imaginary_skew_modulus K S hskew hKmod hS0
  have hpos : 0 ≤ S - B ∧ 0 ≤ S + B :=
    abs_plus_minus_nonneg B hB.1 S hB.2
  have hfactor := phase_displacement_factors R C S hCS hpy
  have hDp : 1 - Tp = (S - B) * Qm := by
    change 1 - R * phasePlus C S =
      (S - imaginaryUnit * (R - C)) * (S - imaginaryUnit * C)
    exact hfactor.1
  have hDm : 1 - Tm = (S + B) * Qp := by
    change 1 - R * phaseMinus C S =
      (S + imaginaryUnit * (R - C)) * (S + imaginaryUnit * C)
    exact hfactor.2
  have htraceP : kyFanSum (finrank ℂ H)
      (LinearMap.id - Wp.toLinearMap) =
        kyFanSum (finrank ℂ H) (S - B).toLinearMap := by
    rw [kyFanSum_displacement_of_unitary Tp hTpunit, hDp]
    exact kyFanSum_mul_unitary_right (S - B) Qm hQphase.2
  have htraceM : kyFanSum (finrank ℂ H)
      (LinearMap.id - Wm.toLinearMap) =
        kyFanSum (finrank ℂ H) (S + B).toLinearMap := by
    rw [kyFanSum_displacement_of_unitary Tm hTmunit, hDm]
    exact kyFanSum_mul_unitary_right (S + B) Qp hQphase.1
  have htracePair :
      kyFanSum (finrank ℂ H) (S - B).toLinearMap +
          kyFanSum (finrank ℂ H) (S + B).toLinearMap =
        kyFanSum (finrank ℂ H) S.toLinearMap +
          kyFanSum (finrank ℂ H) S.toLinearMap := by
    calc
      kyFanSum (finrank ℂ H) (S - B).toLinearMap +
          kyFanSum (finrank ℂ H) (S + B).toLinearMap =
          kyFanSum (finrank ℂ H) ((S - B) + (S + B)).toLinearMap :=
        (kyFanSum_add_of_nonneg (S - B) (S + B) hpos.1 hpos.2).symm
      _ = kyFanSum (finrank ℂ H) (S + S).toLinearMap := by
        congr 1
        abel_nf
      _ = kyFanSum (finrank ℂ H) S.toLinearMap +
          kyFanSum (finrank ℂ H) S.toLinearMap :=
        kyFanSum_add_of_nonneg S S hS0 hS0
  have hprojtrace : kyFanSum (finrank ℂ H)
      (projection U - projection V) =
      kyFanSum (finrank ℂ H) S.toLinearMap :=
    kyFanSum_projector_eq_nonacute_sine U V
  have hboundP := projectionDifference_kyFanSum_le_displacement
    U V Wp hmapP (finrank ℂ H)
  have hboundM := projectionDifference_kyFanSum_le_displacement
    U V Wm hmapM (finrank ℂ H)
  have hOptimal : kyFanSum (finrank ℂ H)
      (LinearMap.id - Wp.toLinearMap) =
        kyFanSum (finrank ℂ H) (projection U - projection V) := by
    rw [hprojtrace] at hboundP hboundM ⊢
    rw [htraceP] at hboundP ⊢
    rw [htraceM] at hboundM
    linarith
  exact ⟨Wp, hmapP, hOptimal⟩

/-- Every other transporting unitary has at least the trace displacement of
our explicit phase-corrected completed rotation. -/
theorem exists_global_complex_trace_minimizer
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      U.map W.toLinearMap = V ∧
      kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ H) (projection U - projection V) ∧
      ∀ Z : H ≃ₗᵢ[ℂ] H, U.map Z.toLinearMap = V →
        kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ H) (LinearMap.id - Z.toLinearMap) := by
  obtain ⟨W, hW⟩ := exists_trace_optimal_unitary_of_equal_finrank U V hUV
  exact ⟨W, hW.1, hW.2, fun Z hZ => hW.le_competitor Z hZ⟩

end

end ComplexTraceOptimality
end DavisKahan.FiniteDimensional
end TauCeti
