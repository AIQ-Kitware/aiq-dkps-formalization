/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.DavisKahan.SharpIdeal
import DavisKahan.FiniteDimensional.DoubleAngle.TanTheta
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalReverseGap
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport

/-!
# Paper-faithful finite-dimensional `tan 2Theta` theorem

The literal Section 7 unitarily-invariant-norm theorem is a finite-dimensional
statement and allows any operator whose singular values are the double-angle
tangents of the principal angles.  It is therefore not the arbitrary-Hilbert,
canonical ambient-operator statement that an earlier version of this file
recorded.

This module proves the source-shaped result at its audited scope:

* `A` and `A + H` are self-adjoint;
* `H` is fully off-diagonal for `U + U-perp`;
* `U` and `V` are the corresponding reducing subspaces on the two sides of the
  same ordered form gap `[a,b]`;
* the strict quarter-turn branch is derived, not assumed;
* the graph-coordinate representative of `tan 2Theta` belongs to every source
  norm ideal containing `H`, with the sharp factor-two estimate.

The strict branch is supplied by the finite-dimensional GKMV/Davis--Kahan
operator-norm theorem.  Once the branch is known, the graph coordinate solves
the bounded Riccati equation.  The approximation-number proof in
`SharpIdeal` supplies the sharp source-norm estimate.  The upper-right block is
compared with the full perturbation by extending it by zero to the ambient
space; this preserves every approximation singular value.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open DavisKahanExt
open Experimental.ExactSinTheta

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The source-permitted graph-coordinate representative of `tan 2Theta`.
Its approximation singular values are the double-angle tangents of the
principal angles of the quarter-acute pair. -/
noncomputable def paperTanTwoThetaRepresentative
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    U →L[ℂ] Uᗮ := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator
    (TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate U V hquarter)
    (TauCeti.DavisKahanExt.norm_quarterAcuteAngularCoordinate_lt_one U V hquarter)

/-- Mapping the two summands into one another is exactly the ambient
off-diagonal condition consumed by the Riccati block API. -/
private theorem isOffDiagonal_of_maps_orthogonal
    (H : E →L[ℂ] E) (U : Submodule ℂ E)
    [U.HasOrthogonalProjection]
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    IsOffDiagonal U H := by
  change U.diagonalPart H = 0
  apply ContinuousLinearMap.ext
  intro x
  have hPzero : U.starProjection (H (U.starProjection x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff U).2
      (hHU (U.starProjection x) (U.starProjection_apply_mem x))
  have hQzero : Uᗮ.starProjection (H (Uᗮ.starProjection x)) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr
        (hHUperp (Uᗮ.starProjection x) (Uᗮ.starProjection_apply_mem x)),
      sub_self]
  simp only [Submodule.diagonalPart, ContinuousLinearMap.comp_apply,
    add_apply, hPzero, hQzero, add_zero, zero_apply]

/-- The finite-dimensional sharp operator-norm theorem gives the strict
quarter-turn branch from the source hypotheses. -/
private theorem isQuarterAcute_of_paper_form_gap
    [FiniteDimensional ℂ E]
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    IsQuarterAcute U V := by
  have hAsym : A.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hAHself : IsSelfAdjoint (A + H) := hA.add hH
  have hAHsym : (A + H).toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAHself
  have hdiagU : ∀ x ∈ U, ∀ y ∈ U,
      ⟪x, ((A + H).toLinearMap - A.toLinearMap) y⟫_ℂ = 0 := by
    intro x hx y hy
    have horth : ⟪x, H y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal U (H y)).mp (hHU y hy) x hx
    have hdiff : ((A + H).toLinearMap - A.toLinearMap) y = H y := by
      change (A + H) y - A y = H y
      simp only [add_apply]
      abel
    rwa [hdiff]
  have hdiagUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ,
      ⟪x, ((A + H).toLinearMap - A.toLinearMap) y⟫_ℂ = 0 := by
    intro x hx y hy
    have horth : ⟪x, H y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal' U x).mp hx (H y) (hHUperp y hy)
    have hdiff : ((A + H).toLinearMap - A.toLinearMap) y = H y := by
      change (A + H) y - A y = H y
      simp only [add_apply]
      abel
    rwa [hdiff]
  have hpert : ∀ x : E,
      ‖((A + H).toLinearMap - A.toLinearMap) x‖ ≤ ‖H‖ * ‖x‖ := by
    intro x
    have hdiff : ((A + H).toLinearMap - A.toLinearMap) x = H x := by
      change (A + H) x - A x = H x
      simp only [add_apply]
      abel
    rw [hdiff]
    exact H.le_opNorm x
  have hbranch := TauCeti.tan_two_theta_norm_sub_le
    (T := A.toLinearMap) (S := (A + H).toLinearMap)
    hAsym hAHsym hAU hAplusH_V hab (norm_nonneg H)
    hUhigh hUperpLow hVhigh hVperpLow hdiagU hdiagUperp hpert
  change ‖U.starProjection - V.starProjection‖ < Real.sqrt 2 / 2
  have hsq : ‖U.starProjection - V.starProjection‖ ^ 2 < (1 : ℝ) / 2 :=
    hbranch.1
  have hthresholdSq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hthresholdPos : 0 < Real.sqrt 2 / 2 := by positivity
  by_contra hnot
  have hle : Real.sqrt 2 / 2 ≤ ‖U.starProjection - V.starProjection‖ :=
    le_of_not_gt hnot
  have hsqle := pow_le_pow_left₀ hthresholdPos.le hle 2
  rw [hthresholdSq] at hsqle
  exact (not_le_of_gt hsq) hsqle

/-- The ambient extension by zero of the upper-right perturbation block is the
corresponding double compression of the full perturbation. -/
private theorem ambientUpperRightBlock_eq
    (H : E →L[ℂ] E) (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] [CompleteSpace U]
    [CompleteSpace (Uᗮ : Submodule ℂ E)]
    (B01 : Uᗮ →L[ℂ] U)
    (hB01 : B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL) :
    U.subtypeL ∘L B01 ∘L Uᗮ.subtypeL.adjoint =
      U.starProjection ∘L H ∘L Uᗮ.starProjection := by
  rw [hB01, Submodule.adjoint_subtypeL]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- **Paper-faithful Davis--Kahan `tan 2Theta` theorem at the audited Section
7 scope.**

For a finite-dimensional Hilbert space and a fully off-diagonal self-adjoint
perturbation across a common ordered gap, the reducing subspaces are strictly
quarter-acute.  Every source unitary-invariant norm that contains the full
perturbation also contains the graph-coordinate `tan 2Theta` representative,
and

`(b - a) * N(tan 2Theta_0) <= 2 * N(H)`.

The representative freedom is exactly the one stated in the paper: no claim is
made here that the rectangular graph-coordinate operator is definitionally the
ambient canonical operator `tanTwoAngleOperatorC`. -/
theorem paperFaithful_tanTwoTheta_uiNorm
    [FiniteDimensional ℂ E]
    (N : PaperUnitaryInvariantNorm)
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    ∃ hquarter : IsQuarterAcute U V,
      N.Mem (paperTanTwoThetaRepresentative U V hquarter) ∧
        (b - a) * N.gauge (paperTanTwoThetaRepresentative U V hquarter) ≤
          2 * N.gauge H := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hquarter : IsQuarterAcute U V :=
    isQuarterAcute_of_paper_form_gap A H U V hA hH hAU hAplusH_V hab
      hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp
  refine ⟨hquarter, ?_⟩
  have hAsym : IsSelfAdjointOperator A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hHsym : IsSelfAdjointOperator H :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hAHsym : IsSelfAdjointOperator (A + H) := by
    have h := hAsym.add hHsym
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  have hUreduces : Reduces A U := reduces_orthogonalComplement hAsym hAU
  have hVreduces : Reduces (A + H) V :=
    reduces_orthogonalComplement hAHsym hAplusH_V
  have hoff : IsOffDiagonal U H :=
    isOffDiagonal_of_maps_orthogonal H U hHU hHUperp
  let B : BlockOperatorData (𝕜 := ℂ) (E0 := U) (E1 := Uᗮ) :=
    TauCeti.DavisKahanExt.subspaceBlockOperatorData (A + H) U hAHsym
  let X : U →L[ℂ] Uᗮ :=
    TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate U V hquarter
  let C := TauCeti.DavisKahanExt.negBlockOperatorData B
  let D := TauCeti.DavisKahanExt.shiftBlockOperatorData C (-b)
  have hsolveB : SolvesRiccati B X := by
    simpa only [B, X] using
      TauCeti.DavisKahanExt.quarterAcuteAngularCoordinate_solvesRiccati
        A H hAsym hHsym U V hVreduces hquarter
  have hsolveC : SolvesRiccati C X := by
    exact (TauCeti.DavisKahanExt.solvesRiccati_negBlockOperatorData_iff B X).2 hsolveB
  have hsolveD : SolvesRiccati D X := by
    exact (TauCeti.DavisKahanExt.solvesRiccati_shiftBlockOperatorData_iff C (-b) X).2 hsolveC
  have hB0 : B.A0 = compressOperator U A := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_A0_add_offDiagonal
        A H U hAHsym hoff
  have hB1 : B.A1 = compressOperator Uᗮ A := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_A1_add_offDiagonal
        A H U hAHsym hoff
  have hB01 : B.B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL := by
    simpa only [B] using
      TauCeti.DavisKahanExt.subspaceBlockOperatorData_B01_add_of_reduces
        A H U hAHsym hUreduces
  have hB0high : ∀ z : U,
      b * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A0 z, z⟫_ℂ := by
    intro z
    rw [hB0]
    have hAz : A (z : E) ∈ U := hAU (z : E) z.property
    change b * ‖(z : E)‖ ^ 2 ≤
      RCLike.re ⟪U.orthogonalProjectionOnto (A (z : E)), z⟫_ℂ
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr hAz]
    exact hUhigh (z : E) z.property
  have hB1low : ∀ z : Uᗮ,
      RCLike.re ⟪B.A1 z, z⟫_ℂ ≤ a * ‖z‖ ^ 2 := by
    intro z
    rw [hB1]
    have hAz : A (z : E) ∈ Uᗮ := hUreduces.2 (z : E) z.property
    change RCLike.re
        ⟪Uᗮ.orthogonalProjectionOnto (A (z : E)), z⟫_ℂ ≤
      a * ‖(z : E)‖ ^ 2
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.starProjection_eq_self_iff.mpr hAz]
    exact hUperpLow (z : E) z.property
  have hC0upper : ∀ z : U,
      RCLike.re ⟪C.A0 z, z⟫_ℂ ≤ (-b) * ‖z‖ ^ 2 := by
    intro z
    have hz := hB0high z
    dsimp only [C, TauCeti.DavisKahanExt.negBlockOperatorData]
    simp only [neg_apply, inner_neg_left, map_neg]
    linarith
  have hC1lower : ∀ z : Uᗮ,
      ((-b) + (b - a)) * ‖z‖ ^ 2 ≤ RCLike.re ⟪C.A1 z, z⟫_ℂ := by
    intro z
    have hz := hB1low z
    dsimp only [C, TauCeti.DavisKahanExt.negBlockOperatorData]
    simp only [neg_apply, inner_neg_left, map_neg]
    linarith
  have hD0 : ∀ z : U, RCLike.re ⟪D.A0 z, z⟫_ℂ ≤ 0 := by
    simpa only [D] using
      TauCeti.DavisKahanExt.shiftBlockOperatorData_A0_nonpos C (-b) hC0upper
  have hD1 : ∀ z : Uᗮ,
      (b - a) * ‖z‖ ^ 2 ≤ RCLike.re ⟪D.A1 z, z⟫_ℂ := by
    simpa only [D] using
      TauCeti.DavisKahanExt.shiftBlockOperatorData_A1_lower
        C (-b) (b - a) hC1lower
  let Camb : E →L[ℂ] E := U.starProjection ∘L H ∘L Uᗮ.starProjection
  have hCambMem : N.Mem Camb := by
    dsimp only [Camb]
    exact N.comp_mem hHmem U.starProjection Uᗮ.starProjection
  have hCambGauge : N.gauge Camb ≤ N.gauge H := by
    dsimp only [Camb]
    exact N.gauge_comp_le_of_contractions hHmem
      U.starProjection Uᗮ.starProjection
      U.starProjection_norm_le Uᗮ.starProjection_norm_le
  have hseqB : SameApproximationSingularSequence Camb B.B01 := by
    have hseq := sameApproximationSingularValues_ambientSubspaceBlock
      Uᗮ U B.B01
    have hext : U.subtypeL ∘L B.B01 ∘L Uᗮ.subtypeL.adjoint = Camb := by
      simpa only [Camb] using ambientUpperRightBlock_eq H U B.B01 hB01
    rw [hext] at hseq
    exact hseq
  have htransport := hseqB.paperMem_iff_and_gauge_eq N
  have hBmem : N.Mem B.B01 := htransport.1.mp hCambMem
  have hBgauge : N.gauge B.B01 = N.gauge Camb := htransport.2.symm
  have hCmem : N.Mem C.B01 := by
    have hnegmem : N.Mem ((-1 : ℂ) • B.B01) := by
      unfold PaperUnitaryInvariantNorm.Mem at hBmem ⊢
      rw [N.extendedGauge_smul]
      norm_num
      exact hBmem
    simpa only [C, TauCeti.DavisKahanExt.negBlockOperatorData, neg_one_smul] using hnegmem
  have hC_B01_gauge : N.gauge C.B01 = N.gauge B.B01 := by
    have hnegGauge :
        N.gauge ((-1 : ℂ) • B.B01) = N.gauge B.B01 := by
      rw [N.gauge_smul (-1 : ℂ) hBmem]
      norm_num
    simpa only [C, TauCeti.DavisKahanExt.negBlockOperatorData, neg_one_smul] using hnegGauge
  have hDB01 : D.B01 = C.B01 := rfl
  have hDmem : N.Mem D.B01 := by
    rw [hDB01]
    exact hCmem
  have hcontractive : ‖X‖ < 1 := by
    simpa only [X] using
      TauCeti.DavisKahanExt.norm_quarterAcuteAngularCoordinate_lt_one
        U V hquarter
  have hsharp := sharp_paperUnitaryInvariantNorm
    N D (sub_pos.mpr hab) hD0 hD1 hsolveD hcontractive hDmem
  change N.Mem (paperTanTwoThetaRepresentative U V hquarter) ∧
      (b - a) * N.gauge (paperTanTwoThetaRepresentative U V hquarter) ≤
        2 * N.gauge H
  have hrepresentative :
      paperTanTwoThetaRepresentative U V hquarter =
        TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator X hcontractive := by
    rfl
  rw [hrepresentative]
  refine ⟨hsharp.1, hsharp.2.trans ?_⟩
  calc
    2 * N.gauge D.B01 = 2 * N.gauge C.B01 := by rw [hDB01]
    _ = 2 * N.gauge B.B01 := by rw [hC_B01_gauge]
    _ = 2 * N.gauge Camb := by rw [hBgauge]
    _ ≤ 2 * N.gauge H :=
      mul_le_mul_of_nonneg_left hCambGauge (by norm_num)

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
