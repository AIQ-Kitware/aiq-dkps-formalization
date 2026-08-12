/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Geometry.Angle.Proposition35Infinite
import DavisKahan.Geometry.Polar.Section3Nonacute

/-!
# Davis--Kahan 1970, Proposition 3.5, in arbitrary Hilbert dimension

This file is the paper-facing surface for Proposition 3.5.  The proposition is
stated in Section 3 for an acute pair of closed subspaces in a real or complex
Hilbert space, without a finite-dimensional hypothesis.

The implementation in `DavisKahan.Geometry.Angle.Proposition35Infinite`
constructs the literal bounded angle

`Theta = arcsin |P - Q|`,

the acute direct rotation `W`, and the quarter turn `J` from the polar
resolution

`W = cos Theta + J sin Theta`.

The theorems below expose the six printed assertions: the four commutations,
the vector-angle identity on an angle eigenvector, and the unique maximality of
the corresponding angle eigenspace under the paper's conditions (a)--(c).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open DavisKahan
open DavisKahan.Frontier.Section3
open DavisKahan.Proposition35

noncomputable section

/-- The literal operator angle used in Proposition 3.5. -/
alias proposition3_5_angleOperator := section3AngleOperator

/-- The paper's direct rotation in Proposition 3.5. -/
alias proposition3_5_directRotation := section3DirectRotation

/-- The paper's quarter turn `J`, zero on the zero-angle space. -/
alias proposition3_5_quarterTurn := section3QuarterTurn

/-- The assembled regular-and-defect quarter-turn candidate for a general pair.
The two summands act on orthogonal blocks. -/
noncomputable def corollary3_2_quarterTurn
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]
    [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
    [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  section3QuarterTurn U V + crossedDefectQuarterTurn U V J

/-- The spectral eigenspace `Omega({theta}) H` at an angle eigenvalue. -/
alias proposition3_5_angleEigenspace := section3AngleEigenspace

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The defining polar resolution of the quarter turn used by Proposition 3.5:
`W = cos Theta + J sin Theta`. -/
theorem proposition3_5_directRotation_resolution (hacute : TauCeti.IsAcute U V) :
    proposition3_5_directRotation U V =
      section3CosAngleOperator U V +
        proposition3_5_quarterTurn U V ∘L section3SinAngleOperator U V :=
  section3DirectRotation_eq_cos_add_quarterTurn_sin U V hacute

/-- Interchanging the subspaces leaves the arbitrary-dimensional bounded angle unchanged. -/
theorem corollary3_2_angleOperator_symm :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V :=
  section3AngleOperator_symm U V

/-- On the acute branch, the arbitrary-dimensional quarter turn used in the paper's polar
resolution changes sign when the subspaces are interchanged. -/
theorem corollary3_2_quarterTurn_symm :
    proposition3_5_quarterTurn V U = -proposition3_5_quarterTurn U V :=
  section3QuarterTurn_symm U V

/-- The paper's quarter turn for the completed nonacute direct rotation.
It is defined by the same polar construction as on the acute branch. -/
noncomputable def corollary3_2_paperQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  (nonacuteDirectRotation U V J - section3CosAngleOperator U V).polarPartial

/-- The skew part of every completed nonacute direct rotation has modulus
exactly `sin Theta`. -/
theorem corollary3_2_nonacute_skew_modulus
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    (nonacuteDirectRotation U V J - section3CosAngleOperator U V).modulus =
      section3SinAngleOperator U V := by
  let W := nonacuteDirectRotation U V J
  let C := section3CosAngleOperator U V
  let S := section3SinAngleOperator U V
  let D := W - C
  have hunit : W ∈ unitary (H →L[𝕜] H) :=
    nonacuteDirectRotation_mem_unitary U V J
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum0 := nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hsum : W + star W = C + C := by
    simpa [W, C, hCeq] using hsum0
  have hcommAbs := nonacuteDirectRotation_comm_absoluteValue U V J
  have hWC : Commute W C := by
    simpa [W, C, hCeq] using hcommAbs
  have hWC' : W * C = C * W := hWC.eq
  have hstarW : star W = C + C - W := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hsum
  have hWstarW : (C + C - W) * W = 1 := by
    rw [← hstarW]
    exact Unitary.star_mul_self_of_mem hunit
  have hpy := section3Sin_sq_add_cos_sq U V
  have hpy' : S * S + C * C = 1 := by
    simpa [S, C] using hpy
  have hCsa : star C = C :=
    (cfc_predicate Real.cos (section3AngleOperator U V)).star_eq
  have hgram : star D * D = S * S := by
    dsimp [D]
    rw [star_sub, hCsa, hstarW]
    calc
      (C + C - W - C) * (W - C) = (C + C - W) * W - C * C := by
        noncomm_ring [hWC']
      _ = 1 - C * C := by rw [hWstarW]
      _ = S * S := (eq_sub_of_add_eq hpy').symm
  have hS0 : 0 ≤ S := section3SinAngleOperator_nonneg U V
  have hmod : S = D.modulus := by
    refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq hS0 ?_
    have hgram' : S * S = star D * D := hgram.symm
    rw [ContinuousLinearMap.star_eq_adjoint] at hgram'
    simpa only [ContinuousLinearMap.mul_def] using hgram'
  exact hmod.symm

/-- The full nonacute polar resolution from the paper: `W = cos Theta + J sin Theta`. -/
theorem corollary3_2_nonacute_directRotation_resolution
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      section3CosAngleOperator U V +
        corollary3_2_paperQuarterTurn U V J ∘L section3SinAngleOperator U V := by
  let D := nonacuteDirectRotation U V J - section3CosAngleOperator U V
  have hmod := corollary3_2_nonacute_skew_modulus U V J
  have hpolar := D.polarPartial_comp_modulus
  have hD : corollary3_2_paperQuarterTurn U V J ∘L
      section3SinAngleOperator U V = D := by
    rw [corollary3_2_paperQuarterTurn, ← hmod]
    exact hpolar
  rw [hD]
  dsimp [D]
  abel

/-- Reversing the ordered pair and the crossed-defect choice negates the paper's
quarter turn. -/
theorem corollary3_2_paperQuarterTurn_symm
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    corollary3_2_paperQuarterTurn V U (swapCrossedDefectEquiv U V J) =
      -corollary3_2_paperQuarterTurn U V J := by
  rw [corollary3_2_paperQuarterTurn, corollary3_2_paperQuarterTurn]
  have hW := nonacuteDirectRotation_swap U V J
  have hC := section3CosAngleOperator_symm U V
  have hsum0 := nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum :
      nonacuteDirectRotation U V J + star (nonacuteDirectRotation U V J) =
        section3CosAngleOperator U V + section3CosAngleOperator U V := by
    simpa [hCeq] using hsum0
  have hD :
      nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) -
          section3CosAngleOperator V U =
        -(nonacuteDirectRotation U V J - section3CosAngleOperator U V) := by
    rw [hW, hC]
    have hsW : star (nonacuteDirectRotation U V J) =
        section3CosAngleOperator U V + section3CosAngleOperator U V -
          nonacuteDirectRotation U V J := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using hsum
    rw [hsW]
    abel
  rw [hD, ContinuousLinearMap.polarPartial_neg]

/-- Full-scope Corollary 3.2 for a chosen direct rotation: the angle is symmetric,
the paper quarter turn changes sign, and the reversed direct rotation is the
adjoint. -/
theorem corollary3_2_source
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V ∧
      corollary3_2_paperQuarterTurn V U (swapCrossedDefectEquiv U V J) =
        -corollary3_2_paperQuarterTurn U V J ∧
      nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
        star (nonacuteDirectRotation U V J) :=
  ⟨section3AngleOperator_symm U V,
    corollary3_2_paperQuarterTurn_symm U V J,
    nonacuteDirectRotation_swap U V J⟩

/-- Reversal symmetry for the general chosen-defect quarter-turn construction.
For any chosen identification of the crossed defects, reversing the ordered
pair uses the inverse identification.  The operator angle is unchanged and the
assembled quarter turn changes sign. -/
theorem corollary3_2_chosenDefect_symmetry
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V ∧
      corollary3_2_quarterTurn V U (swapCrossedDefectEquiv U V J) =
        -corollary3_2_quarterTurn U V J := by
  refine ⟨section3AngleOperator_symm U V, ?_⟩
  rw [corollary3_2_quarterTurn, corollary3_2_quarterTurn,
    section3QuarterTurn_symm U V, crossedDefectQuarterTurn_swap U V J]
  abel

/-- The corresponding chosen nonacute direct rotation reverses to its adjoint. -/
theorem corollary3_2_directRotation_swap
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
      star (nonacuteDirectRotation U V J) :=
  nonacuteDirectRotation_swap U V J

/-- **Davis--Kahan 1970, Proposition 3.5, the four commutation assertions.**
In the acute case `Theta` commutes with `P`, `Q`, the quarter turn `J`, and the
direct rotation `W`. -/
theorem proposition3_5_commutations (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (TauCeti.DavisKahan.projection U) ∧
      Commute (proposition3_5_angleOperator U V) (TauCeti.DavisKahan.projection V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  ⟨section3AngleOperator_comm_projection U V,
    section3AngleOperator_comm_projection_right U V,
    section3AngleOperator_comm_quarterTurn U V hacute,
    section3AngleOperator_comm_directRotation U V hacute⟩

/-- **Davis--Kahan 1970, Proposition 3.5, eigenvector assertion.**
If `x` is a nonzero eigenvector of `Theta` with eigenvalue `theta`, the vector
angle from `x` to its direct rotation is exactly `theta`.  `vectorAngle` is the
paper's vector angle (1.14), using the real part of the inner product. -/
theorem proposition3_5_eigenvector_angle (hacute : TauCeti.IsAcute U V)
    {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : proposition3_5_angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (proposition3_5_directRotation U V x) = θ :=
  vectorAngle_section3DirectRotation_eq_of_angleOperator_apply U V hacute hx0 hx

/-- The actual angle eigenspace is the fixed-cosine Halmos eigenspace used by
the paper's maximality argument. -/
theorem proposition3_5_angleEigenspace_eq_fixedCosineSubspace
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    proposition3_5_angleEigenspace U V θ = fixedCosineSubspace U V (Real.cos θ) :=
  section3AngleEigenspace_eq_fixedCosineSubspace U V hacute hθ

/-- **Davis--Kahan 1970, Proposition 3.5, maximal-eigenspace assertion.**
For every genuine angle eigenvalue `theta`, `Omega({theta}) H` itself has the
printed properties (a)--(c), and every subspace having those printed properties
is contained in it.  Thus it is the unique maximal such subspace. -/
theorem proposition3_5_angleEigenspace_uniqueMaximal
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    IsPrintedFixedCosineReducingSubspace U V
        (proposition3_5_angleEigenspace U V θ) (Real.cos θ) ∧
      ∀ M : Submodule 𝕜 H,
        IsPrintedFixedCosineReducingSubspace U V M (Real.cos θ) →
          M ≤ proposition3_5_angleEigenspace U V θ := by
  have h := proposition3_5_angleEigenspace_maximal U V hacute hθ
  exact
    ⟨isPrintedFixedCosineReducingSubspace_of_isFixedCosineReducingSubspace
        U V (Real.cos θ) h.1,
      h.2⟩

end Generic

end

end DavisKahan1970
end TauCeti
