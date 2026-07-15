/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Compatibility

/-!
# Operator angles between closed subspaces

All angle functions are built from the single positive contraction
`S = |P_U-P_V|`.  The angle is `arcsin S`, the cosine is
`sqrt (1-S²)`, and the tangent operators are defined only when the relevant
cosine has a bounded inverse.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Absolute value `(T* T)^(1/2)` of a bounded operator. -/
noncomputable def operatorAbsoluteValue (T : E →L[𝕜] E) : E →L[𝕜] E :=
  RCLikeContinuousFunctionalCalculus.sqrt (star T * T)

/-- Absolute values are positive. -/
theorem operatorAbsoluteValue_nonneg (T : E →L[𝕜] E) :
    0 ≤ operatorAbsoluteValue T :=
  RCLikeContinuousFunctionalCalculus.sqrt_nonneg _

/-- Absolute values are self-adjoint. -/
theorem operatorAbsoluteValue_isSelfAdjoint (T : E →L[𝕜] E) :
    IsSelfAdjoint (operatorAbsoluteValue T) :=
  (operatorAbsoluteValue_nonneg T).isSelfAdjoint

/-- Squaring the absolute value gives `T* T`. -/
theorem operatorAbsoluteValue_mul_self (T : E →L[𝕜] E) :
    operatorAbsoluteValue T * operatorAbsoluteValue T = star T * T := by
  exact RCLikeContinuousFunctionalCalculus.sqrt_sq
    (star_mul_self_nonneg T)

/-- Absolute value has the same operator norm. -/
theorem norm_operatorAbsoluteValue (T : E →L[𝕜] E) :
    ‖operatorAbsoluteValue T‖ = ‖T‖ := by
  have hsquare := operatorAbsoluteValue_mul_self T
  have hnonneg := operatorAbsoluteValue_nonneg T
  calc
    ‖operatorAbsoluteValue T‖ ^ 2
        = ‖operatorAbsoluteValue T * operatorAbsoluteValue T‖ := by
          rw [CStarRing.norm_mul_self hnonneg.isSelfAdjoint]
    _ = ‖star T * T‖ := by rw [hsquare]
    _ = ‖T‖ ^ 2 := CStarRing.norm_star_mul_self T
  exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp this

/-- Absolute value is insensitive to a sign. -/
theorem operatorAbsoluteValue_neg (T : E →L[𝕜] E) :
    operatorAbsoluteValue (-T) = operatorAbsoluteValue T := by
  unfold operatorAbsoluteValue
  congr 1
  simp

/-- Sine of the operator angle, in the full ambient multiplicity convention. -/
noncomputable def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  operatorAbsoluteValue (projection U - projection V)

/-- The sine operator is positive. -/
theorem sinAngleOperator_nonneg
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : 0 ≤ sinAngleOperator U V :=
  operatorAbsoluteValue_nonneg _

/-- Squared sine is the squared projection difference. -/
theorem sinAngleOperator_sq
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    sinAngleOperator U V * sinAngleOperator U V =
      (projection U - projection V) * (projection U - projection V) := by
  rw [sinAngleOperator, operatorAbsoluteValue_mul_self]
  have hself : IsSelfAdjoint (projection U - projection V) :=
    (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  rw [hself.star_eq]

/-- The sine operator is a positive contraction. -/
theorem sinAngleOperator_le_one
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : sinAngleOperator U V ≤ 1 := by
  apply positive_le_one_of_norm_le_one (sinAngleOperator_nonneg U V)
  rw [sinAngleOperator, norm_operatorAbsoluteValue]
  exact Submodule.norm_starProjection_sub_le_one U V

/-- Cosine of the operator angle. -/
noncomputable def cosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  RCLikeContinuousFunctionalCalculus.sqrt
    (1 - sinAngleOperator U V * sinAngleOperator U V)

/-- The cosine operator is positive. -/
theorem cosAngleOperator_nonneg
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : 0 ≤ cosAngleOperator U V :=
  RCLikeContinuousFunctionalCalculus.sqrt_nonneg _

/-- Squared cosine is `1-S²`. -/
theorem cosAngleOperator_sq
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    cosAngleOperator U V * cosAngleOperator U V =
      1 - sinAngleOperator U V * sinAngleOperator U V := by
  apply RCLikeContinuousFunctionalCalculus.sqrt_sq
  exact one_sub_sq_nonneg_of_nonneg_le_one
    (sinAngleOperator_nonneg U V) (sinAngleOperator_le_one U V)

/-- Sine and cosine commute because both are continuous functions of `S`. -/
theorem sinAngleOperator_comm_cosAngleOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Commute (sinAngleOperator U V) (cosAngleOperator U V) := by
  unfold cosAngleOperator
  exact RCLikeContinuousFunctionalCalculus.commute_sqrt_of_commute
    ((Commute.refl (sinAngleOperator U V)).sub_right
      ((Commute.refl (sinAngleOperator U V)).mul_right
        (Commute.refl (sinAngleOperator U V))))

/-- Operator Pythagorean identity. -/
theorem sin_sq_add_cos_sq
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    sinAngleOperator U V * sinAngleOperator U V +
      cosAngleOperator U V * cosAngleOperator U V = 1 := by
  rw [cosAngleOperator_sq]
  abel

/-- Positive operator angle `arcsin |P-Q|`. -/
noncomputable def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  RCLikeContinuousFunctionalCalculus.applyOnSpectrum Real.arcsin
    (sinAngleOperator U V)
    (sinAngleOperator_nonneg U V)
    (spectrum_nonneg_contraction_subset
      (sinAngleOperator_nonneg U V) (sinAngleOperator_le_one U V))

/-- Applying sine to the angle recovers the sine operator. -/
theorem sin_angleOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    RCLikeContinuousFunctionalCalculus.applyOnSpectrum Real.sin
      (angleOperator U V)
      (angleOperator_nonneg U V)
      (spectrum_angleOperator_subset U V) = sinAngleOperator U V := by
  unfold angleOperator
  rw [RCLikeContinuousFunctionalCalculus.comp_applyOnSpectrum]
  apply RCLikeContinuousFunctionalCalculus.congr_on_spectrum
  intro x hx
  have hxIcc := spectrum_sinAngleOperator_subset U V hx
  exact Real.sin_arcsin hxIcc.1 hxIcc.2

/-- In the acute case, cosine is a unit. -/
theorem cosAngleOperator_isUnit_of_acute
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    IsUnit (cosAngleOperator U V) := by
  have hnorm : ‖sinAngleOperator U V‖ < 1 := by
    simpa [sinAngleOperator, norm_operatorAbsoluteValue, subspaceGap] using hacute
  have hlower : ∀ λ ∈ spectrum ℝ (cosAngleOperator U V),
      0 < λ := by
    intro λ hλ
    obtain ⟨s, hs, rfl⟩ := spectrum_cosAngleOperator_image U V hλ
    have hslt : s < 1 := le_lt_trans
      (spectralValue_le_norm hs) hnorm
    positivity
  exact isUnit_of_zero_not_mem_spectrum
    (fun hzero => by simpa using hlower 0 hzero)

/-- Bounded tangent of the operator angle in the acute regime. -/
noncomputable def tanAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →L[𝕜] E :=
  let Cunit := (cosAngleOperator_isUnit_of_acute U V hacute).unit
  sinAngleOperator U V * ((Cunit⁻¹ : (E →L[𝕜] E)ˣ) : E →L[𝕜] E)

/-- Sine of twice the operator angle. -/
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (2 : 𝕜) • (sinAngleOperator U V * cosAngleOperator U V)

/-- Cosine of twice the operator angle. -/
noncomputable def cosTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  cosAngleOperator U V * cosAngleOperator U V -
    sinAngleOperator U V * sinAngleOperator U V

/-- Below the quarter-angle threshold the double-angle cosine is a unit. -/
theorem cosTwoAngleOperator_isUnit_of_quarterAcute
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    IsUnit (cosTwoAngleOperator U V) := by
  have hnorm : ‖sinAngleOperator U V‖ < Real.sqrt 2 / 2 := by
    simpa [sinAngleOperator, norm_operatorAbsoluteValue, subspaceGap] using hquarter
  apply isUnit_of_strictlyPositive
  exact cosTwoAngleOperator_strictlyPositive_of_sin_norm_lt U V hnorm

/-- Bounded tangent of twice the angle. -/
noncomputable def tanTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hquarter : IsQuarterAcute U V) : E →L[𝕜] E :=
  let Cunit := (cosTwoAngleOperator_isUnit_of_quarterAcute U V hquarter).unit
  sinTwoAngleOperator U V * ((Cunit⁻¹ : (E →L[𝕜] E)ˣ) : E →L[𝕜] E)

/-- An angular operator maps `U` into `Uᗮ` and vanishes on `Uᗮ`. -/
def IsAngularOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Prop :=
  X ∘L projection U = X ∧ projection U ∘L X = 0

/-- Maximal operator angle. -/
noncomputable def maximalAngle (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  Real.arcsin (subspaceGap U V)

/-- The sine operator is definitionally the modulus of the projector difference. -/
theorem sinAngleOperator_eq_abs_projection_sub
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    sinAngleOperator U V =
      operatorAbsoluteValue (projection U - projection V) := rfl

/-- Norm of the sine operator. -/
theorem norm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperator U V‖ = subspaceGap U V := by
  rw [sinAngleOperator, norm_operatorAbsoluteValue]
  rfl

/-- For acute pairs the directed and symmetric gaps coincide. -/
theorem directedGap_eq_subspaceGap_of_acute
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : IsAcute U V) :
    directedGap U V = subspaceGap U V := by
  have hdefU : U ⊓ Vᗮ = ⊥ :=
    Submodule.inf_orthogonal_eq_bot_of_projectionGap_lt_one U V h
  have hdefV : V ⊓ Uᗮ = ⊥ :=
    Submodule.inf_orthogonal_eq_bot_of_projectionGap_lt_one V U
      (by simpa [Submodule.projectionGap_comm] using h)
  have hreverse : directedGap U V = directedGap V U :=
    Submodule.directedProjectionGap_eq_reverse_of_defects_bot
      U V hdefU hdefV
  rw [subspaceGap, Submodule.norm_starProjection_sub_eq_max]
  simp [directedGap, hreverse]

/-- Acute subspaces are exactly bounded graphs over either member of the pair. -/
theorem acute_iff_exists_bounded_angularOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    IsAcute U V ↔ ∃ X : E →L[𝕜] E,
      IsAngularOperator U X ∧
      V = LinearMap.range (projection U + X ∘L projection U).toLinearMap := by
  constructor
  · intro hacute
    let T : V →L[𝕜] U := projectionRestriction U V
    have hbelow := projectionRestriction_boundedBelow_of_gap_lt_one U V hacute
    have hsurj := projectionRestriction_surjective_of_gap_lt_one U V hacute
    let e : V ≃L[𝕜] U := ContinuousLinearEquiv.ofBijective T hbelow.injective hsurj
    let X : E →L[𝕜] E :=
      Uᗮ.subtypeL ∘L
        (complementaryProjectionRestriction U V) ∘L
        e.symm.toContinuousLinearMap ∘L U.orthogonalProjectionOnto
    refine ⟨X, ?_, ?_⟩
    · constructor
      · ext x
        simp [X, ContinuousLinearMap.comp_assoc]
      · ext x
        simp [X, ContinuousLinearMap.comp_assoc]
    · ext x
      constructor
      · intro hx
        let v : V := ⟨x, hx⟩
        refine ⟨projection U x, ?_⟩
        apply congrArg Subtype.val (e.apply_symm_apply (T v)) |>.trans
        ext <;> simp [X, T, e, v]
      · rintro ⟨u, rfl⟩
        let v := e.symm ⟨projection U u, U.starProjection_apply_mem u⟩
        exact ⟨v, by ext <;> simp [X, T, e, v]⟩
  · rintro ⟨X, hX, hgraph⟩
    rw [hgraph, projectionGap_graph_of_angular U X hX]
    have hsqrt : ‖X‖ < Real.sqrt (1 + ‖X‖^2) := by
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖X‖^2)]
    exact (div_lt_one (Real.sqrt_pos.2 (by positivity))).2 hsqrt

/-- The graph angular norm is the tangent of the maximal angle. -/
theorem norm_angularOperator_eq_tan_maximalAngle
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : IsAcute U V) :
    ∃ X : E →L[𝕜] E,
      IsAngularOperator U X ∧
      V = LinearMap.range (projection U + X ∘L projection U).toLinearMap ∧
      ‖X‖ = Real.tan (maximalAngle U V) := by
  obtain ⟨X, hX, hgraph⟩ :=
    (acute_iff_exists_bounded_angularOperator U V).mp h
  refine ⟨X, hX, hgraph, ?_⟩
  have hgap := projectionGap_graph_of_angular U X hX
  rw [maximalAngle, hgraph, hgap, Real.tan_arcsin]
  have hroot : Real.sqrt (1 -
      (‖X‖ / Real.sqrt (1 + ‖X‖^2))^2) =
      1 / Real.sqrt (1 + ‖X‖^2) := by
    apply Real.sq_sqrt_eq_iff.2
    constructor
    · positivity
    · field_simp [Real.sqrt_ne_zero'.2 (by positivity : 0 < 1 + ‖X‖^2)]
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖X‖^2)]
  rw [hroot]
  field_simp [Real.sqrt_ne_zero'.2 (by positivity : 0 < 1 + ‖X‖^2)]

/-- Complementing both subspaces preserves the operator angle. -/
theorem angleOperator_orthogonalComplement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    angleOperator Uᗮ Vᗮ = angleOperator U V := by
  have hdiff : projection Uᗮ - projection Vᗮ =
      -(projection U - projection V) := by
    rw [Submodule.starProjection_orthogonal',
      Submodule.starProjection_orthogonal']
    abel
  unfold angleOperator sinAngleOperator
  rw [hdiff, operatorAbsoluteValue_neg]

/-- Triangle inequality for the maximal angle. -/
theorem maximalAngle_triangle
    (U V W : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    maximalAngle U W ≤ maximalAngle U V + maximalAngle V W := by
  exact Submodule.maximalProjectionAngle_triangle U V W

end DavisKahanExt
end ForMathlib
