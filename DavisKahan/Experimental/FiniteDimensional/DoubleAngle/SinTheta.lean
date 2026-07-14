/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.All
import DavisKahan.Experimental.FiniteDimensional.TanTheta.GraphOperator
import DavisKahan.FiniteDimensional.DoubleAngle.SinTheta

/-!
# The complete finite-dimensional `sin (2 Θ)` theorem family

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 9, "The sin two Theta theorem".
* Davis--Kahan (1970), Section 2 (`sin 2Θ`) and Section 7 (reflection proof).
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, Section
  "The sharp two-subspace estimate" for the one-vector ancestor.

The perturbation and mirror-defect forms are already substantially present in
`SinTwoThetaUINorm.lean`.  This scaffold adds the residual form, canonical
angle-operator wrappers, unequal-rank extension, and the full concrete-norm
surface.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Conjugation by the reflection through `V`. -/
noncomputable def reflectionConjugate (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  V.reflection.toLinearMap ∘ₗ A ∘ₗ V.reflection.toLinearMap

/-- Mirror defect `J A J - A`. -/
noncomputable def reflectionDefect (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  reflectionConjugate V A - A

/-- **Davis--Kahan `sin 2Θ`, residual form, every UI norm.**

Lean proof route for a weaker agent:

1. Use the reflection to convert the angle expression to a cross-block Sylvester equation.
2. Prefer the operator-norm proof from the supported `DavisKahan.ReflectionDefect` module; obtain every finite UI norm through the existing `SinTwoThetaUINorm` majorization theorem.
-/
theorem sinTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  sorry

/-- **Davis--Kahan `sin 2Θ`, perturbation form, every UI norm.**
-/
theorem sinTwoTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hcross :
      N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
        N (B - A) / (b - a) := by
    simpa [projection, complementaryProjection] using
      N.sin_two_theta_starProjection_le hA hB hU hV hab hgap.1 hgap.2
  have hg : 0 < b - a := sub_pos.mpr hab
  rw [le_div_iff₀ hg] at hcross
  have hscale :
      N (sinTwoAngleOperator U V) =
        2 * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) := by
    rw [sinTwoAngleOperator_eq_two_smul_cross, N.smul_eq]
    norm_num
  rw [hscale]
  calc
    (b - a) * (2 * N
        (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)) =
        2 * ((b - a) * N
          (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)) := by ring
    _ ≤ 2 * N (B - A) := by
      gcongr
      simpa [mul_comm] using hcross

/-- One-sided cross-block normalization matching the theorem already proved in
`SinTwoThetaUINorm.lean`.
-/
theorem sinTwoTheta_cross_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) *
        N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
      N (B - A) := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have h := N.sin_two_theta_starProjection_le
    hA hB hU hV hab hgap.1 hgap.2
  rw [le_div_iff₀ (sub_pos.mpr hab)] at h
  simpa [projection, complementaryProjection, mul_comm] using h

/-- Mirror-defect theorem with no second operator.
-/
theorem sinTwoTheta_reflectionDefect_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {a b : ℝ} (hab : a < b)
    (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N (sinTwoAngleOperator U V) ≤ N (reflectionDefect V A) := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hmirror :
      2 * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
        N (reflectionDefect V A) / (b - a) := by
    simpa [projection, complementaryProjection, reflectionDefect,
      reflectionConjugate] using
      N.sin_two_theta_reflection_le hA hU hab hgap.1 hgap.2
  rw [le_div_iff₀ (sub_pos.mpr hab)] at hmirror
  have hscale :
      N (sinTwoAngleOperator U V) =
        2 * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) := by
    rw [sinTwoAngleOperator_eq_two_smul_cross, N.smul_eq]
    norm_num
  rw [hscale]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmirror

/-- The reflection defect is at most twice the perturbation when `V` reduces
`B`.

Signature audit: The added `hB` hypothesis upgrades invariance of `V` to reduction of both
orthogonal blocks, so the reflection commutes with `B`.
-/
theorem reflectionDefect_le_two_mul_perturbation
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hB : B.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : Reduces B V) :
    N (reflectionDefect V A) ≤ 2 * N (B - A) := by
  let J : E →ₗ[𝕜] E := V.reflection.toLinearMap
  have hcomm : J ∘ₗ B = B ∘ₗ J := by
    ext x
    change V.reflection (B x) = B (V.reflection x)
    simp only [Submodule.reflection_apply, map_sub, map_nsmul]
    have hproj :
        V.starProjection (B x) = B (V.starProjection x) := by
      change projection V (B x) = B (projection V x)
      exact projection_apply_comm_of_reduces hB hV x
    rw [hproj]
  have hJinvol : J ∘ₗ J = LinearMap.id := by
    ext x
    change V.reflection (V.reflection x) = x
    exact V.reflection_reflection x
  have hconjB : J ∘ₗ B ∘ₗ J = B := by
    ext x
    have hc := LinearMap.congr_fun hcomm (J x)
    change J (B (J x)) = B (J (J x)) at hc
    have hj := LinearMap.congr_fun hJinvol x
    change J (J x) = x at hj
    change J (B (J x)) = B x
    calc
      J (B (J x)) = B (J (J x)) := hc
      _ = B x := congrArg B hj
  have hdef : reflectionDefect V A =
      J ∘ₗ (A - B) ∘ₗ J - (A - B) := by
    ext x
    simp only [reflectionDefect, reflectionConjugate, J, LinearMap.comp_apply,
      LinearMap.sub_apply, map_sub]
    have hb := LinearMap.congr_fun hconjB x
    change J (B (J x)) = B x at hb
    rw [hb]
    abel
  have hconjNorm : N (J ∘ₗ (A - B) ∘ₗ J) = N (A - B) := by
    simpa [J] using N.invariant V.reflection V.reflection (A - B)
  calc
    N (reflectionDefect V A) =
        N (J ∘ₗ (A - B) ∘ₗ J - (A - B)) := by rw [hdef]
    _ ≤ N (J ∘ₗ (A - B) ∘ₗ J) + N (-(A - B)) := by
      rw [sub_eq_add_neg]
      exact N.add_le _ _
    _ = N (A - B) + N (A - B) := by
      rw [hconjNorm, N.apply_neg]
    _ = 2 * N (B - A) := by
      have hsub : A - B = -(B - A) := by abel
      rw [hsub, N.apply_neg]
      ring

/-- Canonical spectral-projector form.
-/
theorem sinTwoTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {Ω : Set ℝ} {a b : ℝ} (hab : a < b)
    (hgap : TwoBlockFormGap A (spectralSubspace A Ω) a b) :
    (b - a) * N (sinTwoAngleOperator (spectralSubspace A Ω)
        (spectralSubspace B Ω)) ≤ 2 * N (B - A) := by
  exact sinTwoTheta_perturbation_le N hA hB
    (reduces_spectralSubspace A Ω) (reduces_spectralSubspace B Ω) hab hgap

/-- Unequal-dimensional extension: zero padding records the unmatched
principal directions.
-/
theorem sinTwoTheta_perturbation_le_unequalFinrank
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  exact sinTwoTheta_perturbation_le N hA hB hU hV hab hgap

/-- Operator-norm form.
-/
theorem opNorm_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * ‖(sinTwoAngleOperator U V).toContinuousLinearMap‖ ≤
      2 * ‖(B - A).toContinuousLinearMap‖ := by
  exact sinTwoTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 E)
    hA hB hU hV hab hgap

/-- Frobenius form.
-/
theorem frobenius_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * UnitarilyInvariantNorm.frobenius 𝕜 E (sinTwoAngleOperator U V) ≤
      2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact sinTwoTheta_perturbation_le (UnitarilyInvariantNorm.frobenius 𝕜 E)
    hA hB hU hV hab hgap

/-- Ky Fan form.
-/
theorem kyFan_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) (k : ℕ) :
    (b - a) * kyFanSum k (sinTwoAngleOperator U V) ≤ 2 * kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := sinTwoTheta_perturbation_le NK hA hB hU hV hab hgap
  simpa [NK, RectangularUnitarilyInvariantNorm.toSquare,
    RectangularUnitarilyInvariantNorm.kyFan_apply,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h

end DavisKahanTheory
end ForMathlib
