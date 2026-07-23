/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.Compatibility
import DavisKahan.Experimental.InfiniteDimensional.Core.CompatibilitySinTwoTheta
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.General

/-!
# Infinite-dimensional `sin 2Θ` and generic double-angle bounds

Literature writeup: local TeX, Sections 14--15, including Seelmann's general
spectral-separation form.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

set_option maxHeartbeats 1000000

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Mirror defect used in the reflection proof of `sin 2Θ`. -/
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  reflectionOperator U ∘L A ∘L reflectionOperator U - A

omit [CompleteSpace E] in
/-- The mirror defect vanishes when the subspace reduces the operator.
-/
theorem reflectionDefect_eq_zero_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    reflectionDefect U A = 0 := by
  ext x
  have hcomm := congrArg (fun T : E →L[𝕜] E => T (reflectionOperator U x))
    (reflectionOperator_comm_of_reduces A U hU)
  have hinvol := congrArg (fun T : E →L[𝕜] E => T x)
    (reflectionOperator_involutive U)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcomm hinvol
  simp only [reflectionDefect, ContinuousLinearMap.comp_apply, sub_apply,
    zero_apply]
  rw [hcomm, hinvol, sub_self]

omit [CompleteSpace E] in
/-- Conjugating and subtracting a reducing comparison operator leaves only
its perturbation.
-/
theorem reflectionDefect_eq_perturbationDefect
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    reflectionDefect V A =
      reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B) := by
  have hB : reflectionDefect V B = 0 :=
    reflectionDefect_eq_zero_of_reduces B V hV
  unfold reflectionDefect at hB ⊢
  calc
    reflectionOperator V ∘L A ∘L reflectionOperator V - A =
        (reflectionOperator V ∘L A ∘L reflectionOperator V - A) -
          (reflectionOperator V ∘L B ∘L reflectionOperator V - B) := by
      rw [hB, sub_zero]
    _ = reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      abel

omit [CompleteSpace E] in
/-- The reflection defect is bounded by twice the perturbation norm.
-/
theorem norm_reflectionDefect_le_two_mul
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    ‖reflectionDefect V A‖ ≤ 2 * ‖A - B‖ := by
  rw [reflectionDefect_eq_perturbationDefect A B V hV]
  have hconj :
      ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V‖ ≤
        ‖A - B‖ := by
    calc
      ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V‖ ≤
          ‖reflectionOperator V‖ * ‖(A - B) ∘L reflectionOperator V‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖reflectionOperator V‖ * (‖A - B‖ * ‖reflectionOperator V‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg (reflectionOperator V))
      _ ≤ 1 * (‖A - B‖ * ‖reflectionOperator V‖) :=
        mul_le_mul_of_nonneg_right (norm_reflectionOperator_le_one V) (by positivity)
      _ ≤ 1 * (‖A - B‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_reflectionOperator_le_one V)
            (norm_nonneg (A - B)))
          zero_le_one
      _ = ‖A - B‖ := by ring
  calc
    ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B)‖ ≤
        ‖reflectionOperator V ∘L (A - B) ∘L reflectionOperator V‖ +
          ‖A - B‖ := norm_sub_le _ _
    _ ≤ ‖A - B‖ + ‖A - B‖ := add_le_add hconj le_rfl
    _ = 2 * ‖A - B‖ := by ring

/-! ## Reflected subspaces and the double-angle operator

The one-sided ambient double-angle operator, the mirror image of a subspace,
and the reflection-transport lemmas the `sin 2Θ` theorems consume.  The
transports whose proofs require restricted-spectrum invariance under unitary
conjugation or the two-projection double-angle calculus are isolated as leaf
obligations.
-/

/-- The ambient one-sided double-angle sine operator `2 P_{Uᗮ} P_V P_U`,
matching the finite-dimensional normalization. -/
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (2 : 𝕜) • (complementaryProjection U ∘L projection V ∘L projection U)

/-- The mirror image of a subspace under the reflection through another. -/
noncomputable def reflectedSubspace (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] : Submodule 𝕜 E :=
  U.map (reflectionOperator V : E →L[𝕜] E).toLinearMap

/-- **Leaf obligation.** The mirror image of a subspace with an orthogonal
projection has one: the conjugated projection is a self-adjoint idempotent
with the reflected range. -/
noncomputable instance reflectedSubspace_hasOrthogonalProjection
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    [U.HasOrthogonalProjection] :
    (reflectedSubspace V U).HasOrthogonalProjection :=
  sorry

/-- The reflection through a subspace is self-adjoint: it is `2 P - 1`. -/
theorem isSelfAdjoint_reflectionOperator
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    IsSelfAdjoint (reflectionOperator V : E →L[𝕜] E) := by
  have hP : IsSelfAdjoint (V.starProjection : E →L[𝕜] E) :=
    isSelfAdjoint_starProjection V
  have hform : (reflectionOperator V : E →L[𝕜] E) =
      (2 : 𝕜) • V.starProjection - 1 := by
    ext x
    simp [Submodule.reflectionOperator_apply]
  rw [hform, IsSelfAdjoint, star_sub, star_smul, star_ofNat, hP.star_eq,
    star_one]

/-- Conjugation by the reflection preserves self-adjointness. -/
theorem IsSelfAdjointOperator.reflection_conjugate
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    IsSelfAdjointOperator
      (reflectionOperator V ∘L A ∘L reflectionOperator V) := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hJsa : IsSelfAdjoint (reflectionOperator V : E →L[𝕜] E) :=
    isSelfAdjoint_reflectionOperator V
  have hstar : IsSelfAdjoint
      (reflectionOperator V ∘L A ∘L reflectionOperator V) := by
    show star (reflectionOperator V * A * reflectionOperator V) =
      reflectionOperator V * A * reflectionOperator V
    rw [star_mul, star_mul, hJsa.star_eq, hAsa.star_eq, mul_assoc]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hstar

/-- **Leaf obligation.** The mirror image of a reducing subspace reduces the
conjugated operator (needs `(J '' U)ᗮ = J '' Uᗮ` for the self-adjoint unitary
reflection). -/
theorem reduces_reflectedSubspace
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) :
    Reduces (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U) :=
  sorry

/-- **Leaf obligation.** A finite-gap configuration yields both mixed
interval/exterior separations against its own reflection through `V`, with
ordered interval endpoints: conjugation by the reflection preserves every
restricted spectrum. -/
theorem finiteGap_mixedIntervalExterior
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} (V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {d : ℝ}
    (hfinite : FiniteGapConfiguration A U d) :
    ∃ l r l' r', l ≤ r ∧ l' ≤ r' ∧
      IntervalExteriorSeparated A U
        (reflectionOperator V ∘L A ∘L reflectionOperator V)
        (reflectedSubspace V U)ᗮ l r d ∧
      IntervalExteriorSeparated
        (reflectionOperator V ∘L A ∘L reflectionOperator V)
        (reflectedSubspace V U) A Uᗮ l' r' d :=
  sorry

/-- **Leaf obligation.** The internal gap transports to the hybrid gap against
the reflected configuration. -/
theorem internalGap_reflection_transport
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {d : ℝ}
    (hgap : InternalGap A U d) :
    HybridGap A (reflectionOperator V ∘L A ∘L reflectionOperator V)
      U (reflectedSubspace V U) d :=
  sorry

/-- **Leaf obligation.** The two-projection double-angle identity: the gap to
the mirror image is the norm of the one-sided double-angle operator. -/
theorem sinAngle_reflected_eq_sinTwoAngle
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    subspaceGap U (reflectedSubspace V U) = ‖sinTwoAngleOperator U V‖ :=
  sorry

/-- **Leaf obligation.** The directed form of the double-angle identity. -/
theorem doubleAngle_directedGap_identity
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperator U V‖ = directedGap U (reflectedSubspace V U) :=
  sorry

/-- **Leaf obligation.** In every symmetric norm ideal, the full sine of the
angle to the mirror image carries the same membership and gauge as the
one-sided double-angle operator: their singular values agree. -/
theorem SymmetricNormIdeal.sinAngle_reflected_mem_gauge_eq
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E)) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (I.mem (sinAngleOperator U (reflectedSubspace V U)) ↔
      I.mem (sinTwoAngleOperator U V)) ∧
    I.gauge (sinAngleOperator U (reflectedSubspace V U)) =
      I.gauge (sinTwoAngleOperator U V) :=
  sorry

/-- **Leaf obligation.** The reflection defect through the closed trial range
is at most twice the residual: the defect is twice the off-diagonal block of
`A`, which the residual dominates. -/
theorem reflectionDefect_range_le_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection]
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M) :
    ‖reflectionDefect (LinearMap.range X.toLinearMap) A‖ ≤
      2 * ‖residual A X M‖ :=
  sorry

/-- The range of an isometric embedding of a complete space is closed, hence
admits an orthogonal projection. -/
theorem hasOrthogonalProjection_range_of_isometric
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X) :
    (LinearMap.range X.toLinearMap).HasOrthogonalProjection := by
  have hiso : Isometry X := AddMonoidHomClass.isometry_of_norm X hX
  have hclosed : IsClosed ((LinearMap.range X.toLinearMap : Submodule 𝕜 E) :
      Set E) := by
    have hr : ((LinearMap.range X.toLinearMap : Submodule 𝕜 E) : Set E) =
        Set.range X := by
      ext y
      simp [LinearMap.mem_range]
    rw [hr]
    exact hiso.isClosedEmbedding.isClosed_range
  haveI : CompleteSpace (LinearMap.range X.toLinearMap) :=
    hclosed.completeSpace_coe
  infer_instance

/-- Reflection-defect `sin 2Θ` theorem.

This is the theorem previously named `sinTwoTheta_residual`. The old name was
misleading: its right-hand side is a mirror defect, not the residual of an
approximate invariant pair.

Lean proof route for a weaker agent:

1. Let `J` be the reflection through `V` and compare `A` with `JAJ`.
2. The spectral subspace `JU` reduces `JAJ` and has the same internal gap.
3. Apply the symmetric `sinTheta` theorem to `A` and `JAJ`.
4. Use the two-projection identity relating the angle between `U` and `JU` to `sin(2Θ(U,V))`.


Ext-agent signature audit (GPT 5.6 High): `FiniteGapConfiguration` already supplies the
structured internal separation at positive `d`; the former separate `InternalGap`
hypothesis was redundant. The reflection-defect target is the correct sharp residual
form.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_reflectionDefect
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤
      ‖reflectionDefect V A‖ := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' := hA.reflection_conjugate V
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  obtain ⟨l, r, l', r', hlr, hlr', hUU', hU'U⟩ :=
    finiteGap_mixedIntervalExterior V hfinite
  have hsin := sinTheta_symmetric hA hA' hU hU' hlr hlr' hd hUU' hU'U
  have hgapid : subspaceGap U U' = ‖sinTwoAngleOperator U V‖ :=
    sinAngle_reflected_eq_sinTwoAngle U V
  calc d * ‖sinTwoAngleOperator U V‖
      = d * subspaceGap U U' := by rw [hgapid]
    _ ≤ ‖A' - A‖ := hsin
    _ = ‖reflectionDefect V A‖ := rfl

/-- Approximate-invariant-pair residual form of `sin 2Θ`.

This is the genuine residual theorem missing from the earlier scaffold.  The
proof should reflect through the closed range of `X`, identify its mirror
defect with twice the off-diagonal residual, and apply
`sinTwoTheta_reflectionDefect`.

Lean proof route for a weaker agent:

1. Prove that an isometric embedding has closed range and construct the
   orthogonal projection onto that range.
2. Show that self-adjointness of `M` makes `X ∘ M ∘ X⁻¹` reduce the trial
   range.
3. Express the reflection defect of `A` through the trial range in terms of
   `residual A X M` and its adjoint block.
4. Bound that defect by twice the residual norm and invoke the
   reflection-defect theorem.
-/
theorem sinTwoTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection]
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d) (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoThetaEmbedding U X‖ ≤ 2 * ‖residual A X M‖ := by
  let V := LinearMap.range X.toLinearMap
  have hangle : sinTwoThetaEmbedding U X = sinTwoAngleOperator U V :=
    sinTwoThetaEmbedding_eq_rangeAngle U X hX
  calc
    d * ‖sinTwoThetaEmbedding U X‖
        = d * ‖sinTwoAngleOperator U V‖ := by rw [hangle]
    _ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖residual A X M‖ :=
      reflectionDefect_range_le_residual hA X hX hM

/-- Perturbation form of the `sin 2Θ` theorem.

Ext-agent signature audit (GPT 5.6 High): Correct under finite-gap geometry. Reduction
of `B` by `V` is essential for cancellation of its reflection defect. Self-adjointness
of `B` is not needed for this reflection argument and was removed from the signature.
-/
theorem sinTwoTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ 2 * ‖B - A‖ := by
  calc
    d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖A - B‖ := norm_reflectionDefect_le_two_mul A B V hV
    _ = 2 * ‖B - A‖ := by rw [norm_sub_rev]

/-- General spectral-separation `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. Apply the general separated-spectrum Sylvester estimate to the reflection defect.
2. Identify the resulting cross block with `sin(2Θ)` through the two-projection calculus.
3. Bound the defect by `2‖B-A‖`; combine constants to obtain the factor `π`.
4. Keep the result at the operator level: `sin (2·maximalAngle)` is not the
   norm of `sinTwoAngleOperator` when the angle spectrum crosses `π/4`.


Ext-agent signature audit (GPT 5.6 High): The corrected operator-norm conclusion is the
meaningful generic theorem. `sin (2·maximalAngle)` alone can miss intermediate angle
spectrum when angles cross `π/4`.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ Real.pi * ‖B - A‖ := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' := hA.reflection_conjugate V
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  have hhybrid : HybridGap A A' U U' d :=
    internalGap_reflection_transport hgap
  have hsin := sinTheta_generalSeparation hA hA' hU hU' hd hhybrid
  have hdefect : ‖reflectionDefect V A‖ ≤ 2 * ‖B - A‖ := by
    rw [norm_sub_rev B A]
    exact norm_reflectionDefect_le_two_mul A B V hV
  calc
    d * ‖sinTwoAngleOperator U V‖
        = d * directedGap U U' := by
          rw [doubleAngle_directedGap_identity U V]
    _ ≤ (Real.pi/2) * ‖A'-A‖ := hsin
    _ = (Real.pi/2) * ‖reflectionDefect V A‖ := rfl
    _ ≤ (Real.pi/2) * (2 * ‖B-A‖) := by gcongr
    _ = Real.pi * ‖B-A‖ := by ring

/-- Ideal-norm `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. Use the reflection-defect form of `sinTwoTheta_reflectionDefect` in the ideal gauge.
2. Show the reflection defect equals the off-diagonal extraction of `B-A` up to the factor two because `V` reduces `B`.
3. Apply `gauge_offDiagonalPart_le` and `hmem`.
4. Package ideal membership before the numerical inequality.


Ext-agent signature audit (GPT 5.6 High): Correct roadmap target under finite-gap
geometry and ideal membership of the perturbation. The proof must work with ambient
reflection blocks so multiplicities match.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem ideal_sinTwoTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hmem : I.mem (B - A)) :
    I.mem (sinTwoAngleOperator U V) ∧
      d * I.gauge (sinTwoAngleOperator U V) ≤ 2 * I.gauge (B - A) := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' := hA.reflection_conjugate V
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  obtain ⟨l, r, l', r', hlr, hlr', hUU', hU'U⟩ :=
    finiteGap_mixedIntervalExterior V hfinite
  have hAB : I.mem (A - B) := by
    simpa [neg_sub] using I.smul_mem (-1 : 𝕜) hmem
  have hnegAB : I.mem (-(A - B)) := by
    simpa using I.smul_mem (-1 : 𝕜) hAB
  have hdefMem : I.mem (A'-A) := by
    rw [show A'-A = reflectionDefect V A by rfl,
      reflectionDefect_eq_perturbationDefect A B V hV]
    have h := I.add_mem
      (I.ideal_mem (reflectionOperator V) (reflectionOperator V) hAB) hnegAB
    simpa [sub_eq_add_neg] using h
  have hsin := ideal_sinTheta I hA hA' hU hU' hlr hlr' hd hUU' hU'U hdefMem
  have hdefGauge : I.gauge (A'-A) ≤ 2 * I.gauge (B-A) := by
    rw [show A'-A = reflectionDefect V A by rfl,
      reflectionDefect_eq_perturbationDefect A B V hV]
    have hconj : I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V) =
        I.gauge (A-B) :=
      I.unitary_invariant
        (reflectionOperator V) (reflectionOperator V) (A-B)
        (reflectionOperator_isUnitary V) (reflectionOperator_isUnitary V)
        (reflectionOperator_involutive V) (reflectionOperator_involutive V) hAB
    have htri := I.triangle
      (I.ideal_mem (reflectionOperator V) (reflectionOperator V) hAB) hnegAB
    have hgneg : I.gauge (-(A - B)) = I.gauge (A - B) := by
      simpa using I.gauge_smul (-1 : 𝕜) hAB
    have hgBA : I.gauge (A - B) = I.gauge (B - A) := by
      simpa [neg_sub] using I.gauge_smul (-1 : 𝕜) hmem
    calc I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V - (A-B))
        = I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V +
            -(A-B)) := by rw [sub_eq_add_neg]
      _ ≤ I.gauge (reflectionOperator V ∘L (A-B) ∘L reflectionOperator V) +
            I.gauge (-(A-B)) := htri
      _ = I.gauge (A-B) + I.gauge (A-B) := by rw [hconj, hgneg]
      _ = 2 * I.gauge (B-A) := by rw [hgBA]; ring
  obtain ⟨hmemiff, hgaugeeq⟩ := I.sinAngle_reflected_mem_gauge_eq U V
  exact ⟨hmemiff.mp hsin.1,
    by rw [← hgaugeeq]; exact hsin.2.trans hdefGauge⟩

end DavisKahanExt
end ForMathlib
