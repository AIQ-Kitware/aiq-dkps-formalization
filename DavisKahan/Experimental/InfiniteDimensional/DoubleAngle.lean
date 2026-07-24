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

/-- The reflection is an involution, applied pointwise. -/
theorem reflectionOperator_apply_apply
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] (x : E) :
    reflectionOperator V (reflectionOperator V x) = x := by
  have h := congrArg (fun T : E →L[𝕜] E => T x) (reflectionOperator_involutive V)
  simpa using h

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

/-- The reflection through `V` exchanges orthogonal complements with mirror
images: it is a self-adjoint involution. -/
theorem reflectedSubspace_orthogonal
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    (reflectedSubspace V U)ᗮ = reflectedSubspace V Uᗮ := by
  have hJsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_reflectionOperator V)
  ext y
  constructor
  · intro hy
    refine Submodule.mem_map.mpr
      ⟨reflectionOperator V y, ?_, reflectionOperator_apply_apply V y⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := (Submodule.mem_orthogonal _ y).mp hy (reflectionOperator V u)
      (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)
    have h2 : ⟪reflectionOperator V u, y⟫_𝕜 =
        ⟪u, reflectionOperator V y⟫_𝕜 := hJsym u y
    rw [← h2]
    exact h
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨u, hu, rfl⟩
    calc ⟪reflectionOperator V u, reflectionOperator V w⟫_𝕜
        = ⟪u, reflectionOperator V (reflectionOperator V w)⟫_𝕜 :=
          hJsym u (reflectionOperator V w)
      _ = ⟪u, w⟫_𝕜 := by rw [reflectionOperator_apply_apply V w]
      _ = 0 := Submodule.inner_right_of_mem_orthogonal hu hw

/-- The mirror image of a subspace with an orthogonal projection has one:
the conjugated projection is an idempotent with the reflected range. -/
noncomputable instance reflectedSubspace_hasOrthogonalProjection
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    [U.HasOrthogonalProjection] :
    (reflectedSubspace V U).HasOrthogonalProjection := by
  set P : E →L[𝕜] E :=
    reflectionOperator V ∘L projection U ∘L reflectionOperator V with hP
  have hPapp : ∀ x, P x = reflectionOperator V
      (U.starProjection (reflectionOperator V x)) := fun x => rfl
  have hidem : IsIdempotentElem P := by
    show P * P = P
    ext x
    show P (P x) = P x
    rw [hPapp, hPapp, reflectionOperator_apply_apply,
      Submodule.starProjection_eq_self_iff.mpr
        (U.starProjection_apply_mem (reflectionOperator V x))]
  have hrange : LinearMap.range (P : E →ₗ[𝕜] E) = reflectedSubspace V U := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact Submodule.mem_map.mpr
        ⟨U.starProjection (reflectionOperator V x),
          U.starProjection_apply_mem _, rfl⟩
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      refine ⟨reflectionOperator V u, ?_⟩
      show P (reflectionOperator V u) =
        (reflectionOperator V : E →L[𝕜] E) u
      rw [hPapp, reflectionOperator_apply_apply,
        Submodule.starProjection_eq_self_iff.mpr hu]
  exact hrange ▸
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range hidem

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

/-- The mirror image of a reducing subspace reduces the conjugated
operator. -/
theorem reduces_reflectedSubspace
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) :
    Reduces (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U) := by
  constructor
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
    show reflectionOperator V (A (reflectionOperator V
      (reflectionOperator V u))) ∈ reflectedSubspace V U
    rw [reflectionOperator_apply_apply]
    exact Submodule.mem_map.mpr ⟨A u, hU.1 u hu, rfl⟩
  · intro y hy
    rw [reflectedSubspace_orthogonal] at hy ⊢
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    show reflectionOperator V (A (reflectionOperator V
      (reflectionOperator V w))) ∈ reflectedSubspace V Uᗮ
    rw [reflectionOperator_apply_apply]
    exact Submodule.mem_map.mpr ⟨A w, hU.2 w hw, rfl⟩

/-- Double reflection conjugation is the identity on operators. -/
theorem reflection_conjugate_conjugate (A : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] :
    reflectionOperator V ∘L (reflectionOperator V ∘L A ∘L reflectionOperator V)
      ∘L reflectionOperator V = A := by
  ext x
  show reflectionOperator V (reflectionOperator V (A (reflectionOperator V
    (reflectionOperator V x)))) = A x
  rw [reflectionOperator_apply_apply, reflectionOperator_apply_apply]

/-- Double reflection is the identity on subspaces. -/
theorem reflectedSubspace_reflectedSubspace (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] :
    reflectedSubspace V (reflectedSubspace V U) = U := by
  have hcomp : ((reflectionOperator V : E →L[𝕜] E) :
      E →ₗ[𝕜] E).comp ((reflectionOperator V : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      LinearMap.id := by
    ext x
    exact reflectionOperator_apply_apply V x
  unfold reflectedSubspace
  rw [← Submodule.map_comp, hcomp, Submodule.map_id]

/-- Conjugation by the reflection carries invariance to the mirror image. -/
theorem invariantFor_reflection_conjugate
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hU : InvariantFor A U) :
    InvariantFor (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U) := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
  show reflectionOperator V (A (reflectionOperator V
    (reflectionOperator V u))) ∈ reflectedSubspace V U
  rw [reflectionOperator_apply_apply]
  exact Submodule.mem_map.mpr ⟨A u, hU u hu, rfl⟩

/-- Invariance of the mirror image forces invariance of the original. -/
theorem invariantFor_of_reflection_conjugate
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection]
    (hU' : InvariantFor (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U)) :
    InvariantFor A U := by
  have h := invariantFor_reflection_conjugate V hU'
  rwa [reflection_conjugate_conjugate, reflectedSubspace_reflectedSubspace] at h

/-- Two-sided intertwiners transport invertibility. -/
private theorem isUnit_conj_of_isUnit {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (Φ : G →L[𝕜] H) (Ψ : H →L[𝕜] G)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    {T : G →L[𝕜] G} (hT : IsUnit T) :
    IsUnit (Φ ∘L T ∘L Ψ) := by
  obtain ⟨w, rfl⟩ := hT
  refine ⟨⟨Φ ∘L (w : G →L[𝕜] G) ∘L Ψ, Φ ∘L ((↑w⁻¹ : G →L[𝕜] G)) ∘L Ψ, ?_, ?_⟩, rfl⟩
  · ext y
    have h1 : (w : G →L[𝕜] G) ((↑w⁻¹ : G →L[𝕜] G) (Ψ y)) = Ψ y :=
      congrArg (fun S : G →L[𝕜] G => S (Ψ y)) w.mul_inv
    show (Φ : G → H) ((w : G →L[𝕜] G) (Ψ (Φ ((↑w⁻¹ : G →L[𝕜] G) (Ψ y))))) = y
    rw [hΨΦ, h1, hΦΨ]
  · ext y
    have h1 : (↑w⁻¹ : G →L[𝕜] G) ((w : G →L[𝕜] G) (Ψ y)) = Ψ y :=
      congrArg (fun S : G →L[𝕜] G => S (Ψ y)) w.inv_mul
    show (Φ : G → H) ((↑w⁻¹ : G →L[𝕜] G) (Ψ (Φ ((w : G →L[𝕜] G) (Ψ y))))) = y
    rw [hΨΦ, h1, hΦΨ]

/-- Conjugation by a two-sided intertwiner pair preserves invertibility. -/
private theorem isUnit_conj_iff {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (Φ : G →L[𝕜] H) (Ψ : H →L[𝕜] G)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (T : G →L[𝕜] G) :
    IsUnit (Φ ∘L T ∘L Ψ) ↔ IsUnit T := by
  constructor
  · intro h
    have h2 := isUnit_conj_of_isUnit Ψ Φ hΦΨ hΨΦ h
    have he : Ψ ∘L (Φ ∘L T ∘L Ψ) ∘L Φ = T := by
      ext x
      show (Ψ : H → G) (Φ (T (Ψ (Φ x)))) = T x
      rw [hΨΦ, hΨΦ]
    rwa [he] at h2
  · exact isUnit_conj_of_isUnit Φ Ψ hΨΦ hΦΨ

/-- Restricting the conjugated operator to the mirror image gives the same
spectrum as restricting the original operator to the original subspace. -/
private theorem spectrum_restrict_reflection_conjugate
    (A : E →L[𝕜] E) (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (hU : InvariantFor A U)
    (hU' : InvariantFor (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U)) :
    spectrum 𝕜 ((reflectionOperator V ∘L A ∘L reflectionOperator V).restrict hU')
      = spectrum 𝕜 (A.restrict hU) := by
  have hΦmem : ∀ x : ↥U,
      ((reflectionOperator V : E →L[𝕜] E) ∘L U.subtypeL) x ∈
        reflectedSubspace V U := fun x =>
    Submodule.mem_map.mpr ⟨(x : E), x.2, rfl⟩
  have hΨmem : ∀ y : ↥(reflectedSubspace V U),
      ((reflectionOperator V : E →L[𝕜] E) ∘L
        (reflectedSubspace V U).subtypeL) y ∈ U := by
    intro y
    obtain ⟨u, hu, huy⟩ := Submodule.mem_map.mp y.2
    have hval : ((reflectionOperator V : E →L[𝕜] E) ∘L
        (reflectedSubspace V U).subtypeL) y = u := by
      show reflectionOperator V (y : E) = u
      rw [← huy]
      exact reflectionOperator_apply_apply V u
    rw [hval]
    exact hu
  set Φ : ↥U →L[𝕜] ↥(reflectedSubspace V U) :=
    ((reflectionOperator V : E →L[𝕜] E) ∘L U.subtypeL).codRestrict
      (reflectedSubspace V U) hΦmem with hΦdef
  set Ψ : ↥(reflectedSubspace V U) →L[𝕜] ↥U :=
    ((reflectionOperator V : E →L[𝕜] E) ∘L
      (reflectedSubspace V U).subtypeL).codRestrict U hΨmem with hΨdef
  have hcoeΦ : ∀ x : ↥U, (Φ x : E) = reflectionOperator V (x : E) := fun _ => rfl
  have hcoeΨ : ∀ y : ↥(reflectedSubspace V U),
      (Ψ y : E) = reflectionOperator V (y : E) := fun _ => rfl
  have hΨΦ : ∀ x : ↥U, Ψ (Φ x) = x := by
    intro x
    apply Subtype.ext
    rw [hcoeΨ, hcoeΦ]
    exact reflectionOperator_apply_apply V (x : E)
  have hΦΨ : ∀ y : ↥(reflectedSubspace V U), Φ (Ψ y) = y := by
    intro y
    apply Subtype.ext
    rw [hcoeΦ, hcoeΨ]
    exact reflectionOperator_apply_apply V (y : E)
  ext z
  rw [spectrum.mem_iff, spectrum.mem_iff, not_iff_not]
  have hz : algebraMap 𝕜
        (↥(reflectedSubspace V U) →L[𝕜] ↥(reflectedSubspace V U)) z -
        (reflectionOperator V ∘L A ∘L reflectionOperator V).restrict hU' =
      Φ ∘L (algebraMap 𝕜 (↥U →L[𝕜] ↥U) z - A.restrict hU) ∘L Ψ := by
    ext y
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      Submodule.coe_sub, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self,
      Submodule.coe_smul, ContinuousLinearMap.coe_restrict_apply,
      hcoeΦ, hcoeΨ, map_sub, map_smul, reflectionOperator_apply_apply]
  rw [hz]
  exact isUnit_conj_iff Φ Ψ hΨΦ hΦΨ _

/-- **Restricted-spectrum invariance under reflection conjugation.**  The
mirror image of an invariant subspace carries the same restricted spectrum
for the conjugated operator. -/
theorem restrictedSpectrum_reflection_conjugate
    (A : E →L[𝕜] E) (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    DavisKahan.Experimental.Foundation.restrictedSpectrum
        (reflectionOperator V ∘L A ∘L reflectionOperator V)
        (reflectedSubspace V U) =
      DavisKahan.Experimental.Foundation.restrictedSpectrum A U := by
  ext r
  constructor
  · rintro ⟨hU', hr⟩
    have hU : InvariantFor A U := invariantFor_of_reflection_conjugate V hU'
    exact ⟨hU, by
      rwa [spectrum_restrict_reflection_conjugate A U V hU hU'] at hr⟩
  · rintro ⟨hU, hr⟩
    have hU' := invariantFor_reflection_conjugate (A := A) V hU
    exact ⟨hU', by
      rwa [spectrum_restrict_reflection_conjugate A U V hU hU']⟩

/-- A finite-gap configuration yields both mixed interval/exterior
separations against its own reflection through `V`, with ordered interval
endpoints: conjugation by the reflection preserves every restricted
spectrum. -/
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
        (reflectedSubspace V U) A Uᗮ l' r' d := by
  obtain ⟨l, r, hlr, hUin, hUcout⟩ := hfinite
  refine ⟨l, r, l, r, hlr, hlr, ⟨hUin, ?_, ?_⟩, ⟨?_, ?_⟩, hUcout⟩
  · rw [reflectedSubspace_orthogonal]
    exact invariantFor_reflection_conjugate V hUcout.1
  · rw [reflectedSubspace_orthogonal, restrictedSpectrum_reflection_conjugate]
    exact hUcout.2
  · exact invariantFor_reflection_conjugate V hUin.1
  · rw [restrictedSpectrum_reflection_conjugate]
    exact hUin.2

/-- The internal gap transports to the hybrid gap against the reflected
configuration: both restricted spectra are invariant under reflection
conjugation. -/
theorem internalGap_reflection_transport
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {d : ℝ}
    (hgap : InternalGap A U d) :
    HybridGap A (reflectionOperator V ∘L A ∘L reflectionOperator V)
      U (reflectedSubspace V U) d := by
  obtain ⟨hInvU, hInvUc, hsep⟩ := hgap
  refine ⟨hInvU, ?_, ?_⟩
  · rw [reflectedSubspace_orthogonal]
    exact invariantFor_reflection_conjugate V hInvUc
  · intro a ha b hb
    rw [reflectedSubspace_orthogonal,
      restrictedSpectrum_reflection_conjugate] at hb
    exact hsep a ha b hb

/-- The projection onto the mirror image is the conjugated projection. -/
theorem starProjection_reflectedSubspace
    (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] [U.HasOrthogonalProjection] :
    (reflectedSubspace V U).starProjection =
      reflectionOperator V ∘L U.starProjection ∘L reflectionOperator V := by
  ext x
  show (reflectedSubspace V U).starProjection x =
    reflectionOperator V (U.starProjection (reflectionOperator V x))
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact Submodule.mem_map.mpr
      ⟨U.starProjection (reflectionOperator V x),
        U.starProjection_apply_mem _, rfl⟩
  · rw [reflectedSubspace_orthogonal]
    refine Submodule.mem_map.mpr
      ⟨reflectionOperator V x - U.starProjection (reflectionOperator V x),
        Submodule.sub_starProjection_mem_orthogonal _, ?_⟩
    show reflectionOperator V (reflectionOperator V x -
      U.starProjection (reflectionOperator V x)) =
      x - reflectionOperator V (U.starProjection (reflectionOperator V x))
    rw [map_sub, reflectionOperator_apply_apply]

/-- The projection onto the mirror image's complement is the conjugated
complementary projection. -/
theorem starProjection_orthogonal_reflectedSubspace
    (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] [U.HasOrthogonalProjection] :
    ((reflectedSubspace V U)ᗮ).starProjection =
      reflectionOperator V ∘L Uᗮ.starProjection ∘L reflectionOperator V := by
  rw [Submodule.starProjection_orthogonal' (reflectedSubspace V U),
    starProjection_reflectedSubspace, Submodule.starProjection_orthogonal' U]
  ext x
  show x - reflectionOperator V (U.starProjection (reflectionOperator V x)) =
    reflectionOperator V (reflectionOperator V x -
      U.starProjection (reflectionOperator V x))
  rw [map_sub, reflectionOperator_apply_apply]

/-- **Cross-block identity.**  The complementary block of the reflection
between the two projections is exactly the one-sided double-angle
operator. -/
theorem complementary_comp_reflection_comp_projection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Uᗮ.starProjection ∘L reflectionOperator V ∘L U.starProjection =
      sinTwoAngleOperator U V := by
  ext x
  show Uᗮ.starProjection (reflectionOperator V (U.starProjection x)) =
    (2 : 𝕜) • Uᗮ.starProjection (V.starProjection (U.starProjection x))
  rw [Submodule.reflectionOperator_apply, map_sub, map_smul]
  have h0 : Uᗮ.starProjection (U.starProjection x) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply U (U.starProjection x),
      show U.starProjection (U.starProjection x) = U.starProjection x from
        Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x),
      sub_self]
  rw [h0, sub_zero]

/-- Left composition with the reflection preserves the operator norm. -/
theorem norm_reflection_comp (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : ‖reflectionOperator V ∘L T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
    show ‖reflectionOperator V (T x)‖ ≤ ‖T‖ * ‖x‖
    rw [V.reflectionOperator_norm_map]
    exact T.le_opNorm x
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖T x‖ = ‖reflectionOperator V (T x)‖ :=
        (V.reflectionOperator_norm_map (T x)).symm
      _ = ‖(reflectionOperator V ∘L T) x‖ := rfl
      _ ≤ ‖reflectionOperator V ∘L T‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ x

/-- Right composition with the reflection preserves the operator norm. -/
theorem norm_comp_reflection (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : ‖T ∘L reflectionOperator V‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
    show ‖T (reflectionOperator V x)‖ ≤ ‖T‖ * ‖x‖
    calc ‖T (reflectionOperator V x)‖ ≤ ‖T‖ * ‖reflectionOperator V x‖ :=
        T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [V.reflectionOperator_norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖T x‖
        = ‖T (reflectionOperator V (reflectionOperator V x))‖ := by
          rw [reflectionOperator_apply_apply]
      _ = ‖(T ∘L reflectionOperator V) (reflectionOperator V x)‖ := rfl
      _ ≤ ‖T ∘L reflectionOperator V‖ * ‖reflectionOperator V x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖T ∘L reflectionOperator V‖ * ‖x‖ := by
          rw [V.reflectionOperator_norm_map]

/-- The two-projection double-angle identity: the gap to the mirror image is
the norm of the one-sided double-angle operator.  Both directed blocks of the
projector difference are the double-angle operator up to composition with the
reflection, which is unitary. -/
theorem sinAngle_reflected_eq_sinTwoAngle
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    subspaceGap U (reflectedSubspace V U) = ‖sinTwoAngleOperator U V‖ := by
  have hgap : subspaceGap U (reflectedSubspace V U) =
      ‖(U.starProjection -
        (reflectedSubspace V U).starProjection : E →L[𝕜] E)‖ := rfl
  rw [hgap, Submodule.norm_starProjection_sub_eq_max]
  have h1 : (1 - (reflectedSubspace V U).starProjection : E →L[𝕜] E) ∘L
      U.starProjection =
      reflectionOperator V ∘L
        (Uᗮ.starProjection ∘L reflectionOperator V ∘L U.starProjection) := by
    rw [← Submodule.starProjection_orthogonal' (reflectedSubspace V U),
      starProjection_orthogonal_reflectedSubspace]
    ext x
    rfl
  have h2 : (1 - U.starProjection : E →L[𝕜] E) ∘L
      (reflectedSubspace V U).starProjection =
      (Uᗮ.starProjection ∘L reflectionOperator V ∘L U.starProjection) ∘L
        reflectionOperator V := by
    rw [← Submodule.starProjection_orthogonal' U,
      starProjection_reflectedSubspace]
    ext x
    rfl
  rw [h1, h2, complementary_comp_reflection_comp_projection,
    norm_reflection_comp, norm_comp_reflection, max_self]

/-- The directed form of the double-angle identity. -/
theorem doubleAngle_directedGap_identity
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperator U V‖ = directedGap U (reflectedSubspace V U) := by
  have hgap : directedGap U (reflectedSubspace V U) =
      ‖((reflectedSubspace V U)ᗮ).starProjection ∘L U.starProjection‖ := rfl
  rw [hgap, starProjection_orthogonal_reflectedSubspace]
  have hassoc : (reflectionOperator V ∘L Uᗮ.starProjection ∘L
      reflectionOperator V) ∘L U.starProjection =
      reflectionOperator V ∘L
        (Uᗮ.starProjection ∘L reflectionOperator V ∘L U.starProjection) := by
    ext x
    rfl
  rw [hassoc, complementary_comp_reflection_comp_projection,
    norm_reflection_comp]

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

omit [CompleteSpace E] in
/-- The reflection defect is `-2` times the sum of the two off-diagonal
blocks: `J A J - A = -2 (P_{Vᗮ} A P_V + P_V A P_{Vᗮ})`. -/
theorem reflectionDefect_eq_neg_two_smul_offdiag (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    reflectionDefect V A =
      (-2 : 𝕜) • (Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection) := by
  ext x
  show reflectionOperator V (A (reflectionOperator V x)) - A x =
    (-2 : 𝕜) • (Vᗮ.starProjection (A (V.starProjection x)) +
      V.starProjection (A (Vᗮ.starProjection x)))
  rw [reflectionOperator_apply, reflectionOperator_apply,
    Submodule.starProjection_orthogonal' V]
  simp only [map_sub, map_smul, sub_apply, one_apply_eq_self]
  module

/-- The two off-diagonal blocks are mutually adjoint for self-adjoint `A`. -/
theorem offdiag_adjoint (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint =
      V.starProjection ∘L A ∘L Vᗮ.starProjection := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq, hA.star_eq,
    ContinuousLinearMap.comp_assoc]

/-- **Sharp reflection-defect estimate through the off-diagonal block.**
For self-adjoint `A`, `‖J_V A J_V - A‖ ≤ 2 ‖P_{Vᗮ} A P_V‖` — no reduction
hypothesis on `V`.  This is the analytic input for the residual form of the
`sin 2Θ` theorem. -/
theorem norm_reflectionDefect_le_two_mul_norm_cross (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    ‖reflectionDefect V A‖ ≤
      2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ := by
  set T₁ : E →L[𝕜] E := Vᗮ.starProjection ∘L A ∘L V.starProjection
    with hT₁
  set T₂ : E →L[𝕜] E := V.starProjection ∘L A ∘L Vᗮ.starProjection
    with hT₂
  have hnormT₂ : ‖T₂‖ = ‖T₁‖ := by
    rw [hT₂, ← offdiag_adjoint V hA, ← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star T₁
  -- the sum of the off-diagonal blocks is bounded by the larger block
  have hsum : ‖T₁ + T₂‖ ≤ ‖T₁‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h1out : T₁ z ∈ Vᗮ := by
      rw [hT₁]
      exact Vᗮ.starProjection_apply_mem _
    have h2out : T₂ z ∈ V := by
      rw [hT₂]
      exact V.starProjection_apply_mem _
    have horth : ⟪T₂ z, T₁ z⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal V _).mp h1out _ h2out
    have hpyth : ‖(T₁ + T₂) z‖ ^ 2 = ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (T₂ z) (T₁ z) horth
      have hadd : (T₁ + T₂) z = T₂ z + T₁ z := by
        rw [add_apply]
        abel
      rw [hadd, sq, sq, sq]
      linarith
    have hin1 : ‖T₁ z‖ ≤ ‖T₁‖ * ‖V.starProjection z‖ := by
      have hfac : T₁ z = T₁ (V.starProjection z) := by
        rw [hT₁]
        show Vᗮ.starProjection (A (V.starProjection z)) =
          Vᗮ.starProjection (A (V.starProjection (V.starProjection z)))
        rw [show V.starProjection (V.starProjection z) =
          V.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (V.starProjection_apply_mem z)]
      rw [hfac]
      exact T₁.le_opNorm _
    have hin2 : ‖T₂ z‖ ≤ ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by
      have hfac : T₂ z = T₂ (Vᗮ.starProjection z) := by
        rw [hT₂]
        show V.starProjection (A (Vᗮ.starProjection z)) =
          V.starProjection (A (Vᗮ.starProjection (Vᗮ.starProjection z)))
        rw [show Vᗮ.starProjection (Vᗮ.starProjection z) =
          Vᗮ.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (Vᗮ.starProjection_apply_mem z)]
      rw [hfac]
      calc ‖T₂ (Vᗮ.starProjection z)‖
          ≤ ‖T₂‖ * ‖Vᗮ.starProjection z‖ := T₂.le_opNorm _
        _ = ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by rw [hnormT₂]
    have hzdecomp : ‖z‖ ^ 2 =
        ‖V.starProjection z‖ ^ 2 + ‖Vᗮ.starProjection z‖ ^ 2 := by
      have horth' : ⟪V.starProjection z, Vᗮ.starProjection z⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal V _).mp
          (Vᗮ.starProjection_apply_mem z) _ (V.starProjection_apply_mem z)
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (V.starProjection z) (Vᗮ.starProjection z) horth'
      rw [V.starProjection_add_starProjection_orthogonal z] at h
      rw [sq, sq, sq]
      linarith
    have hsq : ‖(T₁ + T₂) z‖ ^ 2 ≤ (‖T₁‖ * ‖z‖) ^ 2 := by
      rw [hpyth]
      have h1 := mul_self_le_mul_self (norm_nonneg (T₁ z)) hin1
      have h2 := mul_self_le_mul_self (norm_nonneg (T₂ z)) hin2
      have key : ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 ≤
          ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
            ‖Vᗮ.starProjection z‖ ^ 2) := by
        nlinarith [h1, h2]
      calc ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2
          ≤ ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
              ‖Vᗮ.starProjection z‖ ^ 2) := key
        _ = (‖T₁‖ * ‖z‖) ^ 2 := by rw [← hzdecomp]; ring
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg z))] at hs
  calc ‖reflectionDefect V A‖
      = ‖(-2 : 𝕜) • (T₁ + T₂)‖ := by
        rw [reflectionDefect_eq_neg_two_smul_offdiag]
    _ = 2 * ‖T₁ + T₂‖ := by
        rw [norm_smul]
        norm_num
    _ ≤ 2 * ‖T₁‖ := by linarith [hsum]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The off-diagonal block is bounded by the residual.**  If the trial
subspace `V` is the range of an isometric embedding `X` and
`R = A X - X M` is the residual of the approximate intertwining
relation `A X ≈ X M`, then `‖P_{Vᗮ} A P_V‖ ≤ ‖R‖`: on `v = X u ∈ V`,
`(1 - P_V) A v = (1 - P_V) (X (M u)) + (1 - P_V) (R u) = (1 - P_V) (R u)`,
and the isometry converts `‖u‖` back to `‖v‖`. -/
theorem norm_cross_le_norm_residual
    {X : F →L[𝕜] E} (hX : DavisKahan.IsometricEmbedding X)
    (A : E →L[𝕜] E) (M : F →L[𝕜] F)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hmem : ∀ u, X u ∈ V) (hsurj : ∀ v ∈ V, ∃ u, X u = v) :
    ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ ≤
      ‖A ∘L X - X ∘L M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  obtain ⟨u, hu⟩ := hsurj (V.starProjection z) (V.starProjection_apply_mem z)
  have hunorm : ‖u‖ = ‖V.starProjection z‖ := by rw [← hX u, hu]
  have hperp0 : Vᗮ.starProjection (X (M u)) = 0 := by
    rw [Submodule.starProjection_orthogonal' V]
    have hfix : V.starProjection (X (M u)) = X (M u) :=
      Submodule.starProjection_eq_self_iff.mpr (hmem (M u))
    rw [sub_apply, one_apply_eq_self, hfix, sub_self]
  have hsplit : A (X u) = X (M u) + (A ∘L X - X ∘L M) u := by
    show A (X u) = X (M u) + (A (X u) - X (M u))
    rw [add_sub_cancel]
  have hcalc : (Vᗮ.starProjection ∘L A ∘L V.starProjection) z =
      Vᗮ.starProjection ((A ∘L X - X ∘L M) u) := by
    show Vᗮ.starProjection (A (V.starProjection z)) = _
    rw [← hu, hsplit, map_add, hperp0, zero_add]
  rw [hcalc]
  calc ‖Vᗮ.starProjection ((A ∘L X - X ∘L M) u)‖
      ≤ ‖(A ∘L X - X ∘L M) u‖ :=
        Vᗮ.norm_starProjection_apply_le _
    _ ≤ ‖A ∘L X - X ∘L M‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖A ∘L X - X ∘L M‖ * ‖V.starProjection z‖ := by rw [hunorm]
    _ ≤ ‖A ∘L X - X ∘L M‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le z)
          (norm_nonneg _)

omit [CompleteSpace F] in
/-- **Leaf obligation.** The reflection defect through the closed trial range
is at most twice the residual: the defect is twice the off-diagonal block of
`A`, which the residual dominates. -/
theorem reflectionDefect_range_le_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection]
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M) :
    ‖reflectionDefect (LinearMap.range X.toLinearMap) A‖ ≤
      2 * ‖residual A X M‖ := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  set V := LinearMap.range X.toLinearMap with hV
  have hmem : ∀ u, X u ∈ V := fun u => ⟨u, rfl⟩
  have hsurj : ∀ v ∈ V, ∃ u, X u = v := fun v hv => hv
  have hcross := norm_cross_le_norm_residual hX A M hmem hsurj
  calc ‖reflectionDefect V A‖
      ≤ 2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ :=
        norm_reflectionDefect_le_two_mul_norm_cross V hAsa
    _ ≤ 2 * ‖residual A X M‖ := by
        have hres : residual A X M = A ∘L X - X ∘L M := rfl
        rw [hres]
        linarith

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
