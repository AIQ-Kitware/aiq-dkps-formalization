/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineSpectrum
import DavisKahan.Experimental.InfiniteDimensional.Core.OperatorAngleComplex
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle

/-!
# The genuine-spectrum `sin 2Θ` theorem

The `sin 2Θ` scaffold in `DoubleAngle.lean` is stated over the blocked
operator-angle ladder and the point-spectrum separation predicates.  This
module proves the honest complex version by the reflection argument: with
`J` the reflection through `V`, the conjugate `J A J` is self-adjoint, is
reduced by the reflected subspace `J U` with the *same* genuine compression
spectra (unitary conjugation transport), so the symmetric two-sided
genuine-spectrum `sin Θ` theorem applies to the pair `(A, J A J)` and gives
`d * subspaceGap U (J U) ≤ ‖J A J - A‖ ≤ 2 ‖B - A‖`.  The subspace gap to
the reflected image is exactly the operator norm of `sin 2Θ(U, V)`.

Supporting API, upstream candidates:

* `ContinuousLinearEquiv.conjAlgEquiv`: conjugation by a continuous linear
  equivalence as an algebra equivalence of endomorphism algebras;
* `conjByIsometryEquiv` and its transport laws for self-adjointness,
  reducing subspaces, orthogonal projections, compressions, and spectra.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

/-- Conjugation by a continuous linear equivalence, as an algebra
equivalence of the endomorphism algebras. -/
noncomputable def _root_.ContinuousLinearEquiv.conjAlgEquiv
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (e : X ≃L[ℂ] Y) :
    (X →L[ℂ] X) ≃ₐ[ℂ] (Y →L[ℂ] Y) where
  toFun T := (e : X →L[ℂ] Y) ∘L T ∘L (e.symm : Y →L[ℂ] X)
  invFun S := (e.symm : Y →L[ℂ] X) ∘L S ∘L (e : X →L[ℂ] Y)
  left_inv T := by ext x; simp
  right_inv S := by ext x; simp
  map_mul' T₁ T₂ := by ext x; simp
  map_add' T₁ T₂ := by ext x; simp
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem _root_.ContinuousLinearEquiv.conjAlgEquiv_apply
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (e : X ≃L[ℂ] Y)
    (T : X →L[ℂ] X) (y : Y) :
    e.conjAlgEquiv T y = e (T (e.symm y)) := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

section IsometryConjugation

/-- Conjugation of a bounded operator by a linear isometry equivalence. -/
noncomputable def conjByIsometryEquiv (W : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) :
    E →L[ℂ] E :=
  W.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    W.symm.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace E] in
@[simp] theorem conjByIsometryEquiv_apply (W : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (x : E) : conjByIsometryEquiv W A x = W (A (W.symm x)) := rfl

/-- Conjugation preserves self-adjointness. -/
theorem isSelfAdjoint_conjByIsometryEquiv (W : E ≃ₗᵢ[ℂ] E)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (conjByIsometryEquiv W A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA ⊢
  intro x y
  calc ⟪(conjByIsometryEquiv W A) x, y⟫_ℂ
      = ⟪W (A (W.symm x)), W (W.symm y)⟫_ℂ := by
        rw [W.apply_symm_apply]
        rfl
    _ = ⟪A (W.symm x), W.symm y⟫_ℂ := W.inner_map_map _ _
    _ = ⟪W.symm x, A (W.symm y)⟫_ℂ := hA _ _
    _ = ⟪W (W.symm x), W (A (W.symm y))⟫_ℂ := (W.inner_map_map _ _).symm
    _ = ⟪x, (conjByIsometryEquiv W A) y⟫_ℂ := by
        rw [W.apply_symm_apply]
        rfl

omit [CompleteSpace E] in
/-- Conjugation transports reducing subspaces to the image subspace. -/
theorem Reduces.map_isometryEquiv {A : E →L[ℂ] E} {U : Submodule ℂ E}
    (hU : Reduces A U) (W : E ≃ₗᵢ[ℂ] E) :
    Reduces (conjByIsometryEquiv W A)
      (U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) := by
  constructor
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨A y, hU.1 y hy, ?_⟩
    have h : conjByIsometryEquiv W A (W y) = W (A y) := by
      show W (A (W.symm (W y))) = W (A y)
      rw [W.symm_apply_apply]
    exact h.symm
  · intro x hx
    rw [← Submodule.map_orthogonal_equiv] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← Submodule.map_orthogonal_equiv]
    refine ⟨A y, hU.2 y hy, ?_⟩
    have h : conjByIsometryEquiv W A (W y) = W (A y) := by
      show W (A (W.symm (W y))) = W (A y)
      rw [W.symm_apply_apply]
    exact h.symm

/-- The isometric restriction of `W` from a subspace onto its image. -/
noncomputable def submoduleMapIsometry (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) :
    U ≃ₗᵢ[ℂ] (U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) where
  toLinearEquiv := W.toLinearEquiv.submoduleMap U
  norm_map' x := by
    have h1 : ((W.toLinearEquiv.submoduleMap U x :
        U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) = W (x : E) := rfl
    rw [show ‖W.toLinearEquiv.submoduleMap U x‖ =
        ‖((W.toLinearEquiv.submoduleMap U x :
          U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E)‖ from rfl, h1,
      W.norm_map]
    rfl

omit [CompleteSpace E] in
@[simp] theorem submoduleMapIsometry_coe_apply (W : E ≃ₗᵢ[ℂ] E)
    (U : Submodule ℂ E) (x : U) :
    ((submoduleMapIsometry W U x : U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) :
      E) = W (x : E) := rfl

omit [CompleteSpace E] in
@[simp] theorem submoduleMapIsometry_symm_coe_apply (W : E ≃ₗᵢ[ℂ] E)
    (U : Submodule ℂ E) (x : U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) :
    (((submoduleMapIsometry W U).symm x : U) : E) = W.symm (x : E) := rfl

omit [CompleteSpace E] in
/-- Conjugation transports compressions along the restricted isometry. -/
theorem compressOperator_map (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (A : E →L[ℂ] E) (W : E ≃ₗᵢ[ℂ] E) :
    compressOperator (U.map (W.toLinearEquiv : E →ₗ[ℂ] E))
        (conjByIsometryEquiv W A) =
      (submoduleMapIsometry W U).toContinuousLinearEquiv.conjAlgEquiv
        (compressOperator U A) := by
  ext x
  have hL : ((compressOperator (U.map (W.toLinearEquiv : E →ₗ[ℂ] E))
      (conjByIsometryEquiv W A) x :
        U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) =
      (U.map (W.toLinearEquiv : E →ₗ[ℂ] E)).starProjection
        ((conjByIsometryEquiv W A) (x : E)) := rfl
  have hR : (((submoduleMapIsometry W U).toContinuousLinearEquiv.conjAlgEquiv
      (compressOperator U A) x :
        U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) =
      W (U.starProjection (A (W.symm (x : E)))) := rfl
  rw [hL, hR, Submodule.starProjection_map_apply]
  have hc : W.symm ((conjByIsometryEquiv W A) (x : E)) =
      A (W.symm (x : E)) := by
    show W.symm (W (A (W.symm (x : E)))) = A (W.symm (x : E))
    rw [W.symm_apply_apply]
  rw [hc]

end IsometryConjugation

section SpectrumTransport

omit [CompleteSpace E] in
/-- Spectra of compressions are invariant under equality of the subspace. -/
theorem spectrum_compressOperator_congr {S T : Submodule ℂ E}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (h : S = T)
    (A : E →L[ℂ] E) :
    spectrum ℝ (compressOperator S A) = spectrum ℝ (compressOperator T A) := by
  subst h
  rfl

/-- **Spectrum transport for conjugated compressions.**  The real spectrum
of the compression of the conjugate to the image subspace equals the real
spectrum of the original compression. -/
theorem spectrum_compressOperator_map (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (W : E ≃ₗᵢ[ℂ] E) :
    spectrum ℝ (compressOperator (U.map (W.toLinearEquiv : E →ₗ[ℂ] E))
        (conjByIsometryEquiv W A)) =
      spectrum ℝ (compressOperator U A) := by
  rw [compressOperator_map]
  exact AlgEquiv.spectrum_eq
    (((submoduleMapIsometry W U).toContinuousLinearEquiv.conjAlgEquiv).restrictScalars
      ℝ) _

end SpectrumTransport

section SinTwoTheta

variable {𝕜 : Type*}

omit [CompleteSpace E] in
/-- The repo reflection operator agrees with Mathlib's reflection isometry. -/
theorem reflectionOperator_eq_reflection (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] (x : E) :
    (reflectionOperator V : E →L[ℂ] E) x = V.reflection x := by
  rw [reflectionOperator_apply, Submodule.reflection_apply, two_smul,
    two_smul]

omit [CompleteSpace E] in
/-- Conjugation by the reflection through `V` differs from the identity by
the reflection defect. -/
theorem conjByReflection_sub_eq_reflectionDefect (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] (A : E →L[ℂ] E) :
    conjByIsometryEquiv V.reflection A - A = reflectionDefect V A := by
  unfold reflectionDefect
  ext x
  show V.reflection (A (V.reflection.symm x)) - A x =
    reflectionOperator V (A (reflectionOperator V x)) - A x
  rw [reflectionOperator_eq_reflection, reflectionOperator_eq_reflection,
    Submodule.reflection_symm]

/-- **The genuine-spectrum `sin 2Θ` theorem** (reflection form).  For a
self-adjoint `A` with a genuine internal spectral configuration at the
reducing subspace `U` — compression to `U` in `[a, b]`, compression to
`Uᗮ` outside `(a - d, b + d)` — and any `B` reduced by `V`,
`d * subspaceGap U (J_V U) ≤ 2 ‖B - A‖`, where `J_V U` is the image of `U`
under the reflection through `V`.  The gap to the reflected image is the
operator norm of `sin 2Θ(U, V)`. -/
theorem sinTwoTheta_genuineSpectrum
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    d * subspaceGap U
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) ≤
      2 * ‖B - A‖ := by
  have hÃsa : IsSelfAdjoint (conjByIsometryEquiv V.reflection A) :=
    isSelfAdjoint_conjByIsometryEquiv V.reflection hA
  have hŨred : Reduces (conjByIsometryEquiv V.reflection A)
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) :=
    hU.map_isometryEquiv V.reflection
  have htrans1 : spectrum ℝ (compressOperator
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
      (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator U A) :=
    spectrum_compressOperator_map U A V.reflection
  have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E) =
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ :=
    Submodule.map_orthogonal_equiv U V.reflection
  have htrans2 : spectrum ℝ (compressOperator
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ
      (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator Uᗮ A) :=
    (spectrum_compressOperator_congr hperp.symm _).trans
      (spectrum_compressOperator_map Uᗮ A V.reflection)
  have h := sinTheta_genuineSpectrum_symmetric hA hÃsa hU hŨred hd hab hab
    hUspec
    (by rw [htrans2]; exact hUspec')
    (by rw [htrans1]; exact hUspec)
    hUspec'
  have hdefect : conjByIsometryEquiv V.reflection A - A =
      reflectionDefect V A :=
    conjByReflection_sub_eq_reflectionDefect V A
  calc d * subspaceGap U
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
      ≤ ‖conjByIsometryEquiv V.reflection A - A‖ := h
    _ = ‖reflectionDefect V A‖ := by rw [hdefect]
    _ ≤ 2 * ‖A - B‖ := norm_reflectionDefect_le_two_mul A B V hV
    _ = 2 * ‖B - A‖ := by rw [norm_sub_rev]

/-- The `sin 2Θ` theorem phrased through the complex sine-angle operator:
`d * ‖sin Θ(U, J_V U)‖ ≤ 2 ‖B - A‖`, and `Θ(U, J_V U) = 2 Θ(U, V)` is the
double-angle content of the reflected pair. -/
theorem sinTwoTheta_genuineSpectrum_sinAngle
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    d * ‖sinAngleOperatorC U
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))‖ ≤
      2 * ‖B - A‖ := by
  rw [norm_sinAngleOperatorC]
  exact sinTwoTheta_genuineSpectrum hA hU hV hd hab hUspec hUspec'

end SinTwoTheta

end DavisKahanExt
end ForMathlib
