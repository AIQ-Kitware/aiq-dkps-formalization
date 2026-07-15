/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Reflection
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.OperatorAbsoluteValue
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Spectra-backed complex direct rotation

For two orthogonally complemented complex subspaces, this module introduces

`S = Q P + Qᗮ Pᗮ`.

The operator `S` is the pre-polar canonical intertwiner in the Davis--Kahan
direct-rotation construction.  The main result of this slice is that acuteness
makes `S` a unit.  The proof uses the exact factorization

`S - 1 = (Q - P) J_P`,

where `J_P` is the reflection through the first subspace.  Since the reflection
is contractive, the projection gap bounds `‖S - 1‖`; the acute hypothesis then
places `S` in the open unit ball around the identity, where the Neumann-series
inverse is available.

The Spectra polar factor is then shown to be unitary in the acute regime, to
intertwine the two orthogonal projections, and to carry the source subspace
onto the target subspace.  The construction remains a complex specialization
alongside the independent scalar-generic development.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The canonical pre-polar intertwiner `Q P + Qᗮ Pᗮ`. -/
noncomputable def spectraCanonicalIntertwiner
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  projection V * projection U +
    complementaryProjection V * complementaryProjection U

omit [CompleteSpace H] in
/-- The canonical intertwiner sends the `U` block into the `V` block. -/
theorem spectraCanonicalIntertwiner_mul_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V * projection U =
      projection V * spectraCanonicalIntertwiner U V := by
  change
    (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) * U.starProjection =
      V.starProjection *
        (V.starProjection * U.starProjection +
          Vᗮ.starProjection * Uᗮ.starProjection)
  rw [Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  have hQ : V.starProjection * V.starProjection = V.starProjection :=
    V.isIdempotentElem_starProjection
  noncomm_ring [hP, hQ]
  rw [← mul_assoc, hQ]
  module

/-- The adjoint of the canonical intertwiner is obtained by reversing the
ordered pair of subspaces. -/
theorem star_spectraCanonicalIntertwiner
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner V U := by
  change
    star (V.starProjection * U.starProjection +
      Vᗮ.starProjection * Uᗮ.starProjection) =
      U.starProjection * V.starProjection +
        Uᗮ.starProjection * Vᗮ.starProjection
  rw [star_add, star_mul, star_mul,
    (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Uᗮ).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq]

omit [CompleteSpace H] in
/-- Reflection through `U` written in the projection algebra. -/
theorem reflectionOperator_eq_projection_add_projection_sub_one
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    reflectionOperator U = projection U + projection U - 1 := by
  ext x
  rw [Submodule.reflectionOperator_apply]
  simp only [add_apply, sub_apply, one_apply_eq_self]
  module

omit [CompleteSpace H] in
/-- Exact factorization of the displacement of the canonical intertwiner from
the identity. -/
theorem spectraCanonicalIntertwiner_sub_one
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalIntertwiner U V - 1 =
      (projection V - projection U) * reflectionOperator U := by
  change
    (V.starProjection * U.starProjection +
        Vᗮ.starProjection * Uᗮ.starProjection) - 1 =
      (V.starProjection - U.starProjection) * U.reflectionOperator
  rw [Submodule.starProjection_orthogonal' U,
    Submodule.starProjection_orthogonal' V]
  rw [show U.reflectionOperator =
    U.starProjection + U.starProjection - 1 by
      exact reflectionOperator_eq_projection_add_projection_sub_one U]
  have hP : U.starProjection * U.starProjection = U.starProjection :=
    U.isIdempotentElem_starProjection
  noncomm_ring [hP]

/-- The displacement of the canonical intertwiner is bounded by the symmetric
projection gap. -/
theorem norm_spectraCanonicalIntertwiner_sub_one_le_gap
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖spectraCanonicalIntertwiner U V - 1‖ ≤ subspaceGap U V := by
  rw [spectraCanonicalIntertwiner_sub_one]
  calc
    ‖(projection V - projection U) * reflectionOperator U‖
        ≤ ‖projection V - projection U‖ * ‖reflectionOperator U‖ :=
      norm_mul_le _ _
    _ ≤ ‖projection V - projection U‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_reflectionOperator_le_one U)
        (norm_nonneg (projection V - projection U))
    _ = subspaceGap U V := by
      rw [mul_one]
      change ‖V.starProjection - U.starProjection‖ =
        ‖U.starProjection - V.starProjection‖
      rw [show V.starProjection - U.starProjection =
        -(U.starProjection - V.starProjection) by abel, norm_neg]

/-- Equivalent one-sided norm estimate, in the form consumed by
`Units.oneSub`. -/
theorem norm_one_sub_spectraCanonicalIntertwiner_le_gap
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖1 - spectraCanonicalIntertwiner U V‖ ≤ subspaceGap U V := by
  rw [show 1 - spectraCanonicalIntertwiner U V =
    -(spectraCanonicalIntertwiner U V - 1) by abel, norm_neg]
  exact norm_spectraCanonicalIntertwiner_sub_one_le_gap U V

/-- Acuteness places the canonical intertwiner strictly inside the unit ball
around the identity. -/
theorem norm_one_sub_spectraCanonicalIntertwiner_lt_one
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ‖1 - spectraCanonicalIntertwiner U V‖ < 1 :=
  (norm_one_sub_spectraCanonicalIntertwiner_le_gap U V).trans_lt hacute

/-- The canonical intertwiner bundled as a unit in the acute regime. -/
noncomputable def spectraCanonicalIntertwinerUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (H →L[ℂ] H)ˣ :=
  Units.oneSub (1 - spectraCanonicalIntertwiner U V)
    (norm_one_sub_spectraCanonicalIntertwiner_lt_one U V hacute)

/-- The bundled unit has the intended underlying canonical intertwiner. -/
@[simp]
theorem coe_spectraCanonicalIntertwinerUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (spectraCanonicalIntertwinerUnit U V hacute : H →L[ℂ] H) =
      spectraCanonicalIntertwiner U V := by
  simp [spectraCanonicalIntertwinerUnit]

/-- The Spectra polar factor of the canonical intertwiner. -/
noncomputable def spectraCanonicalPolarFactor
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  spectraPolarIsometry (spectraCanonicalIntertwiner U V)

/-- Spectra-backed direct-rotation candidate in the acute regime.  The acute
witness records the intended branch; the underlying polar factor is defined
for every pair. -/
noncomputable def spectraDirectRotation
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hacute : IsAcute U V) : H →L[ℂ] H :=
  spectraCanonicalPolarFactor U V

/-- Polar decomposition of the canonical intertwiner. -/
theorem spectraCanonicalPolarFactor_decomposition
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalPolarFactor U V ∘L
        spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner U V :=
  spectraPolar_decomposition (spectraCanonicalIntertwiner U V)

/-- Polar decomposition stated through the acute direct-rotation candidate. -/
theorem spectraDirectRotation_decomposition
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute ∘L
        spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) =
      spectraCanonicalIntertwiner U V :=
  spectraCanonicalPolarFactor_decomposition U V

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The absolute value of the acute canonical intertwiner is invertible. -/
theorem isUnit_spectraCanonicalAbsoluteValue
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    IsUnit (spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)) := by
  rw [← isUnit_mul_self_iff]
  rw [spectraOperatorAbsoluteValue_mul_self]
  have hS : IsUnit (spectraCanonicalIntertwiner U V) := by
    rw [← coe_spectraCanonicalIntertwinerUnit U V hacute]
    exact (spectraCanonicalIntertwinerUnit U V hacute).isUnit
  exact hS.star.mul hS

/-- The absolute value of the acute canonical intertwiner, bundled as a unit. -/
noncomputable def spectraCanonicalAbsoluteValueUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (H →L[ℂ] H)ˣ :=
  Classical.choose (isUnit_spectraCanonicalAbsoluteValue U V hacute)

/-- The absolute-value unit has the expected underlying operator. -/
@[simp]
theorem coe_spectraCanonicalAbsoluteValueUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (spectraCanonicalAbsoluteValueUnit U V hacute : H →L[ℂ] H) =
      spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) :=
  Classical.choose_spec (isUnit_spectraCanonicalAbsoluteValue U V hacute)

/-- The absolute-value unit is fixed by the star operation. -/
theorem star_spectraCanonicalAbsoluteValueUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    star (spectraCanonicalAbsoluteValueUnit U V hacute) =
      spectraCanonicalAbsoluteValueUnit U V hacute := by
  apply Units.ext
  simp only [Units.coe_star]
  rw [coe_spectraCanonicalAbsoluteValueUnit]
  exact (spectraOperatorAbsoluteValue_isSelfAdjoint
    (spectraCanonicalIntertwiner U V)).star_eq

/-- The Gram units of the canonical intertwiner and its absolute value agree. -/
theorem star_intertwinerUnit_mul_self_eq_absoluteValueUnit_mul_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    star (spectraCanonicalIntertwinerUnit U V hacute) *
        spectraCanonicalIntertwinerUnit U V hacute =
      spectraCanonicalAbsoluteValueUnit U V hacute *
        spectraCanonicalAbsoluteValueUnit U V hacute := by
  apply Units.ext
  simp only [Units.val_mul, Units.coe_star]
  rw [coe_spectraCanonicalIntertwinerUnit,
    coe_spectraCanonicalAbsoluteValueUnit]
  exact (spectraOperatorAbsoluteValue_mul_self
    (spectraCanonicalIntertwiner U V)).symm

/-- The Spectra polar factor bundled as a unit, using the invertible polar
formula `S |S|⁻¹`. -/
noncomputable def spectraCanonicalPolarFactorUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (H →L[ℂ] H)ˣ :=
  spectraCanonicalIntertwinerUnit U V hacute *
    (spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹

/-- The algebraic unit formula agrees with Spectra's polar factor. -/
@[simp]
theorem coe_spectraCanonicalPolarFactorUnit
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (spectraCanonicalPolarFactorUnit U V hacute : H →L[ℂ] H) =
      spectraCanonicalPolarFactor U V := by
  let AUnit := spectraCanonicalAbsoluteValueUnit U V hacute
  let SUnit := spectraCanonicalIntertwinerUnit U V hacute
  let A := spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
  let S := spectraCanonicalIntertwiner U V
  let W := spectraCanonicalPolarFactor U V
  have hA : (AUnit : H →L[ℂ] H) = A :=
    coe_spectraCanonicalAbsoluteValueUnit U V hacute
  have hS : (SUnit : H →L[ℂ] H) = S :=
    coe_spectraCanonicalIntertwinerUnit U V hacute
  have hdecomp : W * A = S := by
    simpa only [ContinuousLinearMap.mul_def] using
      spectraCanonicalPolarFactor_decomposition U V
  change ((SUnit * AUnit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = W
  symm
  calc
    W = W * 1 := (mul_one W).symm
    _ = W * ((AUnit : H →L[ℂ] H) * (↑(AUnit⁻¹) : H →L[ℂ] H)) := by
      rw [AUnit.mul_inv]
    _ = (W * (AUnit : H →L[ℂ] H)) * (↑(AUnit⁻¹) : H →L[ℂ] H) := by
      rw [mul_assoc]
    _ = (W * A) * (↑(AUnit⁻¹) : H →L[ℂ] H) := by rw [hA]
    _ = S * (↑(AUnit⁻¹) : H →L[ℂ] H) := by rw [hdecomp]
    _ = (SUnit : H →L[ℂ] H) * (↑(AUnit⁻¹) : H →L[ℂ] H) := by rw [hS]
    _ = ((SUnit * AUnit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) := rfl

/-- The acute canonical polar factor is a unitary element of the bounded
operator algebra. -/
noncomputable def spectraCanonicalPolarFactorUnitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : unitary (H →L[ℂ] H) := by
  let SUnit := spectraCanonicalIntertwinerUnit U V hacute
  let AUnit := spectraCanonicalAbsoluteValueUnit U V hacute
  have hGram : star SUnit * SUnit = star AUnit * AUnit := by
    rw [star_spectraCanonicalAbsoluteValueUnit U V hacute]
    exact star_intertwinerUnit_mul_self_eq_absoluteValueUnit_mul_self U V hacute
  have hmem : (((SUnit * AUnit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)) ∈
      unitary (H →L[ℂ] H) :=
    (Units.mul_inv_mem_unitary SUnit AUnit).2 hGram
  refine ⟨spectraCanonicalPolarFactor U V, ?_⟩
  rw [← coe_spectraCanonicalPolarFactorUnit U V hacute]
  exact hmem

/-- The unitary subtype has the intended underlying polar factor. -/
@[simp]
theorem coe_spectraCanonicalPolarFactorUnitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ((spectraCanonicalPolarFactorUnitary U V hacute :
        unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      spectraCanonicalPolarFactor U V := rfl

/-- The canonical polar factor preserves every vector norm. -/
theorem norm_spectraCanonicalPolarFactor_apply
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (x : H) :
    ‖spectraCanonicalPolarFactor U V x‖ = ‖x‖ := by
  rw [← coe_spectraCanonicalPolarFactorUnitary U V hacute]
  exact Unitary.norm_map
    (spectraCanonicalPolarFactorUnitary U V hacute) x

/-- The canonical polar factor is onto. -/
theorem spectraCanonicalPolarFactor_surjective
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Function.Surjective (spectraCanonicalPolarFactor U V) := by
  let u := spectraCanonicalPolarFactorUnitary U V hacute
  let e := Unitary.linearIsometryEquiv u
  intro y
  obtain ⟨x, hx⟩ := e.surjective y
  refine ⟨x, ?_⟩
  rw [← coe_spectraCanonicalPolarFactorUnitary U V hacute]
  have hcoe : (e : H →L[ℂ] H) = (u : H →L[ℂ] H) := by
    simpa [e] using Unitary.coe_linearIsometryEquiv_apply u
  exact (congrArg (fun T : H →L[ℂ] H => T x) hcoe).symm.trans hx

/-- The canonical polar factor is one-to-one. -/
theorem spectraCanonicalPolarFactor_injective
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Function.Injective (spectraCanonicalPolarFactor U V) := by
  let u := spectraCanonicalPolarFactorUnitary U V hacute
  let e := Unitary.linearIsometryEquiv u
  intro x y hxy
  apply e.injective
  rw [← coe_spectraCanonicalPolarFactorUnitary U V hacute] at hxy
  have hcoe : (e : H →L[ℂ] H) = (u : H →L[ℂ] H) := by
    simpa [e] using Unitary.coe_linearIsometryEquiv_apply u
  have hx : e x = (u : H →L[ℂ] H) x :=
    congrArg (fun T : H →L[ℂ] H => T x) hcoe
  have hy : e y = (u : H →L[ℂ] H) y :=
    congrArg (fun T : H →L[ℂ] H => T y) hcoe
  exact hx.trans (hxy.trans hy.symm)

/-- The Gram operator of the canonical intertwiner commutes with the source
projection. -/
theorem star_spectraCanonicalIntertwiner_mul_self_commute_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute
      (star (spectraCanonicalIntertwiner U V) *
        spectraCanonicalIntertwiner U V)
      (projection U) := by
  have hSP := spectraCanonicalIntertwiner_mul_projection U V
  have hPSstar :
      projection U * star (spectraCanonicalIntertwiner U V) =
        star (spectraCanonicalIntertwiner U V) * projection V := by
    have h := congrArg star hSP
    simpa only [star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] using h
  show
    (star (spectraCanonicalIntertwiner U V) *
        spectraCanonicalIntertwiner U V) * projection U =
      projection U *
        (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V)
  calc
    (star (spectraCanonicalIntertwiner U V) *
        spectraCanonicalIntertwiner U V) * projection U =
      star (spectraCanonicalIntertwiner U V) *
        (spectraCanonicalIntertwiner U V * projection U) := by
          rw [mul_assoc]
    _ = star (spectraCanonicalIntertwiner U V) *
        (projection V * spectraCanonicalIntertwiner U V) := by rw [hSP]
    _ = (star (spectraCanonicalIntertwiner U V) * projection V) *
        spectraCanonicalIntertwiner U V := by rw [← mul_assoc]
    _ = (projection U * star (spectraCanonicalIntertwiner U V)) *
        spectraCanonicalIntertwiner U V := by rw [← hPSstar]
    _ = projection U *
        (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V) := by rw [mul_assoc]

/-- The absolute value of the canonical intertwiner commutes with the source
projection. -/
theorem spectraCanonicalAbsoluteValue_commute_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute
      (spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V))
      (projection U) := by
  have hGram :
      Commute
        (star (spectraCanonicalIntertwiner U V) *
          spectraCanonicalIntertwiner U V)
        (projection U) :=
    star_spectraCanonicalIntertwiner_mul_self_commute_projection U V
  change Commute
    (CFC.abs (spectraCanonicalIntertwiner U V))
    (projection U)
  rw [CFC.abs, CFC.sqrt_eq_real_sqrt
    (star (spectraCanonicalIntertwiner U V) *
      spectraCanonicalIntertwiner U V)
    (star_mul_self_nonneg (spectraCanonicalIntertwiner U V))]
  exact hGram.cfcₙ_real Real.sqrt

/-- The inverse absolute-value unit also commutes with the source projection. -/
theorem spectraCanonicalAbsoluteValueUnit_inv_commute_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Commute
      (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H)
      (projection U) := by
  have h := spectraCanonicalAbsoluteValue_commute_projection U V
  rw [← coe_spectraCanonicalAbsoluteValueUnit U V hacute] at h
  exact h.units_inv_left

/-- The polar factor is the canonical intertwiner followed by the inverse of
its absolute value. -/
theorem spectraCanonicalPolarFactor_eq_intertwiner_mul_absoluteValueUnit_inv
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraCanonicalPolarFactor U V =
      spectraCanonicalIntertwiner U V *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H) := by
  rw [← coe_spectraCanonicalPolarFactorUnit U V hacute]
  change
    (spectraCanonicalIntertwinerUnit U V hacute : H →L[ℂ] H) *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H) =
      spectraCanonicalIntertwiner U V *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H)
  rw [coe_spectraCanonicalIntertwinerUnit]

/-- The acute Spectra polar factor intertwines the two orthogonal projections. -/
theorem spectraCanonicalPolarFactor_intertwines
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraCanonicalPolarFactor U V * projection U =
      projection V * spectraCanonicalPolarFactor U V := by
  rw [spectraCanonicalPolarFactor_eq_intertwiner_mul_absoluteValueUnit_inv
    U V hacute]
  have hInv :=
    spectraCanonicalAbsoluteValueUnit_inv_commute_projection U V hacute
  calc
    (spectraCanonicalIntertwiner U V *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H)) *
        projection U =
      spectraCanonicalIntertwiner U V *
        ((↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H) *
          projection U) := by rw [mul_assoc]
    _ = spectraCanonicalIntertwiner U V *
        (projection U *
          (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H)) := by
            rw [hInv.eq]
    _ = (spectraCanonicalIntertwiner U V * projection U) *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H) := by
          rw [← mul_assoc]
    _ = (projection V * spectraCanonicalIntertwiner U V) *
        (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H) := by
          rw [spectraCanonicalIntertwiner_mul_projection]
    _ = projection V *
        (spectraCanonicalIntertwiner U V *
          (↑((spectraCanonicalAbsoluteValueUnit U V hacute)⁻¹) : H →L[ℂ] H)) := by
            rw [mul_assoc]

/-- The acute Spectra direct rotation preserves norms. -/
theorem norm_spectraDirectRotation_apply
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (x : H) :
    ‖spectraDirectRotation U V hacute x‖ = ‖x‖ :=
  norm_spectraCanonicalPolarFactor_apply U V hacute x

/-- The acute Spectra direct rotation is onto. -/
theorem spectraDirectRotation_surjective
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Function.Surjective (spectraDirectRotation U V hacute) :=
  spectraCanonicalPolarFactor_surjective U V hacute

/-- The acute Spectra direct rotation is one-to-one. -/
theorem spectraDirectRotation_injective
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Function.Injective (spectraDirectRotation U V hacute) :=
  spectraCanonicalPolarFactor_injective U V hacute

/-- The acute Spectra direct rotation intertwines the two orthogonal
projections. -/
theorem spectraDirectRotation_intertwines
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute * projection U =
      projection V * spectraDirectRotation U V hacute :=
  spectraCanonicalPolarFactor_intertwines U V hacute

/-- The acute Spectra direct rotation also intertwines the complementary
orthogonal projections. -/
theorem spectraDirectRotation_intertwines_complementary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    spectraDirectRotation U V hacute * complementaryProjection U =
      complementaryProjection V * spectraDirectRotation U V hacute := by
  change
    spectraDirectRotation U V hacute * Uᗮ.starProjection =
      Vᗮ.starProjection * spectraDirectRotation U V hacute
  rw [Submodule.starProjection_orthogonal',
    Submodule.starProjection_orthogonal']
  rw [mul_sub, mul_one, sub_mul, one_mul,
    spectraDirectRotation_intertwines U V hacute]

/-- The acute Spectra direct rotation carries the source subspace onto the
target subspace. -/
theorem spectraDirectRotation_maps_subspace
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    U.map (spectraDirectRotation U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[ℂ] H => T x)
      (spectraDirectRotation_intertwines U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      U.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := spectraDirectRotation_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply U.starProjection_eq_self_iff.mp
    apply spectraDirectRotation_injective U V hacute
    have h := congrArg (fun T : H →L[ℂ] H => T x)
      (spectraDirectRotation_intertwines U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      V.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-- The acute Spectra direct rotation also carries the orthogonal complement
of the source subspace onto the orthogonal complement of the target. -/
theorem spectraDirectRotation_maps_orthogonalComplement
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Uᗮ.map (spectraDirectRotation U V hacute).toLinearMap = Vᗮ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply Vᗮ.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : H →L[ℂ] H => T x)
      (spectraDirectRotation_intertwines_complementary U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Uᗮ.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := spectraDirectRotation_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply Uᗮ.starProjection_eq_self_iff.mp
    apply spectraDirectRotation_injective U V hacute
    have h := congrArg (fun T : H →L[ℂ] H => T x)
      (spectraDirectRotation_intertwines_complementary U V hacute)
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Vᗮ.starProjection_eq_self_iff.mpr hy] at h
    exact h

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
