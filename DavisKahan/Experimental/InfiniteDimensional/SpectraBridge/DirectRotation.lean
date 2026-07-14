/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Reflection
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.OperatorAbsoluteValue
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Spectra-backed canonical intertwiner and direct-rotation candidate

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

The Spectra polar factor is exposed as a parallel direct-rotation candidate.
Its unitarity and projection-intertwining properties are intentionally left to
the next layer; this file establishes the invertible pre-polar operator and the
algebraic identities those proofs consume.
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
