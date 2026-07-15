/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.DirectRotation
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotation

/-!
# Complex direct rotation backed by Spectra

This module connects the proof-complete complex polar-factor construction to
Davis--Kahan's established direct-rotation namespace and theorem interfaces.
The scalar-generic declarations remain independent; these declarations provide
the completed complex specialization without weakening or replacing the real
and general `RCLike` program.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahanExt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The completed complex direct rotation obtained from the Spectra polar
factor of the canonical intertwiner. -/
noncomputable abbrev complexDirectRotation
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : H →L[ℂ] H :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation U V hacute

/-- The complex direct rotation is norm-preserving and onto. -/
theorem complexDirectRotation_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    IsUnitaryOperator (complexDirectRotation U V hacute) :=
  ⟨_root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.norm_spectraDirectRotation_apply
      U V hacute,
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_surjective
      U V hacute⟩

/-- The complex direct rotation intertwines the source and target
projections. -/
theorem complexDirectRotation_intertwines
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    complexDirectRotation U V hacute ∘L projection U =
      projection V ∘L complexDirectRotation U V hacute := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_intertwines
      U V hacute

/-- The complex direct rotation maps the source subspace onto the target
subspace. -/
theorem complexDirectRotation_maps_subspace
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    U.map (complexDirectRotation U V hacute).toLinearMap = V :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_maps_subspace
    U V hacute

/-- The complex direct rotation maps orthogonal complements onto orthogonal
complements. -/
theorem complexDirectRotation_maps_orthogonalComplement
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Uᗮ.map (complexDirectRotation U V hacute).toLinearMap = Vᗮ :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_maps_orthogonalComplement
    U V hacute

/-- The foundational direct-rotation properties are simultaneously realized
in the complex acute case. -/
theorem exists_complexDirectRotation
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ∃ W : H →L[ℂ] H,
      IsUnitaryOperator W ∧
      W ∘L projection U = projection V ∘L W ∧
      U.map W.toLinearMap = V :=
  ⟨complexDirectRotation U V hacute,
    complexDirectRotation_unitary U V hacute,
    complexDirectRotation_intertwines U V hacute,
    complexDirectRotation_maps_subspace U V hacute⟩


/-- The complete foundational complex package, including transport of the
orthogonal complements. -/
theorem exists_complexDirectRotation_with_complements
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ∃ W : H →L[ℂ] H,
      IsUnitaryOperator W ∧
      W ∘L projection U = projection V ∘L W ∧
      U.map W.toLinearMap = V ∧
      Uᗮ.map W.toLinearMap = Vᗮ :=
  ⟨complexDirectRotation U V hacute,
    complexDirectRotation_unitary U V hacute,
    complexDirectRotation_intertwines U V hacute,
    complexDirectRotation_maps_subspace U V hacute,
    complexDirectRotation_maps_orthogonalComplement U V hacute⟩


/-! ## Elementary adjoint and reflection consequences -/

/-- The complex direct rotation is a unitary element of the bounded operator
algebra. -/
theorem complexDirectRotation_mem_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    complexDirectRotation U V hacute ∈ unitary (H →L[ℂ] H) :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_mem_unitary
    U V hacute

/-- The adjoint of the complex direct rotation is its left inverse. -/
theorem star_complexDirectRotation_comp_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    star (complexDirectRotation U V hacute) ∘L
        complexDirectRotation U V hacute = 1 := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_mul_self
      U V hacute

/-- The adjoint of the complex direct rotation is its right inverse. -/
theorem complexDirectRotation_comp_star_self
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    complexDirectRotation U V hacute ∘L
        star (complexDirectRotation U V hacute) = 1 := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_mul_star_self
      U V hacute

/-- The adjoint intertwines the target projection back to the source
projection. -/
theorem star_complexDirectRotation_intertwines
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    star (complexDirectRotation U V hacute) ∘L projection V =
      projection U ∘L star (complexDirectRotation U V hacute) := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_intertwines
      U V hacute

/-- The adjoint also intertwines complementary target and source projections. -/
theorem star_complexDirectRotation_intertwines_complementary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    star (complexDirectRotation U V hacute) ∘L complementaryProjection V =
      complementaryProjection U ∘L star (complexDirectRotation U V hacute) := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_intertwines_complementary
      U V hacute

/-- Conjugation by the complex direct rotation carries the source projection
to the target projection. -/
theorem complexDirectRotation_conjugates_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (complexDirectRotation U V hacute ∘L projection U) ∘L
        star (complexDirectRotation U V hacute) = projection V := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_conjugates_projection
      U V hacute

/-- Conjugation by the adjoint carries the target projection back to the source projection. -/
theorem star_complexDirectRotation_conjugates_projection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (star (complexDirectRotation U V hacute) ∘L projection V) ∘L
        complexDirectRotation U V hacute = projection U := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_conjugates_projection
      U V hacute

/-- Conjugation by the complex direct rotation carries complementary source projection to the
complementary target projection. -/
theorem complexDirectRotation_conjugates_complementaryProjection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (complexDirectRotation U V hacute ∘L complementaryProjection U) ∘L
        star (complexDirectRotation U V hacute) = complementaryProjection V := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_conjugates_complementaryProjection
      U V hacute

/-- The complex direct rotation intertwines the source and target
reflections. -/
theorem complexDirectRotation_intertwines_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    complexDirectRotation U V hacute ∘L reflectionOperator U =
      reflectionOperator V ∘L complexDirectRotation U V hacute := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_intertwines_reflection
      U V hacute

/-- The adjoint intertwines the target reflection back to the source reflection. -/
theorem star_complexDirectRotation_intertwines_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    star (complexDirectRotation U V hacute) ∘L reflectionOperator V =
      reflectionOperator U ∘L star (complexDirectRotation U V hacute) := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_intertwines_reflection
      U V hacute

/-- Conjugation by the complex direct rotation carries the source reflection
to the target reflection. -/
theorem complexDirectRotation_conjugates_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (complexDirectRotation U V hacute ∘L reflectionOperator U) ∘L
        star (complexDirectRotation U V hacute) = reflectionOperator V := by
  simpa only [ContinuousLinearMap.mul_def] using
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_conjugates_reflection
      U V hacute

/-- The adjoint of the complex direct rotation maps the target subspace back
onto the source subspace. -/
theorem star_complexDirectRotation_maps_subspace
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    V.map ((star (complexDirectRotation U V hacute) :
      H →L[ℂ] H).toLinearMap) = U :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_maps_subspace
    U V hacute

/-- The adjoint of the complex direct rotation maps the target orthogonal
complement back onto the source orthogonal complement. -/
theorem star_complexDirectRotation_maps_orthogonalComplement
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Vᗮ.map ((star (complexDirectRotation U V hacute) :
      H →L[ℂ] H).toLinearMap) = Uᗮ :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.star_spectraDirectRotation_maps_orthogonalComplement
    U V hacute


/-! ## Reflection-product reduction -/

/-- The ordered target/source reflection product associated with the complex
acute pair. -/
noncomputable abbrev complexReflectionProduct
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraReflectionProduct U V

/-- The ordered reflection product is unitary. -/
theorem complexReflectionProduct_mem_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    complexReflectionProduct U V ∈ unitary (H →L[ℂ] H) :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraReflectionProduct_mem_unitary
    U V

omit [CompleteSpace H] in
/-- Twice the canonical pre-polar intertwiner is the identity plus the ordered
reflection product. -/
theorem complexCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraCanonicalIntertwiner U V +
        _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraCanonicalIntertwiner U V =
      1 + complexReflectionProduct U V :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct
    U V

/-- The complex direct rotation commutes with the ordered reflection product.
This is the final algebraic reduction before proving that its square equals
that product. -/
theorem complexDirectRotation_commute_reflectionProduct
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Commute (complexDirectRotation U V hacute)
      (complexReflectionProduct U V) :=
  _root_.ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_commute_reflectionProduct
    U V hacute

end DavisKahanExt
end ForMathlib
