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

end DavisKahanExt
end ForMathlib
