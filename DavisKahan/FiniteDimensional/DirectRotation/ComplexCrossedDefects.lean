/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Geometry.Halmos.CrossedDefectGap

/-!
# Equal rank supplies the nonacute direct-rotation defect identification

In finite dimension, the two crossed defects of a pair of equal-rank subspaces
have the same dimension, without an acuteness assumption.  This is the precise
hypothesis required by the general Halmos completed direct rotation.

The proof uses the Grassmann formula and orthogonal-complement dimension,
not an enumeration of principal angles.
-/

public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open Module (finrank)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The dimensions of `U ∩ V⊥` and `V ∩ U⊥` differ by the dimensions of
`U` and `V`.  Here we state the equal-rank specialization. -/
theorem crossed_defect_finrank_eq_of_finrank_eq
    (U V : Submodule ℂ H) (hUV : finrank ℂ U = finrank ℂ V) :
    finrank ℂ (halmosSourceDefect U V) =
      finrank ℂ (halmosTargetDefect U V) := by
  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq U (Vᗮ)
  have hU := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (K := U)
  have hV := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (K := V)
  have hOrth : (U ⊔ Vᗮ)ᗮ = Uᗮ ⊓ V := by
    calc
      (U ⊔ Vᗮ)ᗮ = Uᗮ ⊓ (Vᗮ)ᗮ := (Submodule.inf_orthogonal U (Vᗮ)).symm
      _ = Uᗮ ⊓ V := by rw [Submodule.orthogonal_orthogonal]
  have hSum := Submodule.finrank_add_finrank_orthogonal
    (𝕜 := ℂ) (K := U ⊔ Vᗮ)
  rw [hOrth] at hSum
  change finrank ℂ (U ⊓ Vᗮ : Submodule ℂ H) =
    finrank ℂ (Uᗮ ⊓ V : Submodule ℂ H)
  omega

/-- In finite dimension, equal-rank complex subspaces automatically satisfy
Davis--Kahan's nonacute crossed-defect hypothesis (3.5). -/
theorem crossedDefectsEquivalent_of_finrank_eq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hUV : finrank ℂ U = finrank ℂ V) :
    CrossedDefectsEquivalent U V :=
  (crossedDefectsEquivalent_iff_finrank_eq U V).2
    (crossed_defect_finrank_eq_of_finrank_eq U V hUV)

/-- An explicit isometric equivalence of the crossed defects, including
right-angle sectors and zero-dimensional cases. -/
@[expose]
noncomputable def finiteCrossedDefectEquiv
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hUV : finrank ℂ U = finrank ℂ V) :
    halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V :=
  Classical.choice (crossedDefectsEquivalent_of_finrank_eq U V hUV)

end DavisKahan
end TauCeti
