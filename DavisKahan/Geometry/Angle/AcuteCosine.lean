/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Geometry.Angle.Proposition35Infinite
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Invertibility of the principal cosine for uniformly acute pairs -/

public section

noncomputable section

namespace TauCeti.DavisKahan.Proposition35

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- A projection gap below one makes the full principal cosine invertible,
also on infinite-dimensional Hilbert spaces. -/
theorem isUnit_section3CosAngleOperator_of_isUniformlyAcute
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute K L) : IsUnit (section3CosAngleOperator K L) := by
  rw [section3CosAngleOperator_eq_canonicalAbsoluteValue]
  exact isUnit_spectraCanonicalAbsoluteValue K L hacute

/-- The principal cosine of a uniformly acute pair has no kernel. -/
theorem section3CosAngleOperator_injective_of_isUniformlyAcute
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute K L) : Function.Injective (section3CosAngleOperator K L) :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp
    (isUnit_section3CosAngleOperator_of_isUniformlyAcute K L hacute)).injective

end TauCeti.DavisKahan.Proposition35
