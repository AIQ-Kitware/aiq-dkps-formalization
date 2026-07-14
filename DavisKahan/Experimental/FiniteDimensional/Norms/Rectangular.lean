/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
# Compatibility surface for unfinished rectangular norm constructors

The proved rectangular unitarily invariant norm infrastructure moved to
`ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm`.
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

namespace RectangularUnitarilyInvariantNorm

/-- Every square unitarily invariant norm has a compatible rectangular
extension, unique after fixing its symmetric gauge family across dimensions. -/
noncomputable def ofSquareFamily
    (Ns : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [FiniteDimensional 𝕜 H], UnitarilyInvariantNorm 𝕜 H) :
    RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- Schatten `p`-norm for `1 ≤ p`. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry


end RectangularUnitarilyInvariantNorm
end DavisKahanTheory
end ForMathlib
