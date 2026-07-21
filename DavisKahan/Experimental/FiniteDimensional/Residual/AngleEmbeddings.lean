/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Residual.AngleEmbedding
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm
import ForMathlib.Analysis.InnerProductSpace.MoorePenroseInverse

/-!
# Coordinate tangent and double-angle embeddings

For an isometric trial map `X : F → E`, write

* `C = P_U X : F → E`,
* `S = P_{Uᗮ} X : F → E`,
* `|C| = (C⋆C)^(1/2) : F → F`.

The coordinate tangent is `S |C|⁺`.  The double-angle source cosine is
`C⋆C - S⋆S`, while the rectangular double-angle sine is `2 S |C|`.  These
choices put every denominator on the trial-coordinate space and avoid the
extra cosine factor produced by the former ambient pseudoinverse formulas.

The definitions below are totalized by Moore--Penrose inverses.  Under the
corresponding injectivity assumptions, the compatibility lemmas identify them
with the proof-carrying `inverseOnRange` construction.  Singular-value
identifications still require a simultaneous CS decomposition and are not
asserted here merely from these definitions.
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

/-- Trial-coordinate tangent map `S |C|⁺`.

Its nonzero singular values are intended to be the tangents of the principal
angles.  That identification is a separate CS-decomposition theorem; this
definition only fixes the canonical coordinate semantics. -/
noncomputable def tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinThetaEmbedding U X ∘ₗ
    FiniteDimensional.moorePenroseInverse (cosThetaMagnitude U X)

/-- Under transversality, the totalized tangent agrees with composition by the
proof-carrying inverse of the positive coordinate cosine. -/
theorem tanThetaEmbedding_eq_inverseOnRange
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (hC : Function.Injective (cosThetaEmbedding U X)) :
    tanThetaEmbedding U X =
      sinThetaEmbedding U X ∘ₗ
        FiniteDimensional.inverseOnRange (cosThetaMagnitude U X)
          (cosThetaMagnitude_injective U X hC) := by
  rw [tanThetaEmbedding,
    FiniteDimensional.moorePenroseInverse_eq_inverseOnRange]

/-- Transversality supplies the inverse required by the coordinate tangent. -/
theorem tanThetaEmbedding_eq_inverseOnRange_of_isTransverse
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    tanThetaEmbedding U X =
      sinThetaEmbedding U X ∘ₗ
        FiniteDimensional.inverseOnRange (cosThetaMagnitude U X)
          (cosThetaMagnitude_injective U X
            (LinearMap.ker_eq_bot.mp
              ((tanThetaEmbedding_defined_iff U X).mp htrans))) :=
  -- the injectivity witness occurs only in a proof position, so unification
  -- cannot recover it; it has to be supplied explicitly
  tanThetaEmbedding_eq_inverseOnRange U X
    (LinearMap.ker_eq_bot.mp ((tanThetaEmbedding_defined_iff U X).mp htrans))

/-- Trial-coordinate double-angle sine `2 S |C|`.

On a simultaneous principal-angle basis this has singular values
`2 sin θᵢ cos θᵢ = sin (2 θᵢ)`. -/
noncomputable def sinTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  (2 : 𝕜) • (sinThetaEmbedding U X ∘ₗ cosThetaMagnitude U X)

/-- Every rectangular unitarily invariant norm of the coordinate double-angle
sine is at most twice the corresponding single-angle sine norm. -/
theorem sinTwoThetaEmbedding_uiNorm_le_two_mul
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E) :
    N (sinTwoThetaEmbedding U X) ≤ 2 * N (sinThetaEmbedding U X) := by
  rw [sinTwoThetaEmbedding, N.smul_eq, RCLike.norm_ofNat]
  have hcomp := N.comp_le_mul_opNorm
    (sinThetaEmbedding U X) (cosThetaMagnitude U X)
  calc
    2 * N (sinThetaEmbedding U X ∘ₗ cosThetaMagnitude U X)
        ≤ 2 * (N (sinThetaEmbedding U X) *
          ‖(cosThetaMagnitude U X).toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ ≤ 2 * (N (sinThetaEmbedding U X) * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (cosThetaMagnitude_opNorm_le_one U X) (N.nonneg _))
        (by positivity)
    _ = 2 * N (sinThetaEmbedding U X) := by ring

/-- Totalized double-angle tangent
`(2 S |C|) (C⋆C - S⋆S)⁺`. -/
noncomputable def tanTwoThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  sinTwoThetaEmbedding U X ∘ₗ
    FiniteDimensional.moorePenroseInverse
      (cosTwoThetaSourceOperator U X)

/-- Under quarter-turn avoidance expressed as injectivity of the source
cosine, the totalized double-angle tangent agrees with `inverseOnRange`. -/
theorem tanTwoThetaEmbedding_eq_inverseOnRange
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : F →ₗᵢ[𝕜] E)
    (hC₂ : Function.Injective (cosTwoThetaSourceOperator U X)) :
    tanTwoThetaEmbedding U X =
      sinTwoThetaEmbedding U X ∘ₗ
        FiniteDimensional.inverseOnRange (cosTwoThetaSourceOperator U X) hC₂ := by
  rw [tanTwoThetaEmbedding,
    FiniteDimensional.moorePenroseInverse_eq_inverseOnRange]

end DavisKahanTheory
end ForMathlib
