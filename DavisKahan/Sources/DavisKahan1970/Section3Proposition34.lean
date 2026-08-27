/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section3Proposition34Printed

/-!
# Davis--Kahan 1970, Proposition 3.4 over complex Hilbert spaces

> **Proposition 3.4.** If `C₀² ≥ ½`, then `U²` is the direct rotation of
> `Q₋ℋ` to `Qℋ`.

Definition 3.1 asks a direct rotation for five things: unitarity, the
intertwining relation, genuine positivity `C₀ ≥ 0` and `C₁ ≥ 0` of the two
diagonal blocks, and the crossed-block relation `S₁ = S₀*`.  The paper's own
proof of Proposition 3.4 discharges the positivity clause in that genuine
operator sense: "we must still prove (i) and (ii), which for this case take the
form `Q₋U²Q₋ ≥ 0` ...".

`TauCeti.DavisKahan.proposition3_4_source_full` concludes the
weaker `IsPaperDirectRotation` predicate, whose diagonal clauses record only a
nonnegative real numerical range, `0 ≤ re ⟪x, (P T P) x⟫`.  Over a complex
Hilbert space that does not even force the compression to be self-adjoint, so it
is strictly weaker than Definition 3.1 and cannot by itself certify the printed
proposition.

This module closes that gap.  `positiveDiagonalBlocks_of_sq` is the upgrade: for
a paper direct rotation whose square is the known reflection product, the two
diagonal compressions are forced to be self-adjoint, and their recorded
numerical-range signs then *are* operator positivity.  The argument was written
for the real descent and lived privately in `Section3Proposition34Real.lean`; it
is promoted here because the complex source statement needs it too.

`proposition3_4_source_full_complex` is the resulting public complex
source-facing theorem, with the printed hypothesis `C₀² ≥ ½` and the full
Definition 3.1 conclusion.  It adds no acuteness, compactness,
finite-dimensionality, or separability hypothesis.  The real counterpart is
`TauCeti.DavisKahan1970.proposition3_4_source_full_real`.
-/

open scoped InnerProductSpace ComplexOrder

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.Frontier
open TauCeti.DavisKahanExt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Definition 3.1 positivity upgrade.**

For a complex paper direct rotation whose square is the known reflection
product, the reflection conjugation `J_K T J_K = T*` forces both diagonal
compressions to be self-adjoint.  A self-adjoint operator with nonnegative real
numerical range is positive, so the numerical-range clauses of
`IsPaperDirectRotation` become the genuine `C₀ ≥ 0`, `C₁ ≥ 0` of Definition 3.1.
-/
theorem positiveDiagonalBlocks_of_sq
    (K L : Submodule ℂ H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : IsPaperDirectRotation K L T)
    (hsq : T * T = spectraReflectionProduct K L) :
    (K.starProjection * T * K.starProjection).IsPositive ∧
      (Kᗮ.starProjection * T * Kᗮ.starProjection).IsPositive := by
  have hintR : T * K.reflectionOperator = L.reflectionOperator * T := by
    rw [DavisKahan.reflectionOperator_eq_projection_add_projection_sub_one K,
      DavisKahan.reflectionOperator_eq_projection_add_projection_sub_one L,
      mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul, hT.intertwines]
  have hconj : K.reflectionOperator * T * K.reflectionOperator = star T :=
    DavisKahan.reflection_conjugate_eq_star_of_sq_of_intertwines
      K L T hT.unitary_mem hsq hintR
  have hsource_sa : IsSelfAdjoint (K.starProjection * T * K.starProjection) := by
    rw [IsSelfAdjoint, star_mul, star_mul,
      (isSelfAdjoint_starProjection K).star_eq]
    calc
      K.starProjection * star T * K.starProjection =
          K.starProjection * (K.reflectionOperator * T * K.reflectionOperator) *
            K.starProjection := by rw [hconj]
      _ = (K.starProjection * K.reflectionOperator) * T *
            (K.reflectionOperator * K.starProjection) := by
          simp only [mul_assoc]
      _ = K.starProjection * T * K.starProjection := by
          rw [projection_mul_reflectionOperator_self K,
            reflectionOperator_mul_projection_self K]
  have hRsub : K.reflectionOperator = K.starProjection - Kᗮ.starProjection := by
    rw [DavisKahan.reflectionOperator_eq_projection_add_projection_sub_one K]
    have hsum : K.starProjection + Kᗮ.starProjection = (1 : H →L[ℂ] H) := by
      apply ContinuousLinearMap.ext
      intro x
      simpa only [add_apply, one_apply_eq_self] using
        K.starProjection_add_starProjection_orthogonal x
    rw [← hsum]
    abel
  have hPcR : Kᗮ.starProjection * K.reflectionOperator = -Kᗮ.starProjection := by
    rw [hRsub, mul_sub, DavisKahan.complementaryProjection_mul_projection K,
      DavisKahan.complementaryProjection_sq K, zero_sub]
  have hRPc : K.reflectionOperator * Kᗮ.starProjection = -Kᗮ.starProjection := by
    rw [hRsub, sub_mul, DavisKahan.projection_mul_complementaryProjection K,
      DavisKahan.complementaryProjection_sq K, zero_sub]
  have hcomplement_sa : IsSelfAdjoint (Kᗮ.starProjection * T * Kᗮ.starProjection) := by
    rw [IsSelfAdjoint, star_mul, star_mul,
      (isSelfAdjoint_starProjection Kᗮ).star_eq]
    calc
      Kᗮ.starProjection * star T * Kᗮ.starProjection =
          Kᗮ.starProjection * (K.reflectionOperator * T * K.reflectionOperator) *
            Kᗮ.starProjection := by rw [hconj]
      _ = (Kᗮ.starProjection * K.reflectionOperator) * T *
            (K.reflectionOperator * Kᗮ.starProjection) := by
          simp only [mul_assoc]
      _ = (-Kᗮ.starProjection) * T * (-Kᗮ.starProjection) := by rw [hPcR, hRPc]
      _ = Kᗮ.starProjection * T * Kᗮ.starProjection := by noncomm_ring
  constructor
  · refine ContinuousLinearMap.isPositive_def'.mpr ⟨hsource_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.source_compression_nonnegative x
  · refine ContinuousLinearMap.isPositive_def'.mpr ⟨hcomplement_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.complement_compression_nonnegative x

/-- **Davis--Kahan 1970, Proposition 3.4, complex source scope, with the genuine
Definition 3.1 conclusion.**

`W` is an arbitrary direct rotation from `Uℋ` to `Vℋ` in the printed
Definition 3.1 sense: unitary, intertwining, with the two diagonal blocks
genuinely positive (`C₀ ≥ 0`, `C₁ ≥ 0`) and the printed crossed-block relation.
`hcos` is the printed `C₀² ≥ ½` read through equation (3.7).

The conclusion is Definition 3.1 for `W²` and the ordered pair `(Q₋ℋ, Qℋ)`,
clause by clause, with `IsPositive` diagonal compressions rather than the weaker
numerical-range predicate.

No acuteness, uniform acuteness, compactness, finite-dimensionality, or
separability hypothesis is used. -/
theorem proposition3_4_source_full_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : H →L[ℂ] H)
    (hunitary : W ∈ unitary (H →L[ℂ] H))
    (hintertwines : W * U.starProjection = V.starProjection * W)
    (hcrossed : Uᗮ.starProjection * W * U.starProjection =
      -star (U.starProjection * W * Uᗮ.starProjection))
    (hsource_pos : (U.starProjection * W * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) :
    (W * W) ∈ unitary (H →L[ℂ] H) ∧
      (W * W) * (reflectedSubspace U V).starProjection =
        V.starProjection * (W * W) ∧
      ((reflectedSubspace U V).starProjection * (W * W) *
        (reflectedSubspace U V).starProjection).IsPositive ∧
      ((reflectedSubspace U V)ᗮ.starProjection * (W * W) *
        (reflectedSubspace U V)ᗮ.starProjection).IsPositive ∧
      (reflectedSubspace U V)ᗮ.starProjection * (W * W) *
          (reflectedSubspace U V).starProjection =
        -star ((reflectedSubspace U V).starProjection * (W * W) *
          (reflectedSubspace U V)ᗮ.starProjection) := by
  have hpaper : IsPaperDirectRotation (reflectedSubspace U V) V (W * W) :=
    proposition3_4_source_full U V W hunitary hintertwines
      hcrossed
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hsource_pos)
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hcomplement_pos) hcos
  have hWsq : W * W = spectraReflectionProduct U V :=
    sq_eq_spectraReflectionProduct U V W hunitary hintertwines
      hsource_pos.isSelfAdjoint hcomplement_pos.isSelfAdjoint hcrossed
  have hrefl : (reflectedSubspace U V).reflectionOperator =
      U.reflectionOperator * V.reflectionOperator * U.reflectionOperator :=
    reflectionOperator_reflectedSubspace V U
  have hRU : U.reflectionOperator * U.reflectionOperator = 1 :=
    reflectionOperator_mul_self_complex U
  have hsq : (W * W) * (W * W) =
      spectraReflectionProduct (reflectedSubspace U V) V := by
    show (W * W) * (W * W) =
      V.reflectionOperator * (reflectedSubspace U V).reflectionOperator
    rw [hrefl, hWsq]
    noncomm_ring
  have hpos := positiveDiagonalBlocks_of_sq (reflectedSubspace U V) V (W * W)
    hpaper hsq
  exact ⟨mul_mem hunitary hunitary, hpaper.intertwines, hpos.1, hpos.2,
    hpaper.crossed_blocks⟩

end DavisKahan1970
end TauCeti
