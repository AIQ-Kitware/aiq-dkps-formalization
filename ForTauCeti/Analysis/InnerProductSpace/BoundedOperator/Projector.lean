/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.SinTheta

/-!
# Sharp projector geometry for bounded Davis--Kahan theory

The two-projection norm identity and the sharp factor-one coercive projector
theorem over arbitrary `RCLike` scalars.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/BoundedOperator/Projector.lean`
until 2026-07-29, when lane Y3(b3) moved the dependency-closed base of the sin-Θ core
into the staging layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-! ### Compatibility names for generic projection geometry -/

/-- Block-diagonal norm identity, re-exported from the generic operator API. -/
theorem norm_add_eq_max_of_block {P A B : H →L[𝕜] H}
    (hPsa : IsSelfAdjoint P) (hPid : IsIdempotentElem P)
    (hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖) (hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖)
    (hAP : A * P = A) (hPA : P * A = A) (hBP : B * P = 0) (hPB : P * B = 0) :
    ‖A + B‖ = max ‖A‖ ‖B‖ :=
  ContinuousLinearMap.norm_add_eq_max_of_block hPsa hPid hPnorm hcompnorm
    hAP hPA hBP hPB

/-- Sharp norm identity for two orthogonal projections, re-exported from the
 generic projection-gap API. -/
theorem norm_starProjection_sub_eq_max (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖(U.starProjection - V.starProjection : H →L[𝕜] H)‖ =
      max ‖(1 - V.starProjection) ∘L U.starProjection‖
          ‖(1 - U.starProjection) ∘L V.starProjection‖ :=
  U.norm_starProjection_sub_eq_max V

/-- **The sharp (factor-one) operator-norm Davis--Kahan projector theorem.**  With
a two-sided coercive spectral gap — `A`'s form `≥ (c+g)` on `U` and `≤ c` on
`Uᗮ`, `B`'s form `≥ (c+g)` on `W` and `≤ c` on `Wᗮ` — the orthogonal
projectors onto these reducing subspaces on an arbitrary `RCLike` Hilbert space
satisfy the sharp bound

`‖P_U − P_W‖ ≤ ‖B − A‖ / g`

with constant one and no equal-rank hypothesis.  Combines the projector-difference
identity `norm_starProjection_sub_eq_max` with the two dimension-free directed
`sin Θ` estimates `sinTheta_directed_coercive`. -/
theorem opNorm_starProjection_sub_le_of_coercive
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : Reduces A U) (hW : Reduces B W)
    {c g : ℝ} (hg : 0 < g)
    (hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUlo : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hWc : ∀ x ∈ W, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hWlo : ∀ x ∈ Wᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g := by
  rw [norm_starProjection_sub_eq_max U W]
  refine max_le ?_ ?_
  · rw [show (1 - W.starProjection : H →L[𝕜] H) = Wᗮ.starProjection from
      (Submodule.starProjection_orthogonal' W).symm]
    exact sinTheta_directed_coercive hA hB hU (reduces_orthogonalComplement hB hW.2) hg hUc hWlo
  · rw [show (1 - U.starProjection : H →L[𝕜] H) = Uᗮ.starProjection from
      (Submodule.starProjection_orthogonal' U).symm]
    have h := sinTheta_directed_coercive hB hA hW (reduces_orthogonalComplement hA hU.2) hg hWc hUlo
    rwa [show ‖A - B‖ = ‖B - A‖ from by rw [← neg_sub, norm_neg]] at h


/-- Sharp projector bound stated with reusable subspace form-bound predicates. -/
theorem opNorm_starProjection_sub_le_of_formBounds
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : Reduces A U) (hW : Reduces B W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : A.LowerFormBoundOn U (c + g))
    (hUlo : A.UpperFormBoundOn Uᗮ c)
    (hWhi : B.LowerFormBoundOn W (c + g))
    (hWlo : B.UpperFormBoundOn Wᗮ c) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g :=
  opNorm_starProjection_sub_le_of_coercive hA hB hU hW hg hUhi hUlo hWhi hWlo


end DavisKahan
end TauCeti
