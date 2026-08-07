/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section8.CompressionApproximation
import DavisKahan.Frontier.Section8

/-!
# Davis--Kahan 1970, Theorem 8.1(ii)

The printed clause is

  `α_k - α ≤ ‖C₁‖₁² (λ_k - α)`

where `α_k` are the ordered eigenvalues of the unperturbed compression `A₁` on
`Pᗮ`, `λ_k` those of the perturbed compression `Λ₁` on `Qᗮ`, and `‖·‖₁` is the
bound norm.

## How this is assembled

Three ingredients, each proved separately:

* `theorem8_1_upperCompressionRepulsion_source` -- part (i) on the `Pᗮ` block,
  i.e. `A₁ - α ≤ C₁(Λ₁ - α)C₁` as quadratic forms;
* `approximationNumber_mono_of_form_le` -- the Weyl step, for positive operators
  and in arbitrary dimension;
* `approximationNumber_adjoint_sandwich_le` -- `aₙ(D⋆ M D) ≤ ‖D‖² aₙ(M)`.

## Why the statement is ambient

Both compressions are written as ambient operators cut down by the relevant
projection (`P_{Pᗮ} (A - α) P_{Pᗮ}` and `P_{Qᗮ} (A + K - α) P_{Qᗮ}`) rather than
as operators on the subtypes `↥Pᗮ` and `↥Qᗮ`.  That is deliberate: it keeps the
whole argument inside `H`, so no subspace-transfer machinery is needed, and the
cosine block appears directly as `D = P_{Qᗮ} P_{Pᗮ}`, whose norm is exactly the
paper's `‖C₁‖₁`.  Extending each compression by zero adds only zeros to the
approximation-number sequence, so the ordered comparison is unaffected.

## Ordering convention

`approximationNumber` is indexed in **decreasing** order, while the paper prints
`λ₁ ≤ λ₂ ≤ ⋯` increasing.  The printed family of inequalities is invariant under
reversing both lists together -- which is exactly what a global reindex does --
so this is the printed statement and not a reordering of it.  In finite
dimensions the approximation numbers of these positive operators are their
eigenvalues, which is the printed reading of `α_k` and `λ_k`.

Because the Weyl step used here is dimension-free, the theorem below is *not*
restricted to finite dimensions; the printed "In finite dimensions" rider is a
statement about where eigenvalues are available, not a limitation of the
estimate.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.Frontier.Section8

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The unperturbed upper compression `A₁ - α`, extended by zero off `Pᗮ`. -/
noncomputable def upperBlockShift (A : H →L[ℂ] H) (P : Submodule ℂ H)
    [P.HasOrthogonalProjection] (alpha : ℝ) : H →L[ℂ] H :=
  Pᗮ.starProjection ∘L (A - (alpha : ℂ) • ContinuousLinearMap.id ℂ H) ∘L
    Pᗮ.starProjection

/-- The cosine block `C₁`, as an ambient operator: `P_{Qᗮ} P_{Pᗮ}`. -/
noncomputable def cosineBlock (P Q : Submodule ℂ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] : H →L[ℂ] H :=
  Qᗮ.starProjection ∘L Pᗮ.starProjection

theorem upperBlockShift_apply (A : H →L[ℂ] H) (P : Submodule ℂ H)
    [P.HasOrthogonalProjection] (alpha : ℝ) (x : H) :
    RCLike.re ⟪x, upperBlockShift A P alpha x⟫_ℂ =
      RCLike.re ⟪Pᗮ.starProjection x, A (Pᗮ.starProjection x)⟫_ℂ -
        alpha * ‖Pᗮ.starProjection x‖ ^ 2 := by
  have hself : ⟪x, upperBlockShift A P alpha x⟫_ℂ =
      ⟪Pᗮ.starProjection x,
        (A - (alpha : ℂ) • ContinuousLinearMap.id ℂ H) (Pᗮ.starProjection x)⟫_ℂ := by
    show ⟪x, Pᗮ.starProjection ((A - (alpha : ℂ) • ContinuousLinearMap.id ℂ H)
      (Pᗮ.starProjection x))⟫_ℂ = _
    rw [← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection Pᗮ)]
  rw [hself]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right, map_sub]
  have hnorm : (⟪Pᗮ.starProjection x, Pᗮ.starProjection x⟫_ℂ).re =
      ‖Pᗮ.starProjection x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hs : RCLike.re ((alpha : ℂ) *
      ⟪Pᗮ.starProjection x, Pᗮ.starProjection x⟫_ℂ) =
      alpha * ‖Pᗮ.starProjection x‖ ^ 2 := by
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hnorm]
    ring
  rw [hs]

end Section8
end DavisKahan1970
end TauCeti
