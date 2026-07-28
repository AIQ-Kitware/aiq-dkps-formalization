/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventBound
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# A self-adjoint operator has real spectrum

The basic criterion: for a self-adjoint `A : E →ₗ.[ℂ] E` and `z` off the real
axis, `A - z` has a bounded two-sided inverse, with `‖(A - z)⁻¹‖ ≤ |Im z|⁻¹`.
Hence `spectrum A ⊆ ℝ`.

The argument is the classical one, in three steps:

1. **the estimate** `‖(A - z) x‖ ≥ |Im z| ‖x‖` — because `⟪A x, x⟫` is real, the
   cross term in `‖(A - Re z) x - i (Im z) x‖²` is purely imaginary and drops
   out, leaving `‖(A - Re z)x‖² + (Im z)² ‖x‖²`;
2. **closed range** — the estimate plus closedness of `A` (self-adjoint
   operators are closed) makes the range of `A - z` closed;
3. **dense range** — a vector orthogonal to the range is an eigenvector of `A`
   for the eigenvalue `conj z`, and self-adjointness forces its eigenvalues to
   be real, so it vanishes.

## Provenance

* **Extraction class:** *new*.  Statement and proof are ours.
* **Spectra influence:** Spectra proves the same criterion
  (`Spectra.YosidaHille.isSelfAdjoint_to_surjective`,
  `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`) and that is what told us
  the criterion was needed here; per
  `docs/planning/tauceti-adaptation-and-spectra-extraction.md`, theorem
  selection is attributable even when the proof is independent.  The proof below
  was written against Mathlib's `LinearPMap` adjoint API and shares no lemma with
  Spectra's, which routes through the Cayley transform and Yosida--Hille.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a symmetric operator the quadratic form is real. -/
theorem inner_apply_self_isReal {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (x : A.domain) : (starRingEnd ℂ) ⟪A x, (x : E)⟫_ℂ = ⟪A x, (x : E)⟫_ℂ := by
  rw [inner_conj_symm]
  exact (hsym x x).symm

/-- **The basic estimate.**  `‖(A - z) x‖ ≥ |Im z| ‖x‖` for symmetric `A`.

The cross term vanishes because `⟪A x - (Re z) x, x⟫` is real while the
subtracted vector is `i (Im z) x`. -/
theorem norm_sub_smul_ge_abs_im {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖ := by
  set u : E := A x - (z.re : ℂ) • (x : E) with hu
  have hsplit : A x - z • (x : E) = u - ((z.im : ℂ) * Complex.I) • (x : E) := by
    rw [hu]
    have : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
    rw [show z • (x : E) = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • (x : E) by rw [← this]]
    rw [add_smul]
    abel
  -- `⟪u, x⟫` is real
  have hreal : (starRingEnd ℂ) ⟪u, (x : E)⟫_ℂ = ⟪u, (x : E)⟫_ℂ := by
    rw [hu, inner_sub_left, inner_smul_left, map_sub, map_mul]
    rw [inner_apply_self_isReal hsym x]
    simp [Complex.conj_ofReal]
  -- the cross term is purely imaginary
  have hcross : RCLike.re ⟪u, (((z.im : ℂ) * Complex.I) • (x : E))⟫_ℂ = 0 := by
    have hr : (⟪u, (x : E)⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
    rw [inner_smul_right]
    simp [hr]
  have hsq : ‖A x - z • (x : E)‖ ^ 2
      = ‖u‖ ^ 2 + (z.im) ^ 2 * ‖(x : E)‖ ^ 2 := by
    rw [hsplit, @norm_sub_sq ℂ, hcross, norm_smul]
    simp [Complex.norm_I, Complex.norm_real, mul_pow, sq_abs]
  nlinarith [norm_nonneg (A x - z • (x : E)), norm_nonneg u, norm_nonneg ((x : E)),
    abs_nonneg z.im, sq_abs z.im, sq_nonneg ‖u‖, hsq,
    mul_nonneg (abs_nonneg z.im) (norm_nonneg ((x : E)))]

end LinearPMap
end TauCeti
