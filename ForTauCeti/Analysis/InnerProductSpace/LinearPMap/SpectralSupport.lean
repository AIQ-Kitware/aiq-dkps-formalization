/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# The spectral measure is supported in the spectrum

A self-adjoint operator's spectral measure gives no mass to Borel sets that miss
its spectrum.  This is Spectra-removal lane **SR-B**
(`dev/tauceti/spectra-removal-parallel-lanes.md`), replacing the donor constant
`spectralPVM_proj_eq_zero_of_subset_resolventSet`.

## The argument

Everything is local.  If `B` sits inside a small interval around a resolvent
point `lam`, then on `B` the symbol `s - lam` is bounded by the interval radius,
so `SpectralMeasure`'s
`specProjection_apply_sub_smul` gives

```
‖(A - lam) E(B) y‖ ≤ r ‖y‖
```

while `lam ∈ resolventSet A` supplies a bounded `R` inverting `A - lam`.  Hence
`‖E(B) y‖ = ‖R (A - lam) E(B) y‖ ≤ ‖R‖ r ‖y‖`, so `‖E(B)‖ ≤ ‖R‖ r`.  Choosing
`r < ‖R‖⁻¹` forces `‖E(B)‖ < 1`, and a projection of norm `< 1` is zero.

The last step is `ContinuousLinearMap.eq_zero_of_isIdempotentElem_of_opNorm_lt_one`
below: idempotence alone gives it, with no self-adjointness needed.

## Provenance

* Replaces `Spectra/SpectralTheory/…`'s `spectralPVM_proj_eq_zero_of_subset_resolventSet`.
  Proved natively against `TauCeti`'s own `specProjection` rather than relocated,
  because the donor's proof runs through `borelMeasure` and the Born-rule support
  estimate — 44 Spectra files — none of which `ForTauCeti` may import.
* Spectra influence: none.  This module depends only on Mathlib and
  `ForTauCeti`.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- An idempotent bounded operator of norm `< 1` is zero.

No self-adjointness is needed: idempotence gives `‖Px‖ = ‖P(Px)‖ ≤ ‖P‖ ‖Px‖`,
and `‖P‖ < 1` then forces `‖Px‖ = 0`. -/
theorem _root_.ContinuousLinearMap.eq_zero_of_isIdempotentElem_of_opNorm_lt_one
    {P : H →L[ℂ] H} (hP : IsIdempotentElem P) (hlt : ‖P‖ < 1) : P = 0 := by
  ext x
  have hidem : P (P x) = P x := by
    have := congrArg (fun T : H →L[ℂ] H => T x) hP
    simpa [_root_.mul_apply_eq_comp] using this
  have hle : ‖P x‖ ≤ ‖P‖ * ‖P x‖ := by
    calc ‖P x‖ = ‖P (P x)‖ := by rw [hidem]
      _ ≤ ‖P‖ * ‖P x‖ := P.le_opNorm _
  have hzero : ‖P x‖ ≤ 0 := by nlinarith [norm_nonneg (P x)]
  simpa using le_antisymm hzero (norm_nonneg _)

section Support

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
variable (B : Set ℝ) (hB : MeasurableSet B)

/-- **The spectral projection of a small set around a resolvent point vanishes.**

If `lam` is real and in the resolvent set, and `B` stays within `r` of `lam`
with `r` smaller than the reciprocal of the resolvent's norm, then `E_A(B) = 0`.

This is the local half of SR-B; the global statement follows by covering. -/
theorem specProjection_eq_zero_of_dist_lt
    {M lam r : ℝ} {R : H →L[ℂ] H}
    (hbnd : ∀ s ∈ B, |s| ≤ M) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - lam| ≤ r)
    (hR : ∀ ψ : A.domain, R (A ψ - (lam : ℂ) • (ψ : H)) = (ψ : H))
    (hlt : ‖R‖ * r < 1) :
    specProjection hA B hB = 0 := by
  -- `E(B) y` lies in `dom A`, and `R` inverts `A - lam` there, so
  -- `E(B) y = R ((A - lam) E(B) y)` is bounded by `‖R‖ · r · ‖y‖`.
  have hkey : ∀ y : H, ‖specProjection hA B hB y‖ ≤ ‖R‖ * r * ‖y‖ := by
    intro y
    obtain ⟨hy, hEq⟩ := specProjection_apply_sub_smul hA B hB hbnd hr hcr y
    have hinv : R (A ⟨specProjection hA B hB y, hy⟩ -
        (lam : ℂ) • specProjection hA B hB y) = specProjection hA B hB y :=
      hR ⟨specProjection hA B hB y, hy⟩
    rw [hEq] at hinv
    have hbound :
        ‖BorelCalculus.borelCalculus (isStarNormal_cayley hA)
            (isBddMeasurable_truncSymbol hA B hB hr hcr) y‖ ≤ r * ‖y‖ :=
      BorelCalculus.norm_borelCalculus_apply_le _ _ hr
        (norm_truncSymbol_le hA B hr hcr) y
    calc ‖specProjection hA B hB y‖
        = ‖R (BorelCalculus.borelCalculus (isStarNormal_cayley hA)
            (isBddMeasurable_truncSymbol hA B hB hr hcr) y)‖ := by rw [hinv]
      _ ≤ ‖R‖ * ‖BorelCalculus.borelCalculus (isStarNormal_cayley hA)
            (isBddMeasurable_truncSymbol hA B hB hr hcr) y‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (r * ‖y‖) :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ = ‖R‖ * r * ‖y‖ := by ring
  have hop : ‖specProjection hA B hB‖ ≤ ‖R‖ * r :=
    ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg _) hr) hkey
  exact ContinuousLinearMap.eq_zero_of_isIdempotentElem_of_opNorm_lt_one
    (isIdempotentElem_specProjection hA B hB) (lt_of_le_of_lt hop hlt)

end Support

end LinearPMap
end TauCeti
