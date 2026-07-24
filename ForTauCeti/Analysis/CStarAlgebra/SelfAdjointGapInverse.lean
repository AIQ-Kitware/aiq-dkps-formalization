/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Norm and inverse bounds from self-adjoint spectral position

For a self-adjoint element of a unital C*-algebra:

* `TauCeti.IsSelfAdjoint.norm_le_of_spectrum_subset_Icc`: if the real
  spectrum lies in `[-r, r]` then `‖a‖ ≤ r`;
* `TauCeti.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap`: if the
  real spectrum avoids the open interval `(-r, r)` then `a` has a two-sided
  inverse of norm at most `r⁻¹`.

Both are direct applications of the isometric continuous functional calculus.
They are the analytic inputs to the constant-one interval/exterior Sylvester
estimate for the Davis--Kahan `sin Θ` theorem (shift-and-invert argument).

Proposed Mathlib destination:
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `ForMathlib.IsSelfAdjoint.norm_le_of_spectrum_subset_Icc`,
  `ForMathlib.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap`
  (namespace renamed here `ForMathlib` → `TauCeti`).
* Original authors / copyright: Jon Crall, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
* Spectra influence: **none** (imports only Mathlib).
-/

@[expose] public section

namespace TauCeti

variable {A : Type*} [CStarAlgebra A]

/-- A self-adjoint element whose real spectrum lies in `[-r, r]` has norm at
most `r`. -/
theorem IsSelfAdjoint.norm_le_of_spectrum_subset_Icc {a : A}
    (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h : spectrum ℝ a ⊆ Set.Icc (-r) r) : ‖a‖ ≤ r := by
  rw [← cfc_id ℝ a]
  refine norm_cfc_le hr fun x hx => ?_
  have hmem := h hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hmem.1, hmem.2⟩

/-- A self-adjoint element whose real spectrum avoids the open interval
`(-r, r)` has a two-sided inverse of norm at most `r⁻¹`. -/
theorem IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap {a : A}
    (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ spectrum ℝ a, r ≤ |x|) :
    ∃ j : A, j * a = 1 ∧ a * j = 1 ∧ ‖j‖ ≤ r⁻¹ := by
  have hne : ∀ x ∈ spectrum ℝ a, x ≠ 0 := by
    intro x hx hx0
    have hrx := h x hx
    rw [hx0, abs_zero] at hrx
    linarith
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ a) :=
    continuousOn_inv₀.mono fun x hx =>
      Set.mem_compl_singleton_iff.mpr (hne x hx)
  have hid : ContinuousOn (fun x : ℝ => x) (spectrum ℝ a) := by fun_prop
  refine ⟨cfc (fun x : ℝ => x⁻¹) a, ?_, ?_, ?_⟩
  · have hmul : cfc (fun x : ℝ => x⁻¹) a * cfc (fun x : ℝ => x) a =
        cfc (fun x : ℝ => x⁻¹ * x) a :=
      (cfc_mul _ _ a hcont hid).symm
    rw [cfc_id' ℝ a] at hmul
    rw [hmul,
      cfc_congr (g := fun _ : ℝ => (1 : ℝ))
        (fun x hx => inv_mul_cancel₀ (hne x hx)),
      cfc_const_one ℝ a]
  · have hmul : cfc (fun x : ℝ => x) a * cfc (fun x : ℝ => x⁻¹) a =
        cfc (fun x : ℝ => x * x⁻¹) a :=
      (cfc_mul _ _ a hid hcont).symm
    rw [cfc_id' ℝ a] at hmul
    rw [hmul,
      cfc_congr (g := fun _ : ℝ => (1 : ℝ))
        (fun x hx => mul_inv_cancel₀ (hne x hx)),
      cfc_const_one ℝ a]
  · refine norm_cfc_le (by positivity) fun x hx => ?_
    rw [Real.norm_eq_abs, abs_inv]
    exact inv_anti₀ hr (h x hx)

end TauCeti
