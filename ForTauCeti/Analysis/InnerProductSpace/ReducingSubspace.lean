/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Quantitative reduction for symmetric linear maps

A quantitative orthogonal-block estimate for symmetric linear maps on
inner-product spaces. Qualitative reducing-subspace theory and projected-subspace
completeness are consumed by their callers directly from Tau Ceti.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Projected-subspace completeness uses accepted
  `TauCeti.Analysis.InnerProductSpace.Projection.Completeness` directly. The
  native module acknowledges the same DKPS observation; its proof uses the
  closed range of an idempotent. Neither a local completeness theorem nor a
  forwarding instance remains. Callers needing instance search register the
  native theorem locally; the former `TauCeti.CompleteSubspace` scope is retired.
* The former bounded `ContinuousLinearMap.Reduces` predicate and qualitative
  reduction/projection-commutation proofs are retired. Consumers use native
  `Submodule.IsReducing`, invariant-submodule membership and commutation directly.
  The quantitative linear-map estimate below retains its incomplete-ambient
  scope; it is not identified with a bounded Hilbert-space specialization.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- **A symmetric map that nearly reduces `Z` moves `Zᗮ` only slightly into `Z`.**

If `‖T x - Z.starProjection (T x)‖ ≤ ρ ‖x‖` for every `x ∈ Z` -- the quantitative form of
"`T` reduces `Z`" -- then for `w ⊥ Z` the part of `T w` lying in `Z` is at most `ρ ‖w‖`.
Symmetry is what lets the estimate be read on either side of the inner product.

At `ρ = 0` this is the qualitative statement: a symmetric map reducing `Z` maps `Zᗮ` into
`Zᗮ`, the qualitative case of
`LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule`. -/
theorem norm_starProjection_apply_le_of_mem_orthogonal
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {Z : Submodule 𝕜 E} [Z.HasOrthogonalProjection] {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hrho : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ rho * ‖x‖)
    {w : E} (hw : w ∈ Zᗮ) : ‖Z.starProjection (T w)‖ ≤ rho * ‖w‖ := by
  set z := Z.starProjection (T w) with hz
  have hzZ : z ∈ Z := Z.starProjection_apply_mem _
  have hsq : ‖z‖ ^ 2 ≤ rho * ‖w‖ * ‖z‖ := by
    have h0 : ⟪z, z⟫_𝕜 = ⟪T w, z⟫_𝕜 := by
      conv_lhs => rw [hz]
      rw [Z.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hzZ]
    have h1 : ⟪T w, z⟫_𝕜 = ⟪w, T z - Z.starProjection (T z)⟫_𝕜 := by
      rw [hT w z, inner_sub_right,
        Submodule.inner_left_of_mem_orthogonal
          (Z.starProjection_apply_mem (T z)) hw, sub_zero]
    calc ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_𝕜 := (inner_self_eq_norm_sq z).symm
      _ = RCLike.re ⟪w, T z - Z.starProjection (T z)⟫_𝕜 := by rw [h0, h1]
      _ ≤ ‖⟪w, T z - Z.starProjection (T z)⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖w‖ * ‖T z - Z.starProjection (T z)‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (rho * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hrho z hzZ) (norm_nonneg w)
      _ = rho * ‖w‖ * ‖z‖ := by ac_rfl
  rcases eq_or_ne ‖z‖ 0 with h0 | h0
  · rw [h0]
    exact mul_nonneg hrho0 (norm_nonneg w)
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hsq) hzpos

end LinearMap
