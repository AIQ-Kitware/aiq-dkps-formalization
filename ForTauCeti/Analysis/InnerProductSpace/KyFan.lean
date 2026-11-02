/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Historical source: `ForMathlib.Analysis.InnerProductSpace.KyFan`, introduced at
Davis--Kahan commit 199390a; Formalized by Claude Fable 5 (claude-fable-5[1m]).
The Ky Fan definition and variational engine are now consumed from Tau Ceti.
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.ZeroExtension
public import ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix


/-! # Additional finite-dimensional Ky Fan consequences

The maintained API uses `LinearMap.kyFanSum` directly. This donor retains the
sorted-modulus eigenvalue identity, a filtered-index sum conversion, unimodular
rescaling of orthonormal families and the absolute-real-part witness inequality.
The last result rephases the witnesses before applying the accepted native
orthonormal trace bound; it is used by the branch-free double-angle theorem.

The native variational principle, homogeneity, saturation and seminorm interface
replace the former local definition and its conversion/scaling/witness wrappers.
See `dev/tauceti/dkps-upstream-contribution-census.md` for exact retirement provenance.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### Singular values under absolute homogeneity and bounded factors

The composition, scalar-homogeneity, and left-factor comparison facts are provided by
Mathlib's `LinearMap.singularValues_*` API. -/

/-- The sorted eigenvalues of the modulus `|A|` are the singular values. -/
theorem eigenvalues_operatorAbs (A : E →ₗ[𝕜] E) :
    (A.isPositive_operatorAbs).isSymmetric.eigenvalues rfl
      = fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ) := by
  refine LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ rfl
    (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
    (fun i j hij => A.singularValues_antitone (by exact_mod_cast hij))
    fun i => ?_
  rw [show A.operatorAbs = (LinearMap.isPositive_adjoint_comp_self A).sqrt from
      (LinearMap.isPositive_adjoint_comp_self A).sqrt_unique
        A.isPositive_operatorAbs A.operatorAbs_sq,
    (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis rfl i,
    A.singularValues_fin rfl i]

/-! ### The Ky Fan variational principle (F1.c) -/

/-- Index plumbing: a top-`k` filtered sum over `Fin n` is a sum over `Fin k`.
(Not `private`: `UnitarilyInvariantSeminorm.lean` consumes it to convert `LinearMap.kyFanSum`
domination into the prefix-sum hypothesis of the T-transform descent.) -/
theorem sum_filter_lt_eq_sum_fin {n k : ℕ} (hk : k ≤ n) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f (j : ℕ)
      = ∑ i : Fin k, f (i : ℕ) := by
  rw [show (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f (j : ℕ))
      = ∑ j : Fin n, if (j : ℕ) < k then f (j : ℕ) else 0 from Finset.sum_filter _ _,
    Fin.sum_univ_eq_sum_range (fun m => if m < k then f m else 0) n,
    Fin.sum_univ_eq_sum_range (fun m => f m) k, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-! ### Ky Fan sums and weak majorization (F2)

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.KyFan`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `199390a`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

omit [FiniteDimensional 𝕜 F] in
/-- Rescaling an orthonormal family by unimodular scalars leaves it
orthonormal. -/
theorem orthonormal_unimodular_smul {ι : Type*} {u : ι → F}
    (hu : Orthonormal 𝕜 u) {c : ι → 𝕜} (hc : ∀ i, ‖c i‖ = 1) :
    Orthonormal 𝕜 fun i => c i • u i := by
  classical
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  rw [inner_smul_left, inner_smul_right, hu i j]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, mul_one, RCLike.conj_mul, hc i]
    norm_num
  · rw [ite_eq_right h, mul_zero, mul_zero]

/-- **Absolute-value witness form of the rectangular Ky Fan upper bound.**
Rephasing one orthonormal family by signs makes the Ky Fan prefix dominate
the sum of the absolute real parts of the matched coefficients. This is needed
when the geometry dictates each coefficient's sign. -/
theorem sum_abs_le_kyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (_hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ |RCLike.re ⟪u i, A (v i)⟫_𝕜|) :
    ∑ i, t i ≤ A.kyFanSum k := by
  classical
  set ε : Fin k → 𝕜 := fun i =>
    if 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 then 1 else -1 with hε
  have hεnorm : ∀ i, ‖ε i‖ = 1 := by
    intro i
    rw [hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 <;> simp [h]
  have hnorm := A.norm_sum_inner_le_kyFanSum
    (orthonormal_unimodular_smul hu hεnorm) hv
  simp only [Fintype.card_fin] at hnorm
  have hreal := (RCLike.re_le_norm _).trans hnorm
  rw [map_sum] at hreal
  refine (Finset.sum_le_sum fun i _ => ?_).trans hreal
  have hval : RCLike.re ⟪ε i • u i, A (v i)⟫_𝕜 =
      |RCLike.re ⟪u i, A (v i)⟫_𝕜| := by
    rw [inner_smul_left, hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  rw [hval]
  exact ht i



end TauCeti
