/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`KyFan.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).

Ky Fan partial sums of singular values: the trace inequality
`∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{top k} λᵢ(S)` for an orthonormal `k`-family (via a
fractional-knapsack lemma), the Ky Fan variational principle
`∑_{i<k} σᵢ(A) = max re ∑ᵢ ⟪uᵢ, A vᵢ⟫` (via the polar decomposition and the
positive square root), and its consequence, the simultaneous triangle
inequality for all Ky Fan norms — weak majorization
`σ(A + B) ≺_w σ(A) + σ(B)`.
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


/-! # Ky Fan sums of singular values

For operators on finite-dimensional inner product spaces over `𝕜 = ℝ, ℂ`:

* `kyFanSum k A = ∑_{i<k} σᵢ(A)`, the Ky Fan `k`-sums;
* the **Ky Fan trace inequality**: for a symmetric `S` and an orthonormal
  family `w : Fin k → E`, `∑ᵢ re⟪S wᵢ, wᵢ⟫ ≤ ∑_{i<k} λᵢ(S)`;
* the **Ky Fan variational principle**: `kyFanSum k A` is the maximum of
  `re ∑ᵢ ⟪uᵢ, A vᵢ⟫` over orthonormal `k`-families `u, v`;
* **weak majorization** `kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B` —
  the triangle inequality for every Ky Fan norm simultaneously, the engine of
  the Fan dominance principle (`UnitarilyInvariantSeminorm.lean`);
* unitary invariance, adjoint invariance, and nonnegative-real scaling of
  singular values and Ky Fan sums, plus the bounded-factor domination
  `σᵢ(C ∘ A) ≤ c σᵢ(A)` (Loewner monotonicity of the Gram eigenvalues).

## References

* R. Bhatia, *Matrix Analysis*, Chapter IV (Ky Fan norms, dominance).
* K. Fan, *On a theorem of Weyl concerning eigenvalues of linear
  transformations I*, Proc. Nat. Acad. Sci. USA 35 (1949), 652–655.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

/-! ### Singular values under absolute homogeneity and bounded factors

The composition, scalar-homogeneity, and left-factor comparison facts are provided by
Mathlib's `LinearMap.singularValues_*` API. -/

/-- The sorted eigenvalues of the modulus `|A|` are the singular values. -/
theorem eigenvalues_operatorAbs (A : E →ₗ[𝕜] E) :
    (isPositive_operatorAbs A).isSymmetric.eigenvalues rfl
      = fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ) := by
  refine LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis _ rfl
    (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
    (fun i j hij => A.singularValues_antitone (by exact_mod_cast hij))
    fun i => ?_
  rw [show operatorAbs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
    (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis rfl i,
    A.singularValues_fin rfl i]

/-! ### The Ky Fan variational principle (F1.c) -/

/-- Index plumbing: a top-`k` filtered sum over `Fin n` is a sum over `Fin k`.
(Not `private`: `UnitarilyInvariantSeminorm.lean` consumes it to convert `kyFanSum`
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

/-- **The Ky Fan `k`-sum** of an operator: the sum of its `k` largest singular
values.  `kyFanSum 1 A = ‖A‖`, `kyFanSum (finrank 𝕜 E) A` is the trace norm.

`@[expose]`: the defining sum is the working form throughout the Ky Fan and
unitarily-invariant-norm development, so the body must stay visible to the
kernel for the `rfl`-level rewrites below. -/
@[expose]
noncomputable def kyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)

/-- The Ky Fan sum as a finite singular-value vector sum. -/
theorem kyFanSum_eq_sum_fin (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = ∑ i : Fin k, A.singularValues (i : ℕ) :=
  rfl

/-- The Ky Fan sum as the sum over the natural-number prefix `[0, k)`. -/
theorem kyFanSum_eq_sum_range (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = ∑ i ∈ Finset.range k, A.singularValues i :=
  Fin.sum_univ_eq_sum_range (fun i => A.singularValues i) k

/-- The local finite-prefix presentation agrees with Tau Ceti's canonical Ky Fan sum. -/
theorem kyFanSum_eq_linearMap_kyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = A.kyFanSum k := by
  rw [kyFanSum_eq_sum_range, LinearMap.kyFanSum_def]

/-- The finite-prefix presentation is the canonical Tau Ceti Ky Fan seminorm. -/
theorem kyFanSum_eq_kyFan (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = UnitarilyInvariantSeminorm.kyFan 𝕜 E F k A := by
  rw [kyFanSum_eq_linearMap_kyFanSum, ← UnitarilyInvariantSeminorm.kyFan_apply]

/-- Ky Fan sums saturate at `k = finrank`: larger `k` adds only zeros. -/
theorem kyFanSum_eq_of_finrank_le {k : ℕ} (hk : finrank 𝕜 E ≤ k) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = kyFanSum (finrank 𝕜 E) A := by
  rw [kyFanSum_eq_sum_range, kyFanSum_eq_sum_range]
  refine (Finset.sum_subset (fun i hi => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)) fun i _ hi => ?_).symm
  exact A.singularValues_of_finrank_le (by simpa using hi)

/-- Pointwise singular-value domination gives Ky Fan domination. -/
theorem kyFanSum_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) (k : ℕ) :
    kyFanSum k A ≤ kyFanSum k B :=
  Finset.sum_le_sum fun i _ => h i

/-- Ky Fan sums are absolutely homogeneous under real scaling. -/
theorem kyFanSum_real_smul (k : ℕ) (A : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) :
    kyFanSum k (((r : 𝕜)) • A) = r * kyFanSum k A := by
  rw [kyFanSum_eq_linearMap_kyFanSum k (((r : 𝕜)) • A),
    kyFanSum_eq_linearMap_kyFanSum k A, LinearMap.kyFanSum_smul,
    RCLike.norm_of_nonneg hr]

/-- A convenient witness form of the rectangular Ky Fan upper bound. -/
theorem sum_le_kyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (_hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜) :
    ∑ i, t i ≤ kyFanSum k A := by
  calc
    ∑ i, t i ≤ ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 :=
      Finset.sum_le_sum fun i _ => ht i
    _ = RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) := by
      rw [map_sum]
    _ ≤ ‖∑ i, ⟪u i, A (v i)⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ A.kyFanSum k := by simpa using A.norm_sum_inner_le_kyFanSum hu hv
    _ = kyFanSum k A := (kyFanSum_eq_linearMap_kyFanSum k A).symm

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
Because the two orthonormal families may be rephased independently, the Ky Fan
prefix dominates the sum of the *magnitudes* of the matched coefficients, not
merely their signed real parts.  This is the form needed whenever the sign of
each matched coefficient is dictated by the geometry rather than chosen. -/
theorem sum_abs_le_kyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ |RCLike.re ⟪u i, A (v i)⟫_𝕜|) :
    ∑ i, t i ≤ kyFanSum k A := by
  classical
  set ε : Fin k → 𝕜 := fun i =>
    if 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 then 1 else -1 with hε
  have hεnorm : ∀ i, ‖ε i‖ = 1 := by
    intro i
    rw [hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜 <;> simp [h]
  refine sum_le_kyFanSum_of_orthonormal hk
    (orthonormal_unimodular_smul hu hεnorm) hv (t := t) fun i => ?_
  have hval : RCLike.re ⟪ε i • u i, A (v i)⟫_𝕜 =
      |RCLike.re ⟪u i, A (v i)⟫_𝕜| := by
    rw [inner_smul_left, hε]
    by_cases h : 0 ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  rw [hval]
  exact ht i



end TauCeti
