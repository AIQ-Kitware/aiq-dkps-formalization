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

/-- **Ky Fan variational principle, upper bound:** for orthonormal families
`u, v : Fin k → E` and any `A : E →ₗ[𝕜] E`,
`re ∑ᵢ ⟪uᵢ, A vᵢ⟫ ≤ ∑_{i<k} σᵢ(A)`. -/
private theorem re_sum_inner_map_le_sum_singularValues_square {A : E →ₗ[𝕜] E} {k : ℕ}
    (hk : k ≤ finrank 𝕜 E) {u v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := by
  set W := choosePolarUnitary A with hW
  set R := (isPositive_operatorAbs A).sqrt with hR
  have hRsymm : R.IsSymmetric := (isPositive_operatorAbs A).sqrt_isPositive.isSymmetric
  have hRR : R ∘ₗ R = operatorAbs A := (isPositive_operatorAbs A).sqrt_sq
  -- Pull the polar unitary across and split `|A|` symmetrically.
  have hterm : ∀ i, ⟪u i, A (v i)⟫_𝕜 = ⟪R (W.symm (u i)), R (v i)⟫_𝕜 := by
    intro i
    have h1 : A (v i) = W (operatorAbs A (v i)) := by
      have h := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary A) (v i)
      rw [LinearMap.comp_apply] at h
      exact h.trans rfl
    calc ⟪u i, A (v i)⟫_𝕜 = ⟪W (W.symm (u i)), W (operatorAbs A (v i))⟫_𝕜 := by
          rw [W.apply_symm_apply, ← h1]
      _ = ⟪W.symm (u i), operatorAbs A (v i)⟫_𝕜 := W.inner_map_map _ _
      _ = ⟪W.symm (u i), R (R (v i))⟫_𝕜 := by
          rw [← hRR]; rfl
      _ = ⟪R (W.symm (u i)), R (v i)⟫_𝕜 := (hRsymm (W.symm (u i)) (R (v i))).symm
  have hquad : ∀ x : E, ‖R x‖ ^ 2 = RCLike.re ⟪operatorAbs A x, x⟫_𝕜 := fun x =>
    (isPositive_operatorAbs A).norm_sqrt_apply_sq x
  have hterm_le : ∀ i, RCLike.re ⟪u i, A (v i)⟫_𝕜
      ≤ RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜 / 2
        + RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜 / 2 := by
    intro i
    rw [hterm i, ← hquad, ← hquad]
    have h1 : RCLike.re ⟪R (W.symm (u i)), R (v i)⟫_𝕜 ≤ ‖R (W.symm (u i))‖ * ‖R (v i)‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    nlinarith [sq_nonneg (‖R (W.symm (u i))‖ - ‖R (v i)‖)]
  have hu' : Orthonormal 𝕜 (fun i => W.symm (u i)) := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    rw [W.symm.inner_map_map]
    exact hu i j
  have htr1 := LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues
    (isPositive_operatorAbs A).isSymmetric rfl hu'
  have htr2 := LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues
    (isPositive_operatorAbs A).isSymmetric rfl hv
  rw [eigenvalues_operatorAbs A] at htr1 htr2
  have htr1' : (∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < k),
        A.singularValues (j : ℕ) := by
    simpa only [Fintype.card_fin] using htr1
  have htr2' : (∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < k),
        A.singularValues (j : ℕ) := by
    simpa only [Fintype.card_fin] using htr2
  rw [sum_filter_lt_eq_sum_fin hk (fun j => A.singularValues j)] at htr1' htr2'
  calc RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜)
      = ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 := map_sum _ _ _
    _ ≤ ∑ i, (RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜 / 2
          + RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜 / 2) :=
        Finset.sum_le_sum fun i _ => hterm_le i
    _ = (∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜) / 2
        + (∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜) / 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    _ ≤ (∑ i : Fin k, A.singularValues (i : ℕ)) / 2
        + (∑ i : Fin k, A.singularValues (i : ℕ)) / 2 := by
        have h1 : ∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜
            ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := htr1'
        have h2 : ∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜
            ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := htr2'
        linarith
    _ = ∑ i : Fin k, A.singularValues (i : ℕ) := by ring

/-- **Ky Fan variational principle, achievability:** the top-`k` singular-value
sum is attained at the singular pairs. -/
private theorem exists_orthonormal_re_sum_inner_map_eq_square (A : E →ₗ[𝕜] E) {k : ℕ}
    (hk : k ≤ finrank 𝕜 E) :
    ∃ u v : Fin k → E, Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) = ∑ i : Fin k, A.singularValues (i : ℕ) := by
  set b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hb
  set v : Fin k → E := fun i => b (Fin.castLE hk i) with hv
  have hvon : Orthonormal 𝕜 v := b.orthonormal.comp _ (Fin.castLE_injective hk)
  set u : Fin k → E := fun i => choosePolarUnitary A (v i) with hu
  have huon : Orthonormal 𝕜 u := by
    rw [orthonormal_iff_ite] at hvon ⊢
    intro i j
    rw [hu]
    simp only
    rw [(choosePolarUnitary A).inner_map_map]
    exact hvon i j
  refine ⟨u, v, huon, hvon, ?_⟩
  have hterm : ∀ i, ⟪u i, A (v i)⟫_𝕜 = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) := by
    intro i
    have h1 : A (v i) = choosePolarUnitary A (operatorAbs A (v i)) := by
      have h := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary A) (v i)
      rw [LinearMap.comp_apply] at h
      exact h.trans rfl
    have h2 : operatorAbs A (v i) = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) • v i := by
      rw [hv]
      simp only
      rw [show operatorAbs A = (LinearMap.isPositive_adjoint_comp_self A).sqrt from rfl,
        (LinearMap.isPositive_adjoint_comp_self A).sqrt_apply_eigenvectorBasis rfl
          (Fin.castLE hk i),
        ← A.singularValues_fin rfl (Fin.castLE hk i)]
      rfl
    rw [hu]
    simp only
    rw [h1, (choosePolarUnitary A).inner_map_map, h2, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hvon.1 i]
    simp
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [show (∑ i : Fin k, ((A.singularValues (i : ℕ) : ℝ) : 𝕜))
      = ((∑ i : Fin k, A.singularValues (i : ℕ) : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.ofReal_re]

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

/-- Ky Fan sums are nonnegative, being sums of singular values. -/
theorem kyFanSum_nonneg (k : ℕ) (A : E →ₗ[𝕜] F) : 0 ≤ kyFanSum k A :=
  Finset.sum_nonneg fun i _ => A.singularValues_nonneg i

/-- Ky Fan sums saturate at `k = finrank`: larger `k` adds only zeros. -/
theorem kyFanSum_eq_of_finrank_le {k : ℕ} (hk : finrank 𝕜 E ≤ k) (A : E →ₗ[𝕜] F) :
    kyFanSum k A = kyFanSum (finrank 𝕜 E) A := by
  rw [kyFanSum_eq_sum_range, kyFanSum_eq_sum_range]
  refine (Finset.sum_subset (fun i hi => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)) fun i _ hi => ?_).symm
  exact A.singularValues_of_finrank_le (by simpa using hi)

/-- **Weak majorization / the simultaneous Ky Fan triangle inequality:**
`kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B` for every `k` — i.e.
`σ(A + B) ≺_w σ(A) + σ(B)`.  From the variational principle: the maximizing
pair for `A + B` tests both `A` and `B`. -/
private theorem kyFanSum_add_le_aux {k : ℕ} (hk : k ≤ finrank 𝕜 E) (A B : E →ₗ[𝕜] E) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  obtain ⟨u, v, hu, hv, heq⟩ := exists_orthonormal_re_sum_inner_map_eq_square (A + B) hk
  have hsplit : RCLike.re (∑ i, ⟪u i, (A + B) (v i)⟫_𝕜)
      = RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) + RCLike.re (∑ i, ⟪u i, B (v i)⟫_𝕜) := by
    rw [← map_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.add_apply, inner_add_right]
  rw [kyFanSum_eq_sum_fin, ← heq, hsplit, kyFanSum_eq_sum_fin, kyFanSum_eq_sum_fin]
  exact add_le_add (re_sum_inner_map_le_sum_singularValues_square hk hu hv)
    (re_sum_inner_map_le_sum_singularValues_square hk hu hv)

/-- Square variational proof, used internally for the rectangular theorem. -/
private theorem kyFanSum_add_le_square (k : ℕ) (A B : E →ₗ[𝕜] E) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  rcases le_or_gt k (finrank 𝕜 E) with hk | hk
  · exact kyFanSum_add_le_aux hk A B
  · rw [kyFanSum_eq_of_finrank_le hk.le, kyFanSum_eq_of_finrank_le hk.le A,
      kyFanSum_eq_of_finrank_le hk.le B]
    exact kyFanSum_add_le_aux le_rfl A B


/-- The Ky Fan triangle inequality for arbitrary rectangular maps and every prefix length. -/
theorem kyFanSum_add_le (k : ℕ) (A B : E →ₗ[𝕜] F) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := by
  have h := kyFanSum_add_le_square k (LinearMap.zeroExtension A) (LinearMap.zeroExtension B)
  have hext : LinearMap.zeroExtension (A + B) =
      LinearMap.zeroExtension A + LinearMap.zeroExtension B := by
    ext z
    simp only [LinearMap.zeroExtension_apply, LinearMap.add_apply]
    rw [← WithLp.toLp_add]
    exact congrArg (WithLp.toLp 2) (by ext <;> simp)
  simpa only [← hext, kyFanSum, LinearMap.singularValues_zeroExtension] using h


/-- Pointwise singular-value domination gives Ky Fan domination. -/
theorem kyFanSum_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) (k : ℕ) :
    kyFanSum k A ≤ kyFanSum k B :=
  Finset.sum_le_sum fun i _ => h i

/-- Ky Fan sums are adjoint-invariant, since the singular values are. -/
theorem kyFanSum_adjoint (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFanSum k A.adjoint = kyFanSum k A := by
  unfold kyFanSum
  rw [LinearMap.singularValues_adjoint]

/-- Ky Fan sums are unchanged by a unitary on the codomain. -/
theorem kyFanSum_unitary_comp (k : ℕ) (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    kyFanSum k (U.toLinearMap ∘ₗ A) = kyFanSum k A := by
  unfold kyFanSum
  exact congrArg (fun s : ℕ →₀ ℝ => ∑ i : Fin k, s (i : ℕ))
    (LinearMap.singularValues_linearIsometryEquiv_comp U A)

/-- Ky Fan sums are unchanged by a unitary on the domain.  With `kyFanSum_unitary_comp` this is
the two-sided unitary invariance that makes each Ky Fan sum a unitarily invariant norm. -/
theorem kyFanSum_comp_unitary (k : ℕ) (A : E →ₗ[𝕜] F) (U : E ≃ₗᵢ[𝕜] E) :
    kyFanSum k (A ∘ₗ U.toLinearMap) = kyFanSum k A := by
  unfold kyFanSum
  exact congrArg (fun s : ℕ →₀ ℝ => ∑ i : Fin k, s (i : ℕ))
    (LinearMap.singularValues_comp_linearIsometryEquiv A U)

/-- Ky Fan sums are absolutely homogeneous under real scaling. -/
theorem kyFanSum_real_smul (k : ℕ) (A : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) :
    kyFanSum k (((r : 𝕜)) • A) = r * kyFanSum k A := by
  unfold kyFanSum
  rw [Finset.mul_sum]
  simp [LinearMap.singularValues_smul, abs_of_nonneg hr, Finsupp.smul_apply, smul_eq_mul]

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
