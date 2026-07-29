/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, Claude Opus 5

Staged for Mathlib: a proposed new file `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); golf pass by Claude Opus 4.8
(claude-opus-4-8[1m]); redesigned around the polar factorization by Claude Opus 5
(claude-opus-5[1m]) per the `mathlib-quality` rules.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/
module

public import ForTauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # A near-isometry is close to a genuine isometry (via the polar factorization)

A linear map `M` on a finite-dimensional real inner product space whose quadratic form
`x ↦ ⟪M x, M x⟫` is uniformly `δ`-close to `x ↦ ⟪x, x⟫` (with `δ < 1`) factors as `M = W ∘ S`
with `W` a linear isometry equivalence and `S` a square root of the Gram operator `Mᵀ ∘ M`
that moves no vector by more than `δ`.  In particular `M` lies within `δ` of the genuine
isometry `W`: `‖M x - W x‖ ≤ δ * ‖x‖`.

The factorization is the *polar decomposition* `M = W |M|`: `S = (Mᵀ M)^(1/2)` is built
directly from the orthonormal eigenbasis of the Gram operator
(`LinearMap.IsSymmetric.eigenvectorBasis`), and `W = M ∘ S⁻¹`.  So the proof uses neither the
continuous functional calculus nor a singular value decomposition — which is the point of
having a real, finite-dimensional development at all, since Mathlib registers the continuous
functional calculus on Hilbert-space operators only over `ℂ`.

Exposing the factorization, rather than only the estimate, is what makes the constant sharp.
Because `W` is an isometry and `M x = W (S x)`,

  `‖M x - W x‖ = ‖W (S x) - W x‖ = ‖S x - x‖`,

so the operator estimate *is* the scalar estimate `|√μ - 1| ≤ |μ - 1| ≤ δ` on the eigenvalues
`μ` of the Gram operator (`TauCeti.Real.abs_sqrt_sub_one_le_abs_sub_one`), with no loss.
Estimating instead through `M ∘ (1 - S⁻¹)` — the route that gives the constant `2 * δ` — pays
an avoidable `‖M‖ ≤ √(1 + δ)` factor and needs `δ ≤ 1 / 2`.

## Main results

* `TauCeti.LinearMap.exists_linearIsometryEquiv_comp_polarFactor`: the polar factorization
  `M = W ∘ S` with `S ∘ S = Mᵀ ∘ M`, `S` symmetric, and `‖S x - x‖ ≤ δ * ‖x‖`.  This is the
  primary statement; the estimates below are corollaries of it.
* `TauCeti.LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le` and
  `TauCeti.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_apply_le`: the sharp
  near-isometry estimate `‖M x - W x‖ ≤ δ * ‖x‖`, under the pointwise quadratic-form
  hypothesis and the operator-norm hypothesis `‖Mᵀ M - 1‖ ≤ δ` respectively.
* `TauCeti.LinearMap.exists_linearIsometryEquiv_norm_sub_le` and
  `TauCeti.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`: the historical
  statements, with the weaker constant `2 * δ` under `δ ≤ 1 / 2`.  Retained because they are
  the form quoted by the downstream paper development and by the challenge comparator; both
  are now one-line corollaries.

## Design note: why an existential here and a definition over `ℂ`

`ForTauCeti/Analysis/InnerProductSpace/PolarIsometry.lean` defines the polar isometry
*canonically*, as `ContinuousLinearMap.polarIsometryOfIsUnitModulus M = M ∘L Ring.inverse |M|`,
for arbitrary complex Hilbert spaces and with the same sharp constant; that is the general
theorem and the
canonical object.  It cannot be stated over `ℝ` because it needs the operator square root
`|M| = (M⋆ M)^(1/2)`, which Mathlib provides only through the continuous functional calculus,
i.e. only over `ℂ`.  Rather than leave the real case with a bare existential, the statement
here returns the factorization data and pins `S` down by `S ∘ S = Mᵀ ∘ M` together with
symmetry — the two properties that characterize `S` as the modulus of `M` — so the "canonical
object" is recoverable from the statement.  If a real operator square root is added upstream,
this file should be replaced by a specialization of the complex development.

## TODO

* `TODO(RCLike)`: generalize the operator results from `ℝ` to `RCLike 𝕜`.  The eigenbasis
  machinery (`LinearMap.IsSymmetric.eigenvectorBasis`) already works over `RCLike`; only the
  real-inner-product bookkeeping below would need to be redone.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Ch. 8
  (the unitary polar factor as the nearest isometry).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/InnerProductSpace/NearIsometry.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `ForMathlib.Real.abs_one_sub_inv_sqrt_le` (moved to
  `ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`),
  `ForMathlib.LinearMap.exists_linearIsometryEquiv_norm_sub_le`, and
  `TauCeti.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_le`
  (renamed here `ForMathlib.*` → `TauCeti.*`).
* Original authorship: formalized by Claude Fable 5 (`claude-fable-5[1m]`), golf
  pass by Claude Opus 4.8 (`claude-opus-4-8[1m]`); staged for Mathlib (no
  separate copyright line in the source header), released under Apache 2.0.
* Extraction class: **copied, then redesigned** per
  `dev/tauceti-signature-polish-todo.md` §8.2 — the existential now carries the polar
  factorization, the constant is sharp, and the scalar `Real.sqrt` lemmas were moved out.
* Spectra influence: **none** (imports only Mathlib and the Tau Ceti `Real.sqrt` staging
  module).
-/

@[expose] public section

namespace TauCeti

open scoped RealInnerProductSpace InnerProductSpace
open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Diagonal

variable {d : ℕ}

/-- The operator that scales the `k`-th vector of an orthonormal basis by `c k`. -/
private noncomputable def diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ fun j => c j • b j

private theorem diagonal_basis (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) (k : Fin d) :
    diagonal b c (b k) = c k • b k := by
  have := b.toBasis.constr_basis ℝ (fun j => c j • b j) k
  rwa [OrthonormalBasis.coe_toBasis] at this

/-- A diagonal operator acts on basis coordinates by scalar multiplication. -/
private theorem repr_diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) (x : E)
    (k : Fin d) : b.repr (diagonal b c x) k = c k * b.repr x k := by
  have hx : diagonal b c x = ∑ j : Fin d, b.repr x j • (c j • b j) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, diagonal_basis]
  rw [b.repr_apply_apply, hx, inner_sum, Finset.sum_eq_single k]
  · rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.norm_eq_one k, b.repr_apply_apply]
    ring
  · intro j _ hjk
    rw [real_inner_smul_right, real_inner_smul_right, b.inner_eq_zero hjk.symm]
    ring
  · intro hk; exact absurd (Finset.mem_univ k) hk

private theorem isSymmetric_diagonal (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ) :
    (diagonal b c).IsSymmetric := by
  have key : ∀ u v : E, ⟪diagonal b c u, v⟫_ℝ = ∑ k : Fin d, c k * b.repr u k * b.repr v k := by
    intro u v
    conv_lhs => rw [← b.sum_repr v]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm, ← b.repr_apply_apply, repr_diagonal]
    ring
  intro x y
  rw [key, real_inner_comm, key]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A diagonal operator whose scaling factors are bounded by `δ` has operator norm at most
`δ`, by Parseval. -/
private theorem norm_diagonal_apply_le (b : OrthonormalBasis (Fin d) ℝ E) (c : Fin d → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hc : ∀ k, |c k| ≤ δ) (x : E) :
    ‖diagonal b c x‖ ≤ δ * ‖x‖ := by
  have hpars : ∀ y : E, ∑ k : Fin d, b.repr y k ^ 2 = ‖y‖ ^ 2 := by
    intro y
    rw [← b.sum_sq_inner_right y]
    exact Finset.sum_congr rfl fun k _ => by rw [b.repr_apply_apply]
  have hbnd : ‖diagonal b c x‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    rw [← hpars (diagonal b c x), ← hpars x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [repr_diagonal, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := hc k
    nlinarith [abs_nonneg (c k), abs_le.mp (hc k), sq_abs (c k)]
  nlinarith [hbnd, norm_nonneg (diagonal b c x), mul_nonneg hδ0 (norm_nonneg x),
    sq_nonneg (‖diagonal b c x‖ - δ * ‖x‖)]

end Diagonal

variable [FiniteDimensional ℝ E]

namespace LinearMap

/-- **Polar factorization of a near-isometry.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (`|⟪M x, M x⟫ - ⟪x, x⟫| ≤ δ * ⟪x, x⟫`, with `δ < 1`), then `M` factors as `M = W ∘ S`
where

* `W` is a linear isometry equivalence of `E`,
* `S` is the modulus of `M`: symmetric, with `S ∘ S = Mᵀ ∘ M`, and
* `S` moves no vector by more than `δ`: `‖S x - x‖ ≤ δ * ‖x‖`.

`S` is built from the orthonormal eigenbasis of the Gram operator `Mᵀ ∘ M`, rescaling the
`k`-th eigenvector by `√(μ k)`; `W = M ∘ S⁻¹` is an isometry because `⟪M b_j, M b_k⟫ = μ_j δ_jk`
on that basis.  Since the two stated properties of `S` determine it (a symmetric square root of
`Mᵀ M` that is close to the identity is *the* positive square root), this statement exposes the
canonical polar factor rather than an arbitrary witness — see the module docstring for why the
real case is stated existentially at all.

The hypothesis `δ < 1` is exactly what is needed: it forces the eigenvalues `μ k ≥ 1 - δ` of
the Gram operator to be positive, so that `S` is invertible and `M` is bounded below. -/
theorem exists_linearIsometryEquiv_comp_polarFactor (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ (W : E ≃ₗᵢ[ℝ] E) (S : E →ₗ[ℝ] E),
      (∀ x : E, M x = W (S x)) ∧ S.IsSymmetric ∧ S ∘ₗ S = M.adjoint ∘ₗ M ∧
        ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
  -- Degenerate case: if `E` is a subsingleton every vector is `0`.
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · refine ⟨LinearIsometryEquiv.refl ℝ E, LinearMap.id, fun x => ?_, fun x y => ?_,
      LinearMap.ext fun x => ?_, fun x => ?_⟩ <;>
      simp [Subsingleton.elim x (0 : E)]
  -- Main case: `E` is nontrivial.  Derive `δ ≥ 0` from a nonzero vector.
  have hδ0 : 0 ≤ δ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
    have hmul : 0 ≤ δ * ⟪v, v⟫_ℝ :=
      le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)
    exact nonneg_of_mul_nonneg_left hmul hvpos
  obtain ⟨d, hd⟩ : ∃ d, finrank ℝ E = d := ⟨_, rfl⟩
  -- The Gram operator and its symmetry.
  set G : E →ₗ[ℝ] E := M.adjoint * M with hG
  have hGsymm : G.IsSymmetric := LinearMap.isSymmetric_adjoint_mul_self M
  have hGquad : ∀ x : E, ⟪G x, x⟫_ℝ = ⟪M x, M x⟫_ℝ := by
    intro x
    rw [hG, Module.End.mul_apply, LinearMap.adjoint_inner_left]
  -- Sorted eigen-data of `G`.
  set b := hGsymm.eigenvectorBasis hd with hb
  set μ := hGsymm.eigenvalues hd with hμ
  have hunit : ∀ k : Fin d, ⟪b k, b k⟫_ℝ = 1 := fun k => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one k]; ring
  have hGbasis : ∀ k : Fin d, G (b k) = μ k • b k := by
    intro k
    rw [hb, hGsymm.apply_eigenvectorBasis, ← hb, ← hμ]
    simp
  -- Each eigenvalue lies in `[1 - δ, 1 + δ]`, in particular it is positive.
  have hμbound : ∀ k : Fin d, |μ k - 1| ≤ δ := by
    intro k
    have hGbk : ⟪G (b k), b k⟫_ℝ = μ k := by
      rw [hGbasis k, real_inner_smul_left, hunit k, mul_one]
    have := hM (b k)
    rwa [← hGquad, hGbk, hunit k, mul_one] at this
  have hμpos : ∀ k : Fin d, 0 < μ k := by
    intro k
    have := hμbound k
    rw [abs_le] at this
    linarith
  have hsqrtpos : ∀ k : Fin d, 0 < Real.sqrt (μ k) := fun k => Real.sqrt_pos.mpr (hμpos k)
  -- The modulus `S = G^(1/2)` and its inverse `R = G^(-1/2)`, diagonal in the eigenbasis.
  set S : E →ₗ[ℝ] E := diagonal b (fun k => Real.sqrt (μ k)) with hS
  set R : E →ₗ[ℝ] E := diagonal b (fun k => (Real.sqrt (μ k))⁻¹) with hR
  have hRS : ∀ x : E, R (S x) = x := by
    have : R ∘ₗ S = LinearMap.id := by
      refine b.toBasis.ext fun k => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearMap.id_apply, hS, hR,
        diagonal_basis, map_smul, diagonal_basis, smul_smul,
        mul_inv_cancel₀ (ne_of_gt (hsqrtpos k)), one_smul]
    intro x
    exact congrArg (fun T : E →ₗ[ℝ] E => T x) this
  -- `S` is a square root of the Gram operator.
  have hSS : S ∘ₗ S = M.adjoint ∘ₗ M := by
    refine b.toBasis.ext fun k => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, hS, diagonal_basis, map_smul,
      diagonal_basis, smul_smul, Real.mul_self_sqrt (le_of_lt (hμpos k))]
    exact (hGbasis k).symm
  -- `M` applied to the eigenbasis gives inner products `μ j * δ_{jk}`.
  have hMM : ∀ j k : Fin d, ⟪M (b j), M (b k)⟫_ℝ = if j = k then μ j else 0 := by
    intro j k
    have hadj : ⟪M (b j), M (b k)⟫_ℝ = ⟪G (b j), b k⟫_ℝ := by
      rw [hG, Module.End.mul_apply, LinearMap.adjoint_inner_left]
    rw [hadj, hGbasis j, real_inner_smul_left]
    by_cases hjk : j = k
    · subst hjk; rw [hunit j, if_pos rfl, mul_one]
    · rw [b.inner_eq_zero hjk, if_neg hjk, mul_zero]
  -- The candidate isometry `W₀ = M ∘ R`.
  set W₀ : E →ₗ[ℝ] E := M ∘ₗ R with hW
  have hWbasis : ∀ k : Fin d, W₀ (b k) = (Real.sqrt (μ k))⁻¹ • M (b k) := by
    intro k
    rw [hW, LinearMap.comp_apply, hR, diagonal_basis, map_smul]
  have hWortho : ∀ j k : Fin d, ⟪W₀ (b j), W₀ (b k)⟫_ℝ = ⟪b j, b k⟫_ℝ := by
    intro j k
    rw [hWbasis, hWbasis, real_inner_smul_left, real_inner_smul_right, hMM]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, hunit j]
      have hsj := hsqrtpos j
      have hsqj : Real.sqrt (μ j) * Real.sqrt (μ j) = μ j :=
        Real.mul_self_sqrt (le_of_lt (hμpos j))
      field_simp
      exact (Real.sq_sqrt (le_of_lt (hμpos j))).symm
    · rw [if_neg hjk, b.inner_eq_zero hjk, mul_zero, mul_zero]
  have hWinner : ∀ x y : E, ⟪W₀ x, W₀ y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hWortho k j]
  -- `S` moves no vector by more than `δ`, since `|√(μ k) - 1| ≤ |μ k - 1| ≤ δ`.
  have hSid : ∀ x : E, S x - x = diagonal b (fun k => Real.sqrt (μ k) - 1) x := by
    have : S - LinearMap.id = diagonal b fun k => Real.sqrt (μ k) - 1 := by
      refine b.toBasis.ext fun k => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.sub_apply, LinearMap.id_apply, hS,
        diagonal_basis, diagonal_basis, sub_smul, one_smul]
    intro x
    have := congrArg (fun T : E →ₗ[ℝ] E => T x) this
    simpa using this
  have hSest : ∀ x : E, ‖S x - x‖ ≤ δ * ‖x‖ := by
    intro x
    rw [hSid x]
    refine norm_diagonal_apply_le b _ hδ0 (fun k => ?_) x
    exact (Real.abs_sqrt_sub_one_le_abs_sub_one (le_of_lt (hμpos k))).trans (hμbound k)
  -- Bundle `W₀` as a linear isometry equivalence.
  have hWcoe : ⇑(W₀.isometryOfInner hWinner) = ⇑W₀ := W₀.coe_isometryOfInner hWinner
  have hWsurj : Function.Surjective (W₀.isometryOfInner hWinner) := by
    rw [hWcoe]
    exact LinearMap.injective_iff_surjective.mp
      (hWcoe ▸ (W₀.isometryOfInner hWinner).injective)
  refine ⟨LinearIsometryEquiv.ofSurjective _ hWsurj, S, fun x => ?_,
    hS ▸ isSymmetric_diagonal b _, hSS, hSest⟩
  have hx : LinearIsometryEquiv.ofSurjective _ hWsurj (S x) = W₀ (S x) := by
    rw [LinearIsometryEquiv.coe_ofSurjective, hWcoe]
  rw [hx, hW, LinearMap.comp_apply, hRS]

/-- **The sharp near-isometry estimate.**  If the quadratic form of a linear map `M` on a
finite-dimensional real inner product space is uniformly `δ`-close to the identity quadratic
form (with `δ < 1`), then `M` lies within `δ` — not `2 * δ` — of a genuine linear isometry
equivalence.

This is immediate from `exists_linearIsometryEquiv_comp_polarFactor`: `M x - W x` is the image
under the isometry `W` of `S x - x`. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, S, hMS, -, -, hSest⟩ := exists_linearIsometryEquiv_comp_polarFactor M hδ hM
  refine ⟨W, fun x => ?_⟩
  rw [hMS x, ← map_sub, W.norm_map]
  exact hSest x

/-- **Quantitative polar factor for a near-isometry**, historical form.

Superseded by `TauCeti.LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le`, which gives the
sharp constant `δ` under the weaker hypothesis `δ < 1`.  This statement is retained because it
is the form quoted downstream (`Acharyya2025.PolarFactor`) and by the challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ∀ x : E, |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_norm_sub_apply_le M (by linarith) hM
  refine ⟨W, fun x => (hW x).trans ?_⟩
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · simp [Subsingleton.elim x (0 : E)]
  · have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvpos : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.mpr hv
      exact nonneg_of_mul_nonneg_left
        (le_trans (abs_nonneg (⟪M v, M v⟫_ℝ - ⟪v, v⟫_ℝ)) (hM v)) hvpos
    have := norm_nonneg x
    nlinarith

end LinearMap

namespace ContinuousLinearMap

/-- The operator-norm hypothesis `‖Mᵀ M - 1‖ ≤ δ` implies the pointwise quadratic-form
hypothesis, by Cauchy--Schwarz. -/
private theorem abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le (M : E →L[ℝ] E) {δ : ℝ}
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) (x : E) :
    |⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ := by
  have hid : ⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ
      = ⟪(M : E →ₗ[ℝ] E) x, (M : E →ₗ[ℝ] E) x⟫_ℝ - ⟪x, x⟫_ℝ := by
    rw [sub_apply, mul_apply_eq_comp, one_apply_eq_self, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp
  rw [← hid]
  calc |⟪(ContinuousLinearMap.adjoint M * M - 1) x, x⟫_ℝ|
      ≤ ‖(ContinuousLinearMap.adjoint M * M - 1) x‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖ContinuousLinearMap.adjoint M * M - 1‖ * ‖x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.adjoint M * M - 1).le_opNorm x) (norm_nonneg x)
    _ ≤ δ * ‖x‖ * ‖x‖ := by gcongr
    _ = δ * ⟪x, x⟫_ℝ := by rw [real_inner_self_eq_norm_mul_norm]; ring

/-- **The sharp near-isometry estimate, operator-norm form.**  If a continuous linear map `M` on
a finite-dimensional real inner product space satisfies `‖Mᵀ M - 1‖ ≤ δ` with `δ < 1`, then `M`
lies within `δ` of a genuine linear isometry equivalence.

See `ContinuousLinearMap.norm_sub_polarIsometryOfIsUnitModulus_le` in
`ForTauCeti/Analysis/InnerProductSpace/PolarIsometry.lean` for the version over arbitrary
complex Hilbert spaces, which additionally names the isometry. -/
theorem exists_linearIsometryEquiv_norm_sub_apply_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ < 1)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

/-- **Quantitative polar factor, operator-norm form**, historical statement.

Superseded by `TauCeti.ContinuousLinearMap.exists_linearIsometryEquiv_norm_sub_apply_le`;
retained for the downstream paper development and the challenge comparator. -/
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) :
    ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖ := by
  obtain ⟨W, hW⟩ := LinearMap.exists_linearIsometryEquiv_norm_sub_le (M : E →ₗ[ℝ] E) hδ
    (abs_inner_sub_le_of_norm_adjoint_mul_self_sub_one_le M hM)
  exact ⟨W, fun x => by simpa using hW x⟩

end ContinuousLinearMap

end TauCeti

end
