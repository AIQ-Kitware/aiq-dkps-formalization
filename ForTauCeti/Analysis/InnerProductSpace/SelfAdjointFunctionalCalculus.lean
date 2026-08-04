/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import ForTauCeti.Analysis.InnerProductSpace.CourantFischer


/-!
# Finite-dimensional self-adjoint functional calculus

For a symmetric endomorphism on a finite-dimensional real or complex inner-product
space, apply a real scalar function to the ordered eigenvalues and reconstruct the
operator in the associated orthonormal eigenbasis.

The construction is intended as a small `RCLike` counterpart of the continuous
functional calculus.  It is sufficient for functions such as `arcsin` and the
totalized tangent functions used by finite-dimensional operator-angle theory.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `caa0966`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Apply a real function to the spectrum of a finite-dimensional symmetric
endomorphism. -/
noncomputable def selfAdjointFunctionalCalculus
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) •
      (InnerProductSpace.rankOne 𝕜
        (hT.eigenvectorBasis rfl i)
        (hT.eigenvectorBasis rfl i)).toLinearMap

/-- The calculus is additive in the symbol: a finite sum of rank-one terms, added
coefficientwise. -/
theorem selfAdjointFunctionalCalculus_add {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    selfAdjointFunctionalCalculus hT (f + g)
      = selfAdjointFunctionalCalculus hT f + selfAdjointFunctionalCalculus hT g := by
  simp only [selfAdjointFunctionalCalculus, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_smul, RCLike.ofReal_add]

/-- The calculus is real-homogeneous in the symbol. -/
theorem selfAdjointFunctionalCalculus_smul {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (c : ℝ)
    (f : ℝ → ℝ) :
    selfAdjointFunctionalCalculus hT (c • f) = (c : 𝕜) • selfAdjointFunctionalCalculus hT f := by
  simp only [selfAdjointFunctionalCalculus, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_smul, RCLike.ofReal_mul]

/-- The functional calculus acts diagonally in the chosen eigenbasis. -/
theorem selfAdjointFunctionalCalculus_apply_eigenvectorBasis
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    (k : Fin (finrank 𝕜 E)) :
    selfAdjointFunctionalCalculus hT f (hT.eigenvectorBasis rfl k) =
      ((f (hT.eigenvalues rfl k) : ℝ) : 𝕜) •
        hT.eigenvectorBasis rfl k := by
  classical
  unfold selfAdjointFunctionalCalculus
  rw [LinearMap.sum_apply]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro i _ hik
    simp [InnerProductSpace.rankOne_apply,
      orthonormal_iff_ite.mp (hT.eigenvectorBasis rfl).orthonormal i k,
      if_neg hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk
  · simp [InnerProductSpace.rankOne_apply]

/-- Applying a real function to a symmetric operator remains symmetric. -/
theorem selfAdjointFunctionalCalculus_isSymmetric
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    (selfAdjointFunctionalCalculus hT f).IsSymmetric := by
  classical
  unfold selfAdjointFunctionalCalculus
  induction (Finset.univ : Finset (Fin (finrank 𝕜 E))) using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      rw [Finset.sum_insert hi]
      exact
        ((InnerProductSpace.isSymmetric_rankOne_self
          (hT.eigenvectorBasis rfl i)).smul
            (RCLike.conj_ofReal (f (hT.eigenvalues rfl i)))).add hs

/-- **The calculus is bounded by the sup of the symbol on the spectrum.**

Parseval in the eigenbasis: the calculus multiplies the `i`-th coordinate of `x` by
`f (λᵢ)`, so the squared norm is a weighted sum of the coordinate weights. This is the
estimate continuity of `f ↦ calculus hT f` rests on. -/
theorem norm_selfAdjointFunctionalCalculus_apply_le {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (f : ℝ → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, |f (hT.eigenvalues rfl i)| ≤ M) (x : E) :
    ‖selfAdjointFunctionalCalculus hT f x‖ ≤ M * ‖x‖ := by
  classical
  set b := hT.eigenvectorBasis rfl with hb
  set S := selfAdjointFunctionalCalculus hT f with hS
  have hSsym : S.IsSymmetric := selfAdjointFunctionalCalculus_isSymmetric hT f
  have hcoord : ∀ i, ⟪b i, S x⟫_𝕜 = ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 := by
    intro i
    rw [← hSsym (b i) x, hS, selfAdjointFunctionalCalculus_apply_eigenvectorBasis,
      inner_smul_left, RCLike.conj_ofReal]
  have hsq : ‖S x‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (S x), ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hcoord i, norm_mul, mul_pow, RCLike.norm_ofReal]
    have hsq2 : |f (hT.eigenvalues rfl i)| ^ 2 ≤ M ^ 2 := by
      nlinarith [abs_nonneg (f (hT.eigenvalues rfl i)), hM i]
    exact mul_le_mul_of_nonneg_right hsq2 (by positivity)
  have h1 : (0 : ℝ) ≤ M * ‖x‖ := mul_nonneg hM0 (norm_nonneg x)
  nlinarith [norm_nonneg (S x), hsq, h1]

/-- The identity function recovers the original symmetric operator. -/
theorem selfAdjointFunctionalCalculus_id
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    selfAdjointFunctionalCalculus hT id = T := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis,
    hT.apply_eigenvectorBasis]
  rfl

/-- The calculus depends only on the operator, not on the symmetry witness.
The operator occurs solely inside that witness's type, so a plain rewrite
cannot reach it; this is the bridge that lets callers replace it. -/
theorem selfAdjointFunctionalCalculus_congr_op {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (h : T = S) (f : ℝ → ℝ) :
    selfAdjointFunctionalCalculus hT f = selfAdjointFunctionalCalculus hS f := by
  subst h
  rfl

/-- Functions agreeing on every eigenvalue produce the same operator. -/
theorem selfAdjointFunctionalCalculus_congr
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (hfg : ∀ i : Fin (finrank 𝕜 E),
      f (hT.eigenvalues rfl i) = g (hT.eigenvalues rfl i)) :
    selfAdjointFunctionalCalculus hT f =
      selfAdjointFunctionalCalculus hT g := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis]
  rw [hfg i]

/-- Composition corresponds to pointwise multiplication of scalar functions. -/
theorem selfAdjointFunctionalCalculus_comp
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    selfAdjointFunctionalCalculus hT f ∘ₗ
        selfAdjointFunctionalCalculus hT g =
      selfAdjointFunctionalCalculus hT (fun x => f x * g x) := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis, map_smul, smul_smul,
    RCLike.ofReal_mul, mul_comm]

/-- Constant zero gives the zero operator. -/
@[simp] theorem selfAdjointFunctionalCalculus_zero
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    selfAdjointFunctionalCalculus hT (fun _ => 0) = 0 := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp [selfAdjointFunctionalCalculus_apply_eigenvectorBasis]


/-- Functional calculus of a real scalar multiple of the identity is scalar
evaluation.  This is the finite `RCLike` bridge used by planar angle models. -/
theorem selfAdjointFunctionalCalculus_real_smul_id
    (r : ℝ) (f : ℝ → ℝ) :
    let hS : (((r : ℝ) : 𝕜) • LinearMap.id : E →ₗ[𝕜] E).IsSymmetric := by
      intro x y
      simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
        inner_smul_right, RCLike.conj_ofReal]
    selfAdjointFunctionalCalculus hS f =
      (((f r : ℝ) : 𝕜) • LinearMap.id) := by
  dsimp only
  let hS : (((r : ℝ) : 𝕜) • LinearMap.id : E →ₗ[𝕜] E).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have heig : hS.eigenvalues rfl = fun _ => r := by
    apply LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis hS rfl (stdOrthonormalBasis 𝕜 E)
    · exact antitone_const
    · intro i
      simp
  refine (hS.eigenvectorBasis rfl).toBasis.ext fun i => ?_
  rw [OrthonormalBasis.coe_toBasis,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis, heig]
  simp

/-- Functional calculus on an arbitrary eigenvector.  Unlike the basis lemma,
this form is stable on repeated eigenspaces and is the key commutant property. -/
theorem selfAdjointFunctionalCalculus_apply_of_apply_eq_smul
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    {x : E} {lam : ℝ} (hx : T x = ((lam : ℝ) : 𝕜) • x) :
    selfAdjointFunctionalCalculus hT f x =
      ((f lam : ℝ) : 𝕜) • x := by
  classical
  let b := hT.eigenvectorBasis rfl
  rw [← b.sum_repr x, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, selfAdjointFunctionalCalculus_apply_eigenvectorBasis]
  by_cases hi : hT.eigenvalues rfl i = lam
  · rw [hi]; exact smul_comm _ _ _
  · have hcoeff : b.repr x i = 0 := by
      rw [b.repr_apply_apply]
      have heig := hT.apply_eigenvectorBasis rfl i
      have hinner :
          ((hT.eigenvalues rfl i : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 =
            ((lam : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 := by
        calc
          ((hT.eigenvalues rfl i : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜
              = ⟪T (b i), x⟫_𝕜 := by
                  rw [heig, inner_smul_left, RCLike.conj_ofReal]
          _ = ⟪b i, T x⟫_𝕜 := hT _ _
          _ = ((lam : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 := by
                  rw [hx, inner_smul_right]
      have hscalar : (((hT.eigenvalues rfl i - lam : ℝ) : 𝕜)) ≠ 0 :=
        RCLike.ofReal_ne_zero.mpr (sub_ne_zero.mpr hi)
      apply (mul_eq_zero.mp ?_).resolve_left hscalar
      simpa [RCLike.ofReal_sub, sub_mul] using sub_eq_zero.mpr hinner
    rw [hcoeff]
    simp

/-- The constant function `1` gives the identity operator. -/
theorem selfAdjointFunctionalCalculus_one {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    selfAdjointFunctionalCalculus hT (fun _ => (1 : ℝ)) = LinearMap.id := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis, selfAdjointFunctionalCalculus_apply_eigenvectorBasis]
  simp

/-- **The calculus agrees with polynomial evaluation on monomials.**

Induction on `n` from `..._one` and `..._comp`; the base is the identity operator and the
step is multiplicativity of the symbol. This is what makes the calculus an algebra map
extending `Polynomial.aeval`, the property any route to the Mathlib CFC goes through. -/
theorem selfAdjointFunctionalCalculus_pow {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (n : ℕ) :
    selfAdjointFunctionalCalculus hT (fun x => x ^ n) = T ^ n := by
  induction n with
  | zero =>
      simpa [pow_zero, Module.End.one_eq_id] using selfAdjointFunctionalCalculus_one hT
  | succ k ih =>
      have hmul := selfAdjointFunctionalCalculus_comp hT (fun x => x ^ k) id
      have : (fun x : ℝ => x ^ k * id x) = fun x : ℝ => x ^ (k + 1) := by
        funext x; simp [pow_succ]
      rw [this] at hmul
      rw [← hmul, ih, selfAdjointFunctionalCalculus_id, pow_succ]
      rfl

/-- **Extending a symbol by zero off a set containing the spectrum changes nothing.**

The calculus sees `f` only at the eigenvalues, so restricting a symbol to any set containing
them and extending by zero leaves the operator alone. This is what lets a
`g : C(spectrum ℝ a, ℝ)` be turned into an `ℝ → ℝ` for the finite calculus without the
algebra operations drifting: `indicator` commutes with `+` and `*`, and the mismatch at `1`
is invisible here. -/
theorem selfAdjointFunctionalCalculus_indicator {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {S : Set ℝ} (hS : ∀ i, hT.eigenvalues rfl i ∈ S) (g : ℝ → ℝ) :
    selfAdjointFunctionalCalculus hT (S.indicator g)
      = selfAdjointFunctionalCalculus hT g :=
  selfAdjointFunctionalCalculus_congr hT fun i => Set.indicator_of_mem (hS i) g

open scoped Classical in
/-- Extend a continuous function on a subset of `ℝ` to all of `ℝ` by zero.

The finite calculus consumes `ℝ → ℝ`, while `cfcHom` is stated on `C(spectrum ℝ a, ℝ)`; this
is the bridge between the two.  It is multiplicative and additive outright — both sides
vanish off `S` — and `selfAdjointFunctionalCalculus_indicator` covers the unit, the one
operation it does not respect. -/
noncomputable def extendSymbol {S : Set ℝ} (g : C(S, ℝ)) : ℝ → ℝ :=
  fun x => if h : x ∈ S then g ⟨x, h⟩ else 0

open scoped Classical in
@[simp] theorem extendSymbol_apply_of_mem {S : Set ℝ} (g : C(S, ℝ)) {x : ℝ} (hx : x ∈ S) :
    extendSymbol g x = g ⟨x, hx⟩ := dif_pos hx

open scoped Classical in
theorem extendSymbol_mul {S : Set ℝ} (g₁ g₂ : C(S, ℝ)) :
    extendSymbol (g₁ * g₂) = fun x => extendSymbol g₁ x * extendSymbol g₂ x := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendSymbol, hx]

open scoped Classical in
theorem extendSymbol_add {S : Set ℝ} (g₁ g₂ : C(S, ℝ)) :
    extendSymbol (g₁ + g₂) = fun x => extendSymbol g₁ x + extendSymbol g₂ x := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendSymbol, hx]

open scoped Classical in
@[simp] theorem extendSymbol_zero {S : Set ℝ} :
    extendSymbol (0 : C(S, ℝ)) = fun _ => 0 := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendSymbol, hx]

open scoped Classical in
theorem extendSymbol_one_eq_indicator {S : Set ℝ} :
    extendSymbol (1 : C(S, ℝ)) = S.indicator (fun _ => 1) := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendSymbol, Set.indicator, hx]

/-- Every operator commuting with a symmetric map commutes with its finite
real functional calculus.  This includes repeated eigenvalues: the proof uses
that the commuting operator preserves each eigenspace. -/
theorem selfAdjointFunctionalCalculus_comm
    {T B : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    (hBT : B ∘ₗ T = T ∘ₗ B) :
    B ∘ₗ selfAdjointFunctionalCalculus hT f =
      selfAdjointFunctionalCalculus hT f ∘ₗ B := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, LinearMap.comp_apply,
    selfAdjointFunctionalCalculus_apply_eigenvectorBasis, map_smul]
  have hBeig : T (B (hT.eigenvectorBasis rfl i)) =
      ((hT.eigenvalues rfl i : ℝ) : 𝕜) • B (hT.eigenvectorBasis rfl i) := by
    have h := LinearMap.congr_fun hBT (hT.eigenvectorBasis rfl i)
    simpa [LinearMap.comp_apply, hT.apply_eigenvectorBasis, map_smul] using h.symm
  rw [selfAdjointFunctionalCalculus_apply_of_apply_eq_smul hT f hBeig]

/-- **Spectral positive square root** of a positive symmetric operator `T`, as the
functional calculus of `Real.sqrt`:
`sqrt T = ∑ᵢ √λᵢ • (rank-one projection onto the `i`-th eigenvector)`, where `λᵢ ≥ 0`
are the eigenvalues of `T`.  Source: Horn--Johnson Thm 7.2.6.

This was once a second `noncomputable def` with that sum written out, and the
library proved the two coincide by `rfl` — one object defined twice.  The
duplicate has been collapsed; the uniqueness theory that only the square root
has (`sqrt_unique`, `ker_sqrt`, `range_sqrt`, `sqrt_mul_self`) is unchanged and
still lives in `ForTauCeti/Analysis/InnerProductSpace/PositiveSqrt.lean`, which now
imports this module rather than the other way round. -/
noncomputable def _root_.LinearMap.IsPositive.sqrt
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  selfAdjointFunctionalCalculus hT.isSymmetric Real.sqrt

/-- The spectral square root is the finite self-adjoint functional calculus of
`Real.sqrt`.  True by definition; kept because it is the name downstream proofs
rewrite with. -/
theorem selfAdjointFunctionalCalculus_sqrt
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    selfAdjointFunctionalCalculus hT.isSymmetric Real.sqrt = hT.sqrt :=
  rfl

/-- Commutation passes from a positive operator to its positive square root. -/
theorem sqrt_comm
    {T B : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (hBT : B ∘ₗ T = T ∘ₗ B) :
    B ∘ₗ hT.sqrt = hT.sqrt ∘ₗ B := by
  rw [← selfAdjointFunctionalCalculus_sqrt hT]
  exact selfAdjointFunctionalCalculus_comm hT.isSymmetric Real.sqrt hBT

end TauCeti
