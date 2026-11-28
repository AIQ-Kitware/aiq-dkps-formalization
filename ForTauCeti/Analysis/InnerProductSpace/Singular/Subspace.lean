/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SingularSubspace.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

Groundwork for the Yu–Wang–Samworth singular-vector extension: perturbing the
Gram operator `A⋆A` by `Â⋆Â − A⋆A`, controlled by `Â − A`. The adjoint norm
bound used here is Tau Ceti's `LinearMap.norm_adjoint_apply_le`.

Plan step W0.1(d) added by Claude Opus 4.8 (claude-opus-4-8[1m]): the
singular-value symmetry `σ(A⋆) = σ(A)` for a square operator, proved through the
eigenvalue invariance of a symmetric operator under unitary conjugation
(`eigenvalues_conj_unitary`, a Courant–Fischer consequence) applied to the polar
identity `A A⋆ = U (A⋆A) U⁻¹` with `U = choosePolarUnitary A`.
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Trace
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.Gram.Perturbation
public import TauCeti.Analysis.InnerProductSpace.SchurHorn
public import ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Basic


/-! # Gram-operator perturbation

For `A, Â : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
singular subspaces are the spectral subspaces of the Gram operators `A⋆A` and
`Â⋆Â`.  The Yu–Wang–Samworth singular-vector bound applies the symmetric result
to these Gram operators, so it needs the Gram perturbation `Â⋆Â − A⋆A` bounded in
terms of `Â − A`.

## Main results

Gram perturbation, singular-value extrema, energy identities and Gram eigenvalue
symmetry are consumed directly from accepted Tau Ceti APIs. The remaining results
relate the modulus trace to arbitrary basis evaluations, compare its trace with
contraction energy, state a squared singular-value growth-constant corollary, and
prove unitary conjugation identities. In particular, `isSymmetric_conj_unitary`
has no finite-dimensionality or completeness assumption; the generic adjoint-
conjugation API does not cover that full scope.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem
  for statisticians*, Biometrika 102 (2015), §"singular-vector extension".
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open _root_.LinearMap
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

local instance instCompleteSpaceE : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
local instance instCompleteSpaceF : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F

/-- **Trace of the modulus = sum of singular values.** For an endomorphism
`A : E →ₗ[𝕜] E`, `∑ₖ re⟪|A| bₖ, bₖ⟫ = ∑ᵢ σᵢ(A)` in any orthonormal basis `b`.
The modulus `|A| = √(A⋆A)` is diagonal in the `A⋆A`-eigenbasis with entries
`√λᵢ(A⋆A) = σᵢ(A)`, and the trace is basis-independent. -/
theorem sum_re_inner_abs_self_eq_sum_singularValues (A : E →ₗ[𝕜] E)
    {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, RCLike.re ⟪A.operatorAbs (b k), b k⟫_𝕜 = ∑ i : Fin n, A.singularValues (i : ℕ) := by
  subst hn
  have h := A.re_trace_operatorAbs
  rw [LinearMap.trace_eq_sum_inner _ b, map_sum,
    UnitarilyInvariantSeminorm.nuclear_apply, ← A.sum_fin_singularValues (fun s => s) rfl] at h
  simpa only [inner_re_symm] using h

/-- **Frobenius² ≤ trace of the modulus, for a contraction.** If `A : E →ₗ[𝕜] E`
is a contraction, then `∑ₖ ‖A bₖ‖² ≤ ∑ₖ re⟪|A| bₖ, bₖ⟫`, i.e. `∑ σᵢ² ≤ ∑ σᵢ`
(each `σᵢ ∈ [0, 1]`).  This is the core inequality of the aligned-basis
(orthogonal-Procrustes) argument: `∑‖wⱼ − uⱼ‖² = 2d − 2∑σ ≤ 2d − 2∑σ² = 2·sinΘ²`. -/
theorem sum_sq_norm_le_sum_re_inner_abs_of_contraction {A : E →ₗ[𝕜] E}
    (h : ∀ x, ‖A x‖ ≤ ‖x‖) {n : ℕ} (hn : finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, ‖A (b k)‖ ^ 2 ≤ ∑ k, RCLike.re ⟪A.operatorAbs (b k), b k⟫_𝕜 := by
  subst hn
  rw [sum_re_inner_abs_self_eq_sum_singularValues A rfl b]
  have henergy : ∑ k, ‖A (b k)‖ ^ 2 =
      ∑ i : Fin (finrank 𝕜 E), A.singularValues i ^ 2 :=
    (RCLike.ofReal_injective
      ((A.trace_adjoint_comp_self_eq_sum_norm_apply_sq b).symm.trans
        A.trace_adjoint_comp_self_eq_sum_sq_singularValues)).trans
      (A.sum_fin_singularValues (· ^ 2) (by simp)).symm
  rw [henergy]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : A.singularValues i ≤ 1 :=
    LinearMap.singularValues_le_of_norm_apply_le zero_le_one
      (by simpa only [one_mul] using h) i
  have h0 := A.singularValues_nonneg (i : ℕ)
  nlinarith

/-- **Gram-transported Weyl bound for squared singular values.** The `k`-th
squared singular values of `A` and `Â` differ by at most the Gram perturbation
bound: `|σₖ(Â)² − σₖ(A)²| ≤ (a + â) ε`.  Via the dictionary `σₖ² = λₖ(·⋆·)`
(`sq_singularValues_fin`) and Weyl's inequality on the Gram operators, fed by the
perturbation bound from `LinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_apply_le`.

**This is weaker than Weyl's inequality for singular values, in three ways**, and
the name is deliberately not "Weyl's inequality" on that account: it bounds the
*squares*, its constant carries the extra factor `a + â` so the bound degrades
with the size of the operators, and it needs the auxiliary hypotheses `hA`, `hÂ`
that the genuine theorem does not.  The sharp form is
`LinearMap.abs_singularValues_sub_singularValues_le`
(`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung`),
`|σₙ(T) − σₙ(S)| ≤ ‖T − S‖`, which implies this one but not conversely — dividing
back out by `σₖ(A) + σₖ(Â)` recovers nothing when the singular values are small.
This version survives because it is the shape the Gram-side arguments produce. -/
theorem abs_sq_singularValues_sub_le {A Â : E →ₗ[𝕜] F} {a â ε : ℝ}
    (_hâ : 0 ≤ â) (_hε : 0 ≤ ε)
    (hA : ∀ x, ‖A x‖ ≤ a * ‖x‖) (hÂ : ∀ x, ‖Â x‖ ≤ â * ‖x‖)
    (hE : ∀ x, ‖(Â - A) x‖ ≤ ε * ‖x‖)
    {n : ℕ} (hn : finrank 𝕜 E = n) (k : Fin n) :
    |Â.singularValues k ^ 2 - A.singularValues k ^ 2| ≤ (a + â) * ε := by
  rw [Â.sq_singularValues_fin hn, A.sq_singularValues_fin hn]
  exact LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le
    Â.isSymmetric_adjoint_comp_self
    A.isSymmetric_adjoint_comp_self hn
    (fun x => by
      simpa only [add_comm â a] using
        LinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_apply_le Â A hÂ hA hE x) k



/-! ### Singular values of the adjoint (square case)

`σ(A⋆) = σ(A)` for a square operator `A : E →ₗ[𝕜] E`.  The Gram operators
`A⋆A` and `A A⋆` are unitarily conjugate (`A A⋆ = U (A⋆A) U⁻¹` with
`U = choosePolarUnitary A`), so they have equal sorted eigenvalues, hence `A` and
`A⋆` have equal singular values.  This is the symmetry `cosPrincipalAngles`
needs (plan step W0.1(d)).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SingularSubspace`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `29506b0`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

section Adjoint

variable {n : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The conjugate `U S U⁻¹` of a symmetric operator by a unitary is symmetric. -/
theorem isSymmetric_conj_unitary {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric) (U : E ≃ₗᵢ[𝕜] E) :
    (U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  calc ⟪U (S (U.symm x)), y⟫_𝕜
      = ⟪U (S (U.symm x)), U (U.symm y)⟫_𝕜 := by rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪S (U.symm x), U.symm y⟫_𝕜 := U.inner_map_map _ _
    _ = ⟪U.symm x, S (U.symm y)⟫_𝕜 := hS _ _
    _ = ⟪U (U.symm x), U (S (U.symm y))⟫_𝕜 := (U.inner_map_map _ _).symm
    _ = ⟪x, U (S (U.symm y))⟫_𝕜 := by rw [LinearIsometryEquiv.apply_symm_apply]

/-- One direction of unitary-conjugation eigenvalue invariance:
`λₖ(S) ≤ λₖ(U S U⁻¹)`.  Courant–Fischer — a witness `(k+1)`-subspace for `S`
maps under `U` to one for the conjugate, on which the same Rayleigh values
recur. -/
private theorem eigenvalues_conj_unitary_le {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (U : E ≃ₗᵢ[𝕜] E) (k : Fin n) :
    hS.eigenvalues hn k ≤ (isSymmetric_conj_unitary hS U).eigenvalues hn k := by
  obtain ⟨V, hVdim, hVlow⟩ :=
    LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner hS hn k
  have hmapfin : finrank 𝕜 (V.map U.toLinearMap) = (k : ℕ) + 1 := by
    rw [show (U.toLinearMap : E →ₗ[𝕜] E) = (U.toLinearEquiv : E →ₗ[𝕜] E) from rfl,
      LinearEquiv.finrank_map_eq, hVdim]
  obtain ⟨y, hyV', hny, hup⟩ := LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue
    (isSymmetric_conj_unitary hS U) hn k (V.map U.toLinearMap) hmapfin
  obtain ⟨x, hxV, hUxy⟩ := Submodule.mem_map.mp hyV'
  simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hUxy
  have hnx : ‖x‖ = 1 := by rw [← hny, ← hUxy, U.norm_map]
  have hyx : U.symm y = x := by rw [← hUxy, U.symm_apply_apply]
  have hray : RCLike.re ⟪(U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap) y, y⟫_𝕜
      = RCLike.re ⟪S x, x⟫_𝕜 := by
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
    rw [hyx, ← hUxy, U.inner_map_map]
  calc hS.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
    _ = RCLike.re ⟪(U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap) y, y⟫_𝕜 := hray.symm
    _ ≤ (isSymmetric_conj_unitary hS U).eigenvalues hn k := hup

/-- **Unitary conjugation preserves sorted eigenvalues.** For a symmetric
operator `S` and a unitary `U`, `S` and `U S U⁻¹` have the same sorted
eigenvalues.  (Courant–Fischer: the Rayleigh minimax is invariant under the
subspace bijection `V ↦ U V`.) -/
theorem eigenvalues_conj_unitary {S : E →ₗ[𝕜] E} (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (U : E ≃ₗᵢ[𝕜] E) :
    (isSymmetric_conj_unitary hS U).eigenvalues hn = hS.eigenvalues hn := by
  funext k
  refine le_antisymm ?_ (eigenvalues_conj_unitary_le hS hn U k)
  -- Reverse direction: `S` is the conjugate of `U S U⁻¹` by `U⁻¹`.
  have hback : U.symm.toLinearMap ∘ₗ (U.toLinearMap ∘ₗ S ∘ₗ U.symm.toLinearMap)
      ∘ₗ U.symm.symm.toLinearMap = S := by
    ext v
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  have hcong := LinearMap.IsSymmetric.eigenvalues_congr hback
    (isSymmetric_conj_unitary (isSymmetric_conj_unitary hS U) U.symm) hS hn
  have := eigenvalues_conj_unitary_le (isSymmetric_conj_unitary hS U) hn U.symm k
  rwa [hcong] at this

/-- The Gram operators `A A⋆` and `A⋆A` are unitarily conjugate:
`A A⋆ = U (A⋆A) U⁻¹` with `U = choosePolarUnitary A`.  From `A = U |A|`,
`A⋆ = |A| U⁻¹`, so `A A⋆ = U |A|² U⁻¹ = U (A⋆A) U⁻¹`. -/
theorem comp_adjoint_eq_conj_adjoint_comp (A : E →ₗ[𝕜] E) :
    A ∘ₗ A.adjoint = (choosePolarUnitary A).toLinearMap ∘ₗ (A.adjoint ∘ₗ A)
      ∘ₗ (choosePolarUnitary A).symm.toLinearMap := by
  set U := choosePolarUnitary A with hU
  have hpolar : A = U.toLinearMap ∘ₗ A.operatorAbs := polar_decomposition_choosePolarUnitary A
  have hadj : A.adjoint = A.operatorAbs ∘ₗ U.symm.toLinearMap := by
    conv_lhs => rw [hpolar]
    rw [LinearMap.adjoint_comp, (A.isPositive_operatorAbs).adjoint_eq,
      U.adjoint_toLinearMap_eq_symm]
  calc A ∘ₗ A.adjoint
      = (U.toLinearMap ∘ₗ A.operatorAbs) ∘ₗ (A.operatorAbs ∘ₗ U.symm.toLinearMap) := by
        rw [← hpolar, ← hadj]
    _ = U.toLinearMap ∘ₗ (A.operatorAbs ∘ₗ A.operatorAbs) ∘ₗ U.symm.toLinearMap := by
        ext v; simp only [LinearMap.comp_apply]
    _ = U.toLinearMap ∘ₗ (A.adjoint ∘ₗ A) ∘ₗ U.symm.toLinearMap := by
      rw [LinearMap.operatorAbs_sq A]

end Adjoint

end TauCeti
