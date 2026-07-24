/-
TRANSITIONAL COMPATIBILITY SHIM — NOT an upstream candidate.

The Wave-1 CourantFischer dedup deleted the ForMathlib original after the
canonical ForTauCeti API was redesigned per the signature-polish backlog
(`OrthonormalBasis.spanIndices` + `LinearMap.IsSymmetric`-namespace eigenvalue
results + `TauCeti.abs_eigenvalue_sub_eigenvalue_le*`).  The many downstream
consumers still use the historical predicate-based signatures; this file keeps
them compiling as thin wrappers over the canonical API so the dedup commit
does not have to rewrite dozens of paper-layer proofs at once.

Delete each wrapper once its downstream users have migrated to the canonical
name (tracked by the migration name map in
`dev/tauceti/formathlib-to-fortauceti-migration.md`).  Nothing here may be
exported to Tau Ceti.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CourantFischer

@[expose] public section

namespace TauCeti

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- Historical predicate-based basis-subfamily span.  Canonical form:
`OrthonormalBasis.spanIndices`. -/
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  b.spanIndices {i | p i}

/-- Historical form of `OrthonormalBasis.finrank_spanIndices`. -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace, b.finrank_spanIndices_set, Set.toFinset_setOf]

/-- Historical form of `OrthonormalBasis.orthogonal_spanIndices`. -/
theorem orthogonal_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    (specSubspace b p)ᗮ = specSubspace b (fun i => ¬ p i) := by
  rw [specSubspace, specSubspace, b.orthogonal_spanIndices, Set.compl_setOf]

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- Historical name for
`LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq`. -/
theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 :=
  hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hn x

/-- Historical predicate form of
`LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices`. -/
theorem re_inner_map_self_le_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
  hT.re_inner_apply_self_le_of_mem_spanIndices hn (fun i hi => hc i hi) hx

/-- Historical predicate form of
`LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices`. -/
theorem le_re_inner_map_self_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
  hT.le_re_inner_apply_self_of_mem_spanIndices hn (fun i hi => hc i hi) hx

/-- Historical name for
`LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue`. -/
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k :=
  hT.exists_unit_vector_re_inner_le_eigenvalue hn k V hV

/-- Historical (quantifier-misstating) name for
`LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner`. -/
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
  hT.exists_submodule_forall_unit_eigenvalue_le_re_inner hn k

/-- Historical name for `TauCeti.abs_eigenvalue_sub_eigenvalue_le`. -/
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε :=
  abs_eigenvalue_sub_eigenvalue_le hT hS hn hε k

/-- Historical `toContinuousLinearMap` form of
`TauCeti.abs_eigenvalue_sub_eigenvalue_le_norm`. -/
theorem abs_eigenvalues_sub_le_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  refine abs_eigenvalues_sub_le hT hS hn (fun x => ?_) k
  have hx := (LinearMap.toContinuousLinearMap (T - S)).le_opNorm x
  rwa [LinearMap.coe_toContinuousLinearMap'] at hx

omit [FiniteDimensional 𝕜 E] in
/-- Historical name for
`LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_of_eigenbasis`. -/
theorem re_inner_map_self_eq_sum_of_eigenbasis
    (hS : S.IsSymmetric) (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ}
    (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) (x : E) :
    RCLike.re ⟪S x, x⟫_𝕜 = ∑ i : Fin n, μ i * ‖w.repr x i‖ ^ 2 :=
  hS.re_inner_apply_self_eq_sum_of_eigenbasis w hw x

/-- Historical name for `LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis`. -/
theorem eigenvalues_eq_of_eigenbasis
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (w : OrthonormalBasis (Fin n) 𝕜 E)
    {μ : Fin n → ℝ} (hμ : Antitone μ) (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) :
    hS.eigenvalues hn = μ :=
  hS.eigenvalues_eq_of_eigenbasis hn w hμ hw

/-- Historical name for `LinearMap.IsSymmetric.eigenvalue_mono`. -/
theorem eigenvalues_le_eigenvalues_of_re_inner_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (h : ∀ x, RCLike.re ⟪T x, x⟫_𝕜 ≤ RCLike.re ⟪S x, x⟫_𝕜) (k : Fin n) :
    hT.eigenvalues hn k ≤ hS.eigenvalues hn k :=
  hT.eigenvalue_mono hS hn h k

/-- Historical predicate form of `LinearMap.IsSymmetric.map_mem_spanIndices`. -/
theorem map_mem_specSubspace (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (p : Fin n → Prop) {x : E}
    (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    T x ∈ specSubspace (hT.eigenvectorBasis hn) p :=
  hT.map_mem_spanIndices hn {i | p i} hx

end TauCeti

end
