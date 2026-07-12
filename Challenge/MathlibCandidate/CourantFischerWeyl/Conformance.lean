/-
# Weyl eigenvalue perturbation, via Courant-Fischer min-max (Mathlib candidate 02)

The surfaced leaf is Weyl's perturbation inequality; the discrete Courant-Fischer
min-max characterization is the proof vehicle (developed in
`ForMathlib.Analysis.InnerProductSpace.CourantFischer`), not a separately listed leaf.

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

/-- The subspace spanned by the orthonormal basis vectors `b i` for `p i`. -/
noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

/-- A spectral subspace has dimension equal to the number of selected indices. -/
theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]

/-- A vector in a spectral subspace has zero `b`-coordinate outside the predicate. -/
private theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E)
    (p : Fin n → Prop) {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi j.2
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

/-- Parseval for the coordinate norms. -/
private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

/-- The quadratic form of a symmetric operator in its eigenbasis. -/
theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ⟪T x, x⟫_𝕜
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

/-- On a spectral subspace, the quadratic form is bounded above by a bound on the
selected eigenvalues. -/
theorem re_inner_map_self_le_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp

/-- Dual: on a spectral subspace, a lower bound on the selected eigenvalues bounds the
quadratic form below. -/
theorem le_re_inner_map_self_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp

/-- Counting lemma: `#{i : k ≤ i} = n - k`. -/
private theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  have : (Finset.univ.filter (fun i : Fin n => k ≤ i)).card
      = (Finset.Ici k).card := by
    congr 1
    ext i
    simp [Finset.mem_Ici]
  rw [this, Fin.card_Ici]

/-- Counting lemma: `#{i : i ≤ k} = k + 1`. -/
private theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  have : (Finset.univ.filter (fun i : Fin n => i ≤ k)).card
      = (Finset.Iic k).card := by
    congr 1
    ext i
    simp [Finset.mem_Iic]
  rw [this, Fin.card_Iic]

/-- **Courant–Fischer, upper direction.** -/
theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : finrank 𝕜 V = (k : ℕ) + 1) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := specSubspace b (fun i : Fin n => k ≤ i) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_specSubspace, card_filter_le]
  have hsum : finrank 𝕜 V + finrank 𝕜 W = n + 1 := by
    rw [hV, hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hle := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero] at hle
    have hsup : finrank 𝕜 (↑(V ⊔ W) : Submodule 𝕜 E) ≤ n := by
      rw [← hn]; exact Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩
  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        re_inner_map_self_le_of_mem_specSubspace hT hn
          (fun _ hik => hT.eigenvalues_antitone hn hik) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

/-- **Courant–Fischer, lower direction.** -/
theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨specSubspace b (fun i : Fin n => i ≤ k), ?_, ?_⟩
  · rw [finrank_specSubspace, card_filter_ge]
  · intro x hxV hnx
    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
          le_re_inner_map_self_of_mem_specSubspace hT hn
            (fun _ hik => hT.eigenvalues_antitone hn hik) hxV

/-- One-sided Weyl bound. -/
private theorem eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    hS.eigenvalues hn k - hT.eigenvalues hn k ≤ ε := by
  obtain ⟨V, hVdim, hVlow⟩ := forall_unit_vector_eigenvalue_le_re_inner hS hn k
  obtain ⟨x, hxV, hnx, hTup⟩ := exists_unit_vector_re_inner_le_eigenvalue hT hn k V hVdim
  have hSlow : hS.eigenvalues hn k ≤ RCLike.re ⟪S x, x⟫_𝕜 := hVlow x hxV hnx
  have hdiff : RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜
      = RCLike.re ⟪(S - T) x, x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_left, map_sub]
  have hcs : RCLike.re ⟪(S - T) x, x⟫_𝕜 ≤ ‖(S - T) x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hbnd : ‖(S - T) x‖ * ‖x‖ ≤ ε := by
    have := hε x
    rwa [hnx, mul_one] at this ⊢
  calc hS.eigenvalues hn k - hT.eigenvalues hn k
      ≤ RCLike.re ⟪S x, x⟫_𝕜 - RCLike.re ⟪T x, x⟫_𝕜 := by linarith
    _ = RCLike.re ⟪(S - T) x, x⟫_𝕜 := hdiff
    _ ≤ ‖(S - T) x‖ * ‖x‖ := hcs
    _ ≤ ε := hbnd

/-- **Weyl's inequality**, quadratic-form-bound hypothesis. -/
theorem abs_eigenvalues_sub_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ε : ℝ} (hε : ∀ x : E, ‖(T - S) x‖ ≤ ε * ‖x‖) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k| ≤ ε := by
  have hεsymm : ∀ x : E, ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (S - T) x = -((T - S) x) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  rw [abs_le]
  constructor
  · have := eigenvalues_sub_le hT hS hn hεsymm k
    linarith
  · have := eigenvalues_sub_le hS hT hn hε k
    linarith

/-- **Weyl's inequality (operator-norm form).** The `k`-th sorted eigenvalues of two
symmetric operators differ by at most the operator norm of their difference. This is the
leaf of the Courant-Fischer + Weyl development (it is proved through the discrete
Courant-Fischer min-max characterization of the sorted eigenvalues). -/
theorem abs_eigenvalues_sub_le_opNorm (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) (k : Fin n) :
    |hT.eigenvalues hn k - hS.eigenvalues hn k|
      ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  refine abs_eigenvalues_sub_le hT hS hn (fun x => ?_) k
  have hx := (LinearMap.toContinuousLinearMap (T - S)).le_opNorm x
  rwa [LinearMap.coe_toContinuousLinearMap'] at hx

end ForMathlib
