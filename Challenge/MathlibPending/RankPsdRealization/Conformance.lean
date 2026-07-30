/-
# Rank-controlled PSD Gram realization (pending: only the rank-control is novel)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/

import Mathlib

/-!
## Comparator maintenance rule

The proof holes in this module are deliberate challenge placeholders. Do not
discharge them in this repository and do not count them as formalization debt.
Implementations belong in the project modules imported by the paired
`Leaderboard.lean`; Comparator verifies that those implementations match these
statements and use only the permitted kernel dependencies.
-/


namespace TauCeti.Matrix

open scoped BigOperators ComplexOrder
open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Vanishing tail of the sorted eigenvalues** of a PSD matrix of rank `≤ d`. -/
theorem PosSemidef.eigenvalues₀_eq_zero_of_rank_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {d : ℕ} (hrank : A.rank ≤ d)
    {i : Fin (Fintype.card n)} (hi : d ≤ (i : ℕ)) :
    hA.isHermitian.eigenvalues₀ i = 0 := by
  set hH := hA.isHermitian
  -- The index equivalence `eigenvalues₀ = eigenvalues ∘ e` from the definition.
  set e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with he
  have heq0 : ∀ k, hH.eigenvalues₀ k = hH.eigenvalues (e k) := by
    intro k
    rw [Matrix.IsHermitian.eigenvalues, he, Equiv.symm_apply_apply]
  -- PSD ⇒ sorted eigenvalues are nonnegative.
  have hnonneg : ∀ k, 0 ≤ hH.eigenvalues₀ k := fun k => by
    rw [heq0 k]; exact hA.eigenvalues_nonneg (e k)
  by_contra hne
  have hipos : 0 < hH.eigenvalues₀ i := (hnonneg i).lt_of_ne' hne
  -- By antitonicity, every index `≤ i` also has a strictly positive eigenvalue.
  have hpos_le : ∀ k, k ≤ i → 0 < hH.eigenvalues₀ k := fun k hk =>
    lt_of_lt_of_le hipos (hH.eigenvalues₀_antitone hk)
  -- The `i + 1` leading indices all lie in the nonzero-eigenvalue Finset.
  have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun k => hH.eigenvalues₀ k ≠ 0) :=
    fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ne_of_gt (hpos_le k (Finset.mem_Iic.mp hk))⟩
  have hcard_le : (i : ℕ) + 1 ≤ (Finset.univ.filter (fun k => hH.eigenvalues₀ k ≠ 0)).card := by
    calc (i : ℕ) + 1 = (Finset.Iic i).card := by rw [Fin.card_Iic]
      _ ≤ _ := Finset.card_le_card hsub
  -- That Finset has cardinality `rank` (count transported across `e`).
  have hcount : (Finset.univ.filter (fun k => hH.eigenvalues₀ k ≠ 0)).card = A.rank := by
    have h1 : (Finset.univ.filter (fun k => hH.eigenvalues₀ k ≠ 0)).card
        = Fintype.card {k // hH.eigenvalues₀ k ≠ 0} := (Fintype.card_subtype _).symm
    have h2 : Fintype.card {k // hH.eigenvalues₀ k ≠ 0}
        = Fintype.card {j // hH.eigenvalues j ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquiv e fun k => by rw [heq0 k])
    rw [h1, h2, ← hH.rank_eq_card_non_zero_eigs]
  rw [hcount] at hcard_le
  omega

end TauCeti.Matrix

namespace TauCeti.Matrix.RankFactorizationAux

open Module (finrank)
open _root_.Matrix

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

/-- Rank factorization (exact): every matrix factors as `M = L * R` with inner
dimension `Fin M.rank`. -/
theorem exists_eq_mul_rank (M : Matrix m n 𝕜) :
    ∃ (L : Matrix m (Fin M.rank) 𝕜) (R : Matrix (Fin M.rank) n 𝕜), M = L * R := by
  have hdim : finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank := rfl
  let b : Module.Basis (Fin M.rank) 𝕜 (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq 𝕜 _ hdim
  have hcol : ∀ j : n, (fun i => M i j) ∈ LinearMap.range M.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨fun i k => (b k : m → 𝕜) i, fun k j => b.repr ⟨_, hcol j⟩ k, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  have hrepr := congrArg Subtype.val (b.sum_repr ⟨_, hcol j⟩)
  rw [Submodule.coe_sum] at hrepr
  have := congrFun hrepr i
  simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Finset.sum_congr rfl fun k _ => mul_comm ((b k : m → 𝕜) i) (b.repr ⟨_, hcol j⟩ k)]
  exact this.symm

/-- Rank factorization (padded to `Fin r` for any `M.rank ≤ r`). -/
theorem exists_eq_mul_of_rank_le (M : Matrix m n 𝕜) {r : ℕ} (h : M.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  obtain ⟨L₀, R₀, hM⟩ := exists_eq_mul_rank M
  refine ⟨fun i k => if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0,
    fun k j => if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0, ?_⟩
  ext i j
  set f : ℕ → 𝕜 := fun k => if hk : k < M.rank then L₀ i ⟨k, hk⟩ * R₀ ⟨k, hk⟩ j else 0 with hf
  have hpad : ∀ k : Fin r,
      (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
        * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0) = f (k : ℕ) := by
    intro k
    by_cases hk : (k : ℕ) < M.rank <;> simp [hf, hk]
  have hexact : ∀ k : Fin M.rank, L₀ i k * R₀ k j = f (k : ℕ) := by
    intro k
    simp [hf, k.isLt]
  have hsum : (∑ k : Fin r,
        (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
          * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0))
      = ∑ k : Fin M.rank, L₀ i k * R₀ k j := by
    rw [Finset.sum_congr rfl fun k _ => hpad k, Fin.sum_univ_eq_sum_range f r,
      Finset.sum_congr rfl fun k _ => hexact k, Fin.sum_univ_eq_sum_range f M.rank]
    refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le h))
      fun k _ hk => dif_neg (by simpa using hk)).symm
  rw [Matrix.mul_apply, hsum, ← Matrix.mul_apply, ← hM]

end TauCeti.Matrix.RankFactorizationAux

namespace TauCeti.Matrix

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Entrywise spectral expansion of a Hermitian matrix. -/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  have hspec := hB.spectral_theorem
  have hentry : B i j =
      (hB.eigenvectorUnitary *
        (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜))) i j := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply]
    simp [mul_assoc]
  rw [hentry, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply]
  have hdiag : ∑ l : Fin n,
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) k l *
        (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) l j
      = (hB.eigenvalues k : 𝕜) * conj (hB.eigenvectorUnitary j k) := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, Matrix.star_apply, RCLike.star_def]
      rfl
    · intro l _ hl
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hdiag]; ring

/-- Square PSD factorization: `B = Aᴴ * A` with `A` square. -/
theorem PosSemidef.exists_eq_conjTranspose_mul_self
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) :
    ∃ A : Matrix (Fin n) (Fin n) 𝕜, B = Aᴴ * A := by
  have hHerm : B.IsHermitian := hB.1
  refine ⟨fun k i =>
    (Real.sqrt (hHerm.eigenvalues k) : 𝕜) * conj (hHerm.eigenvectorUnitary i k), ?_⟩
  ext i j
  rw [Matrix.mul_apply, isHermitian_entry_eq_sum_eigenvalues B hHerm i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def]
  have hnn : 0 ≤ hHerm.eigenvalues k := _root_.Matrix.PosSemidef.eigenvalues_nonneg hB k
  simp only [map_mul, RCLike.conj_ofReal, RCLike.conj_conj]
  rw [show RCLike.ofReal (Real.sqrt (hHerm.eigenvalues k)) * hHerm.eigenvectorUnitary i k *
      ((Real.sqrt (hHerm.eigenvalues k) : 𝕜) * conj (hHerm.eigenvectorUnitary j k))
    = ((Real.sqrt (hHerm.eigenvalues k) : 𝕜) * (Real.sqrt (hHerm.eigenvalues k) : 𝕜))
        * (hHerm.eigenvectorUnitary i k * conj (hHerm.eigenvectorUnitary j k)) from by ring]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hnn]
  ring

/-- Rank-controlled PSD factorization, forward direction. -/
theorem PosSemidef.exists_conjTranspose_mul_self_of_rank_le
    {d : ℕ} {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) (hrank : B.rank ≤ d) :
    ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  obtain ⟨A₀, hA₀⟩ := PosSemidef.exists_eq_conjTranspose_mul_self hB
  have hrankA₀ : A₀.rank ≤ d := by
    rwa [hA₀, rank_conjTranspose_mul_self] at hrank
  obtain ⟨L, R, hLR⟩ := TauCeti.Matrix.RankFactorizationAux.exists_eq_mul_of_rank_le A₀ hrankA₀
  obtain ⟨S, hS⟩ :=
    PosSemidef.exists_eq_conjTranspose_mul_self (posSemidef_conjTranspose_mul_self L)
  refine ⟨S * R, ?_⟩
  calc B = A₀ᴴ * A₀ := hA₀
    _ = Rᴴ * (Lᴴ * L) * R := by
        rw [hLR, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Rᴴ * (Sᴴ * S) * R := by rw [← hS]
    _ = (S * R)ᴴ * (S * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]

/-- **Rank-controlled PSD Gram realization.** -/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  refine ⟨fun h => PosSemidef.exists_conjTranspose_mul_self_of_rank_le h.1 h.2, ?_⟩
  rintro ⟨A, rfl⟩
  refine ⟨posSemidef_conjTranspose_mul_self A, ?_⟩
  rw [rank_conjTranspose_mul_self]
  exact A.rank_le_height

end TauCeti.Matrix
