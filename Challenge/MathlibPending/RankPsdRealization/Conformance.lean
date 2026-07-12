/-
# Rank-controlled PSD Gram realization (pending: only the rank-control is novel)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib.Matrix

open scoped BigOperators ComplexOrder
open Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Vanishing tail of the sorted eigenvalues** of a PSD matrix of rank `≤ d`. -/
theorem PosSemidef.eigenvalues₀_eq_zero_of_le {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) {d : ℕ} (hrank : B.rank ≤ d)
    (i : Fin (Fintype.card n)) (hi : d ≤ (i : ℕ)) :
    hB.isHermitian.eigenvalues₀ i = 0 := by
  set hH := hB.isHermitian
  -- The index equivalence `eigenvalues₀ = eigenvalues ∘ e` from the definition.
  set e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) with he
  have heq0 : ∀ k, hH.eigenvalues₀ k = hH.eigenvalues (e k) := by
    intro k
    rw [Matrix.IsHermitian.eigenvalues, he, Equiv.symm_apply_apply]
  -- PSD ⇒ sorted eigenvalues are nonnegative.
  have hnonneg : ∀ k, 0 ≤ hH.eigenvalues₀ k := fun k => by
    rw [heq0 k]; exact hB.eigenvalues_nonneg (e k)
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
  have hcount : (Finset.univ.filter (fun k => hH.eigenvalues₀ k ≠ 0)).card = B.rank := by
    have h1 : (Finset.univ.filter (fun k => hH.eigenvalues₀ k ≠ 0)).card
        = Fintype.card {k // hH.eigenvalues₀ k ≠ 0} := (Fintype.card_subtype _).symm
    have h2 : Fintype.card {k // hH.eigenvalues₀ k ≠ 0}
        = Fintype.card {j // hH.eigenvalues j ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquiv e fun k => by rw [heq0 k])
    rw [h1, h2, ← hH.rank_eq_card_non_zero_eigs]
  rw [hcount] at hcard_le
  omega

end ForMathlib.Matrix

namespace ForMathlib.Matrix

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- **Rank-controlled PSD Gram realization.** -/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  sorry

end ForMathlib.Matrix
