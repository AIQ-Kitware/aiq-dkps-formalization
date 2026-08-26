/-
Configuration-assembly step of the DKPS finite-sample concentration bridge
(WP7(c4) of `planning/acharyya-plan.md`): the *final* spectral-bridge theorem.

Given a population symmetric operator `T` on `EuclideanSpace ℝ (Fin n)` whose
leading `d` (sorted) eigenvalues are `≥ α > 0` with all trailing eigenvalues `0`
(the doubly-centered CMDS Gram operator, rank `d`, spectral floor `α`, top
eigenvalue `≤ Λ`), and a sample symmetric operator `S` that is `ε`-close in
operator norm, the *spectral embeddings*
`ψ̂ := spectralConfig S`, `ψ := spectralConfig T`
(the classical MDS coordinates `√λ̂_k · v_k(i)` and `√λ_l · u_l(i)`) are close
*up to a linear isometry* `W`:
a Frobenius configuration error bound with an explicit closed form in
`d, α, Λ, ε`.  The legacy `ConfigError` theorem is retained as a compatibility
corollary and pays the expected Cauchy--Schwarz factor `√n`.

The proof is coordinatewise and reuses the spectral toolkit built in this
session:

* `Acharyya2025.Weyl` (Weyl perturbation and eigenbasis Parseval),
* `YuWangSamworth2015.Core.Residual` and `.Procrustes` (population-gap
  cross-energy and global Procrustes alignment),
* `Acharyya2025.Overlap` (overlap matrix `Q`, commutator identity,
  `QᵀQ − I` deviation bound),
* `ForTauCeti.Analysis.InnerProductSpace.NearIsometry` for the local alignment
  branch.

The three-term decomposition `ψ̂W − ψ = Term1 + Term2 + Term3` is:

* `Term1 = (W − M) ψ̂` where `M := toEuclideanLin Qᵀ` is the near-isometry whose
  Gram deviation `QᵀQ − I` is small; local alignment uses the sharp TauCeti
  near-isometry theorem and the complementary regime uses YWS Procrustes;
* `Term2 = M ψ̂ − (the QΛ^{1/2}-rescaled vector)` — the commutator term, each
  entry `Q_{kl}(√λ̂_k − √λ_l)` controlled by the Sylvester identity;
* `Term3` — the population reconstruction defect `√λ_l(Σ_k Q_{kl} v_k − u_l)`,
  controlled by the YWS population-gap cross energy.

Frobenius triangle inequality (`norm_add_le` on `EuclideanSpace ℝ (Fin n × Fin d)`)
combines the three.  The paper-facing deterministic theorem stops at this
Frobenius bound; `ConfigError ≤ √n · ‖·‖_F` is used only by the compatibility
corollary consumed by older downstream code.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2024.Common
import Acharyya2025.Weyl
import Acharyya2025.Overlap
import ForTauCeti.Analysis.InnerProductSpace.NearIsometry
import YuWangSamworth2015.Core.Residual
import YuWangSamworth2015.Core.Procrustes

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix
open Module (finrank)

namespace Acharyya2025.ConfigPerturbation

/-! ### The spectral configuration (classical MDS embedding) -/

/-- The **spectral embedding / CMDS configuration** of a symmetric operator `S`:
the `i`-th point has `k`-th coordinate `√λ̂_k · v_k(i)`, where `v_k` is the
`k`-th sample eigenvector and `λ̂_k` the `k`-th (decreasingly sorted) eigenvalue.
`Real.sqrt` clamps negative eigenvalues to `0` (the CMDS convention).  The
main theorem does not require the sample top-`d` eigenvalues to stay positive;
the square-root and sample-energy arguments explicitly accommodate clamping.

Paper correspondence: this is the classical-MDS embedding `ψ̂` (when `S` is the
sample Gram operator) or `ψ` (when `S` is the population Gram operator) appearing
in Theorem 2. It is a plain definition, not a claim. -/
noncomputable def spectralConfig {n d : ℕ}
    (S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.IsSymmetric) (hd : d ≤ n) : Acharyya2024.Config n d :=
  fun i => WithLp.toLp 2 (fun k =>
    Real.sqrt (hS.eigenvalues finrank_euclideanSpace_fin (Fin.castLE hd k))
      * hS.eigenvectorBasis finrank_euclideanSpace_fin (Fin.castLE hd k) i)

variable {n d : ℕ}
variable {T S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)}

/-- Internal helper / bookkeeping fact: the dimension of `EuclideanSpace ℝ (Fin n)`
is `n`. This is a Lean-specific witness threaded through the eigenvalue/eigenvector
API; it has no mathematical content in the paper. -/
private theorem hn_eq : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin

/-- Internal helper / purely combinatorial reindexing (`Overlap`'s is private):
summing `f` over the image of the inclusion `Fin d ↪ Fin n` equals summing over
the first `d` indices `{ j : (j:ℕ) < d }`. No mathematical content from the paper. -/
private theorem sum_castLE_eq_filter (hd : d ≤ n) (f : Fin n → ℝ) :
    -- Conclusion: the two indexings of the leading `d`-block give the same sum.
    ∑ m : Fin d, f (Fin.castLE hd m)
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < d), f j := by
  refine Finset.sum_bij'
    (fun (m : Fin d) _ => Fin.castLE hd m)
    (fun (j : Fin n) hj => ⟨(j : ℕ), (Finset.mem_filter.mp hj).2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro m _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Fin.castLE]⟩
  · intro j _; exact Finset.mem_univ _
  · intro m _; apply Fin.ext; simp [Fin.castLE]
  · intro j _; apply Fin.ext; simp [Fin.castLE]
  · intro m _; rfl

/-! ### Step 1: Weyl upper control in the top block

Only the upper sample-eigenvalue bound is needed by the active proof.  No lower
sample-eigenvalue bound is required: negative sample eigenvalues are handled by
`Real.sqrt` clamping, and the cross-energy estimates use the population-only YWS
gap instead of manufacturing a sample gap.
-/

/-- Internal helper (Weyl, upper bound). The sample top-block eigenvalues satisfy
`λ̂_k ≤ Λ + ε`. This is the only per-sample-eigenvalue Weyl bound needed by
the active configuration proof.

Hypotheses:
* `hΛ` — eigenvalue cap `Λ` on all population eigenvalues (the paper's `λ_1` upper
  bound, the `C2` side of Assumption 2).
* `hε` — sample/population operator-norm closeness. -/
private theorem sample_eig_ub (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {Λ ε : ℝ}
    (hΛ : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin d) :
    -- Conclusion: the `k`-th leading sample eigenvalue is at most `Λ + ε`.
    hS.eigenvalues hn_eq (Fin.castLE hd k) ≤ Λ + ε := by
  have hε' : ∀ x, ‖(T - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    have : (T - S) x = -((S - T) x) := by rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel
    rw [this, norm_neg]; exact hε x
  have hweyl := Acharyya2025.Weyl.abs_eigenvalues_sub_le hT hS hn_eq hε' (Fin.castLE hd k)
  rw [abs_le] at hweyl
  linarith [hweyl.1, hΛ (Fin.castLE hd k)]

/-! ### Step 2a: population-gap YWS cross-energy bounds

Yu--Wang--Samworth controls the leading-sample / trailing-population cross energy
directly from the population eigengap.  Principal-angle symmetry transfers the
same bound to the opposite orientation.  This route uses no lower bound on the
sample eigenvalues and no `ε ≤ α/2` side condition.
-/

/-- The leading index filter has exactly `d` elements when `d ≤ n`. -/
private theorem leading_filter_card (hd : d ≤ n) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < d)).card = d := by
  let e : Fin d ↪ Fin n := Fin.castLEEmb hd
  have heq : Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) =
      Finset.univ.map e := by
    ext i
    constructor
    · intro hi
      have hilt : (i : ℕ) < d := (Finset.mem_filter.mp hi).2
      apply Finset.mem_map.mpr
      refine ⟨⟨(i : ℕ), hilt⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, _hj, hji⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hji]
      exact j.isLt
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The complement of the leading filter is the trailing filter. -/
private theorem leading_filter_compl :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < d))ᶜ =
      Finset.univ.filter (fun i : Fin n => d ≤ (i : ℕ)) := by
  ext i
  simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- YWS population-gap bound for the leading-sample / trailing-population
cross energy.  It uses only the population spectral floor/tail separation, so no
sample-eigenvalue lower bound or perturbative smallness side condition enters. -/
private theorem crossSamp_yws_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2
      ≤ 4 * (d : ℝ) * ε^2 / α^2 := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < d)
  have hscard : s.card = d := by
    dsimp [s]
    exact leading_filter_card (n := n) (d := d) hd
  have hscompl : sᶜ = Finset.univ.filter (fun i : Fin n => d ≤ (i : ℕ)) := by
    dsimp [s]
    exact leading_filter_compl (n := n) (d := d)
  have hgap : ∀ j ∈ s, ∀ k ∉ s,
      α ≤ |hT.eigenvalues hn_eq j - hT.eigenvalues hn_eq k| := by
    intro j hj k hk
    have hjlt : (j : ℕ) < d := by
      change j ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) at hj
      exact (Finset.mem_filter.mp hj).2
    have hknot : ¬ (k : ℕ) < d := by
      intro hklt
      apply hk
      change k ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hklt⟩
    have hkge : d ≤ (k : ℕ) := by omega
    have hjlb := hα j hjlt
    have hj0 : 0 ≤ hT.eigenvalues hn_eq j :=
      le_trans (le_of_lt hα_pos) hjlb
    rw [htail k hkge, sub_zero, abs_of_nonneg hj0]
    exact hjlb
  have hyws :=
    YuWangSamworth2015.sq_gap_mul_sum_cross_le_of_population_gap_opNorm
      hT hS hn_eq s hα_pos.le hgap hε
  have hsum :
      (∑ i ∈ s, ∑ j ∈ sᶜ,
          ‖⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq i⟫_ℝ‖^2) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
    rw [hscompl]
    change
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            ‖⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq i⟫_ℝ‖^2) = _
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_comm]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hsum, hscard] at hyws
  have hαsq : 0 < α^2 := by positivity
  rw [le_div_iff₀ hαsq]
  simpa [mul_comm] using hyws

/-- The two directed cross energies of equal-dimensional blocks agree. -/
private theorem crossPop_eq_crossSamp (hd : d ≤ n)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2) =
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < d)
  have hscard : s.card = d := by
    dsimp [s]
    exact leading_filter_card (n := n) (d := d) hd
  have hscompl : sᶜ = Finset.univ.filter (fun i : Fin n => d ≤ (i : ℕ)) := by
    dsimp [s]
    exact leading_filter_compl (n := n) (d := d)
  calc
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2)
        = ∑ i ∈ s, ∑ j ∈ sᶜ,
            ‖⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq i⟫_ℝ‖^2 := by
          rw [hscompl]
          change _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)), _
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [real_inner_comm]
          simp [Real.norm_eq_abs, sq_abs]
    _ = TauCeti.sinThetaSq
          (TauCeti.orthonormal_blockFamily (hS.eigenvectorBasis hn_eq) s hscard)
          (TauCeti.orthonormal_blockFamily (hT.eigenvectorBasis hn_eq) s hscard) :=
        (TauCeti.sinThetaSq_blockFamily_eq_sum_cross
          (hS.eigenvectorBasis hn_eq) (hT.eigenvectorBasis hn_eq) hscard hscard).symm
    _ = TauCeti.sinThetaSq
          (TauCeti.orthonormal_blockFamily (hT.eigenvectorBasis hn_eq) s hscard)
          (TauCeti.orthonormal_blockFamily (hS.eigenvectorBasis hn_eq) s hscard) :=
        TauCeti.sinThetaSq_comm
          (TauCeti.orthonormal_blockFamily (hS.eigenvectorBasis hn_eq) s hscard)
          (TauCeti.orthonormal_blockFamily (hT.eigenvectorBasis hn_eq) s hscard)
    _ = ∑ i ∈ s, ∑ j ∈ sᶜ,
          ‖⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq i⟫_ℝ‖^2 :=
        TauCeti.sinThetaSq_blockFamily_eq_sum_cross
          (hT.eigenvectorBasis hn_eq) (hS.eigenvectorBasis hn_eq) hscard hscard
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
          rw [hscompl]
          change (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)), _) = _
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [real_inner_comm]
          simp [Real.norm_eq_abs, sq_abs]

/-- YWS population-gap bound for the leading-population / trailing-sample
cross energy, obtained from the opposite direction by principal-angle symmetry. -/
private theorem crossPop_yws_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2
      ≤ 4 * (d : ℝ) * ε^2 / α^2 := by
  rw [crossPop_eq_crossSamp hd hT hS]
  exact crossSamp_yws_le hd hT hS hα_pos hα htail hε

/-- Internal helper / algebraic step. A single trailing-energy column of the
`(overlap hS hT)ᵀ * (overlap hS hT)` deviation is bounded by the YWS
leading-sample / trailing-population cross energy:
`∑_{j≥d}⟪hT.basis j, hS.basis (castLE k)⟫² ≤ 4 d ε² / α²`. -/
private theorem tailS_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (k : Fin d) :
    -- Conclusion: the `k`-th trailing-energy column is `≤ 4dε²/α²`.
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2
      ≤ 4 * (d : ℝ) * ε^2 / α^2 := by
  -- Rewrite the column (with `u_j` first, `v_{castLE k}` second) into the
  -- `crossSamp` orientation (`v` leading, `u` trailing) via `real_inner_comm`.
  have hcomm : ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k), hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_comm]
  rw [hcomm]
  -- This column is the `i = castLE k` slice of `crossSamp`; bound by the whole sum.
  have hmem : (Fin.castLE hd k) ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩; simp [Fin.castLE]
  have hslice :
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k), hT.eigenvectorBasis hn_eq j⟫_ℝ)^2
        ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
              (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2 :=
    Finset.single_le_sum
      (f := fun i : Fin n => ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hS.eigenvectorBasis hn_eq i, hT.eigenvectorBasis hn_eq j⟫_ℝ)^2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) hmem
  exact le_trans hslice (crossSamp_yws_le hd hT hS hα_pos hα htail hε)

/-! ### Step 2b: the near-isometry `M` and its Gram deviation

`M := toEuclideanLin Qᵀ`, where `Q := overlap hT hS`.  Then
`(M x)_l = ∑_k Q_{kl} x_k`, and the quadratic-form deviation is governed by the
deviation matrix `QQᵀ − I = (overlap hS hT)ᵀ * (overlap hS hT) − I`, each entry
of which is `≤ τ := 4 d ε² / α²`. -/

/-- The near-isometry `M := toEuclideanLin Qᵀ`, where `Q := overlap hT hS` is the
overlap (cosine) matrix between the population and sample leading eigenbases.
`M` is the linear map whose polar factor will furnish an aligning isometry `W`
(playing the role of the paper's orthogonal `W*`; optimality/uniqueness is not
established here). It is `≈` an isometry because `Q` is `≈` orthogonal under the
rank-`d` floor; a plain definition, not a claim. -/
noncomputable def nearIsometry (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanLin (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ

/-- Internal helper / algebraic step: coordinate formula for `M`,
`(M x)_l = ∑_k Q_{kl} x_k`. -/
private theorem nearIsometry_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (x : EuclideanSpace ℝ (Fin d)) (l : Fin d) :
    -- Conclusion: the `l`-th coordinate of `M x` is the `Q`-weighted combination of `x`.
    (nearIsometry hT hS hd x) l
      = ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l * x k := by
  show ((Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ.mulVec (WithLp.ofLp x)) l = _
  rw [Matrix.mulVec_eq_sum]
  simp [mul_comm]

/-- Internal helper / algebraic step: the deviation matrix `QQᵀ` equals
`(overlap hS hT)ᵀ * (overlap hS hT)` (rewrites the Gram deviation into the form the
`Overlap` toolkit bounds). -/
private theorem dev_eq (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    -- Conclusion: the two ways of writing the overlap-Gram product agree.
    (Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
        (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
      = (Acharyya2025.Overlap.overlap hS hT hn_eq hd)ᵀ *
          (Acharyya2025.Overlap.overlap hS hT hn_eq hd) := by
  have h : Acharyya2025.Overlap.overlap hS hT hn_eq hd
      = (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ := by
    ext k l
    simp only [Acharyya2025.Overlap.overlap, Matrix.transpose_apply]
    rw [real_inner_comm]
  rw [h, Matrix.transpose_transpose]

/-- Internal helper / algebraic step (**entrywise Gram-deviation bound**). Each
entry of `QQᵀ − I` is at most `τ := 4 d ε² / α²` in absolute value. This
quantifies how close the overlap matrix `Q` is to orthogonal.  Its spectral
input is the YWS population-gap cross-energy bound (floor `α`, rank-`d` tail,
closeness `ε`). -/
private theorem abs_dev_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) (k m : Fin d) :
    -- Conclusion: each entry of the Gram deviation `QQᵀ − I` is `≤ 4dε²/α²`.
    |((Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
          (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
        - (1 : Matrix (Fin d) (Fin d) ℝ)) k m|
      ≤ 4 * (d : ℝ) * ε^2 / α^2 := by
  rw [dev_eq hT hS hd]
  -- Apply the Overlap deviation bound (swapped roles `hS hT`).
  have hbnd := Acharyya2025.Overlap.abs_overlapT_mul_overlap_sub_one_le hS hT hn_eq hd k m
  -- The two trailing-energy factors are each `≤ τ`, hence their product `≤ τ`.
  set τ : ℝ := 4 * (d : ℝ) * ε^2 / α^2 with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have htk := tailS_le hd hT hS hα_pos hα htail hε k
  have htm := tailS_le hd hT hS hα_pos hα htail hε m
  have hsk : Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2)
      ≤ Real.sqrt τ := Real.sqrt_le_sqrt htk
  have hsm : Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
        (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd m)⟫_ℝ)^2)
      ≤ Real.sqrt τ := Real.sqrt_le_sqrt htm
  calc |((Acharyya2025.Overlap.overlap hS hT hn_eq hd)ᵀ *
            (Acharyya2025.Overlap.overlap hS hT hn_eq hd)
          - (1 : Matrix (Fin d) (Fin d) ℝ)) k m|
      ≤ Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd k)⟫_ℝ)^2)
          * Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq j, hS.eigenvectorBasis hn_eq (Fin.castLE hd m)⟫_ℝ)^2) :=
        hbnd
    _ ≤ Real.sqrt τ * Real.sqrt τ :=
        mul_le_mul hsk hsm (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = τ := by rw [← Real.sqrt_mul hτ0, Real.sqrt_mul_self hτ0]

/-- Internal helper / algebraic step (**Gram-deviation identity**). The
quadratic-form deviation of `M` is the quadratic form of the deviation matrix
`D := QQᵀ − I`: `⟪M x, M x⟫ − ⟪x, x⟫ = ∑_k ∑_m D_{km} (x_k x_m)`. Pure algebra,
no hypotheses on the spectrum. -/
private theorem gram_dev_identity (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (x : EuclideanSpace ℝ (Fin d)) :
    -- Conclusion: the isometry defect of `M` at `x` is the `D`-quadratic form of `x`.
    ⟪nearIsometry hT hS hd x, nearIsometry hT hS hd x⟫_ℝ - ⟪x, x⟫_ℝ
      = ∑ k, ∑ m, ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
            (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
          - (1 : Matrix (Fin d) (Fin d) ℝ)) k m * (x k * x m) := by
  set Q := Acharyya2025.Overlap.overlap hT hS hn_eq hd with hQ
  have happly : ∀ l, (nearIsometry hT hS hd x) l = ∑ k, Q k l * x k :=
    fun l => nearIsometry_apply hT hS hd x l
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  -- `⟪Mx,Mx⟫ = ∑_k ∑_m (QQᵀ)_{km} (x_k x_m)`.
  have hMM : ∑ i, (nearIsometry hT hS hd x).ofLp i * (nearIsometry hT hS hd x).ofLp i
      = ∑ k, ∑ m, (Q * Qᵀ) k m * (x k * x m) := by
    calc ∑ i, (nearIsometry hT hS hd x).ofLp i * (nearIsometry hT hS hd x).ofLp i
        = ∑ l, (∑ k, Q k l * x k) * (∑ m, Q m l * x m) := by
          refine Finset.sum_congr rfl (fun l _ => by rw [happly])
      _ = ∑ l, ∑ k, ∑ m, (Q k l * x k) * (Q m l * x m) := by
          refine Finset.sum_congr rfl (fun l _ => by rw [Finset.sum_mul_sum])
      _ = ∑ k, ∑ m, ∑ l, (Q k l * x k) * (Q m l * x m) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => by rw [Finset.sum_comm])
      _ = ∑ k, ∑ m, (Q * Qᵀ) k m * (x k * x m) := by
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => ?_))
          rw [Matrix.mul_apply]
          simp only [Matrix.transpose_apply]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun l _ => by ring)
  -- `⟪x,x⟫ = ∑_k ∑_m I_{km} (x_k x_m)`.
  have hxx : ∑ i, x.ofLp i * x.ofLp i
      = ∑ k, ∑ m, (1 : Matrix (Fin d) (Fin d) ℝ) k m * (x k * x m) := by
    symm
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hmk; rw [Matrix.one_apply_ne (Ne.symm hmk), zero_mul]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hMM, hxx, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Matrix.sub_apply]; ring

/-- Internal helper / algebraic step: `⟪x, x⟫` as the coordinate sum of squares
on `EuclideanSpace ℝ (Fin d)`. -/
private theorem inner_self_eq_sum (x : EuclideanSpace ℝ (Fin d)) :
    -- Conclusion: the self inner product equals the sum of squared coordinates.
    ⟪x, x⟫_ℝ = ∑ k, (x k)^2 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [pow_two]

/-- Internal helper / algebraic step (**Gram-deviation quadratic-form bound**).
`M` is a near-isometry: `|⟪M x, M x⟫ − ⟪x, x⟫| ≤ δ ⟪x, x⟫` with `δ := d · τ`,
`τ := 4 d ε² / α²`. This is the input to the local near-isometry alignment
branch.  The spectral input is the YWS population-gap cross-energy bound; no
sample-gap smallness condition is used. -/
private theorem gram_dev_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖)
    (x : EuclideanSpace ℝ (Fin d)) :
    -- Conclusion: `M`'s isometry defect at `x` is `≤ δ ⟪x,x⟫` with `δ = d·4dε²/α²`.
    |⟪nearIsometry hT hS hd x, nearIsometry hT hS hd x⟫_ℝ - ⟪x, x⟫_ℝ|
      ≤ ((d : ℝ) * (4 * (d : ℝ) * ε^2 / α^2)) * ⟪x, x⟫_ℝ := by
  set τ : ℝ := 4 * (d : ℝ) * ε^2 / α^2 with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  set D := (Acharyya2025.Overlap.overlap hT hS hn_eq hd) *
      (Acharyya2025.Overlap.overlap hT hS hn_eq hd)ᵀ
        - (1 : Matrix (Fin d) (Fin d) ℝ) with hD
  have hDbnd : ∀ k m : Fin d, |D k m| ≤ τ :=
    fun k m => abs_dev_le hd hT hS hα_pos hα htail hε k m
  rw [gram_dev_identity hT hS hd x]
  -- `|∑∑ D x x| ≤ ∑∑ τ |x_k| |x_m| = τ (∑|x_k|)² ≤ τ d ∑ x_k² = τ d ⟪x,x⟫`.
  have step1 : |∑ k, ∑ m, D k m * (x k * x m)| ≤ ∑ k, ∑ m, τ * (|x k| * |x m|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hDbnd k m) (by positivity)
  have hsumsum : ∑ k, ∑ m, τ * (|x k| * |x m|) = τ * (∑ k, |x k|)^2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
  have hcard : (∑ k, |x k|)^2 ≤ (d : ℝ) * ∑ k, (x k)^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun k => |x k|)
    simpa only [Finset.card_univ, Fintype.card_fin, sq_abs] using h
  rw [inner_self_eq_sum x]
  calc |∑ k, ∑ m, D k m * (x k * x m)|
      ≤ ∑ k, ∑ m, τ * (|x k| * |x m|) := step1
    _ = τ * (∑ k, |x k|)^2 := hsumsum
    _ ≤ τ * ((d : ℝ) * ∑ k, (x k)^2) := mul_le_mul_of_nonneg_left hcard hτ0
    _ = (d : ℝ) * τ * ∑ k, (x k)^2 := by ring

/-! ### Coordinate / Parseval utilities -/

/-- Internal helper / algebraic step: the `i`-th coordinate of a finite
`smul`-combination in `EuclideanSpace`. -/
private theorem smul_sum_apply {m p : ℕ} (c : Fin p → ℝ)
    (v : Fin p → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    -- Conclusion: coordinate of a linear combination is the combination of coordinates.
    (∑ k, c k • v k) i = ∑ k, c k * (v k) i := by
  show (∑ k, c k • v k).ofLp i = ∑ k, c k * (v k).ofLp i
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [WithLp.ofLp_smul]; rfl

/-- Internal helper / algebraic step (**Parseval for an orthonormal family**):
`‖∑ k, c k • v k‖² = ∑ k, (c k)²`. -/
private theorem norm_sq_smul_sum_orthonormal {m p : ℕ}
    {v : Fin p → EuclideanSpace ℝ (Fin m)} (hv : Orthonormal ℝ v) (c : Fin p → ℝ) :
    -- Conclusion: the squared norm of an orthonormal combination is the coefficient energy.
    ‖∑ k, c k • v k‖^2 = ∑ k, (c k)^2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  have key := hv.inner_left_right_finset (s := (Finset.univ : Finset (Fin p)))
    (a := fun i j => c i * c j)
  calc ∑ i, ⟪c i • v i, ∑ j, c j • v j⟫_ℝ
      = ∑ i, ∑ j, (c i * c j) * ⟪v j, v i⟫_ℝ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inner_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (v i) (v j)]; ring
    _ = ∑ k, c k * c k := by simp_rw [smul_eq_mul] at key; exact key
    _ = ∑ k, (c k)^2 := by refine Finset.sum_congr rfl (fun k _ => by ring)

/-! ### Step 3 helper: the Term-3 reconstruction defect

For the canonical population vector `u_l := hT.eigenvectorBasis (castLE l)` and
the partial reconstruction `∑_k Q_{kl} v_k` (over the top-`d` sample eigenbasis),
the defect vector `w_l := (∑_k Q_{kl} • v_k) − u_l` has squared norm equal to the
trailing cross-energy `∑_{j ≥ d} ⟪v_j, u_l⟫²`. -/

/-- Internal helper / algebraic step. The `v`-coordinate of the Term-3
reconstruction defect vanishes in the leading block and equals `−⟪v_j, u_l⟫` in
the trailing block. (Term 3 is the Davis–Kahan reconstruction-defect term.) -/
private theorem defect_repr (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (l : Fin d) (j : Fin n) :
    -- Conclusion: the defect's `j`-th sample coordinate is `−⟪v_j,u_l⟫` (trailing) or `0` (leading).
    (hS.eigenvectorBasis hn_eq).repr
        ((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
          - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) j
      = if d ≤ (j : ℕ)
          then - ⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq (Fin.castLE hd l)⟫_ℝ
          else 0 := by
  set v := hS.eigenvectorBasis hn_eq with hv
  set u := hT.eigenvectorBasis hn_eq with hu
  set Q := Acharyya2025.Overlap.overlap hT hS hn_eq hd with hQ
  -- `repr (·) j = ⟪v_j, ·⟫`, split the subtraction.
  rw [(v).repr_apply_apply, inner_sub_right, inner_sum]
  -- `⟪v_j, Σ_k Q_kl v_k⟫ = Σ_k Q_kl ⟪v_j, v_{castLE k}⟫ = Σ_k Q_kl (if j = castLE k then 1 else 0)`.
  have hortho : ∀ k : Fin d, ⟪v j, v (Fin.castLE hd k)⟫_ℝ = if j = Fin.castLE hd k then (1:ℝ) else 0 := by
    intro k
    rw [hv]
    exact orthonormal_iff_ite.mp (hS.eigenvectorBasis hn_eq).orthonormal j (Fin.castLE hd k)
  have hsum1 : ∑ k, ⟪v j, Q k l • v (Fin.castLE hd k)⟫_ℝ
      = ∑ k, Q k l * (if j = Fin.castLE hd k then (1:ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_smul_right, hortho k]
  rw [hsum1]
  by_cases hj : d ≤ (j : ℕ)
  · -- trailing block: the leading sum vanishes
    rw [ite_eq_left hj]
    have hzero : ∑ k, Q k l * (if j = Fin.castLE hd k then (1:ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have hne : j ≠ Fin.castLE hd k := by
        intro h; rw [h] at hj; simp only [Fin.val_castLE] at hj; omega
      rw [ite_eq_right hne, mul_zero]
    rw [hzero, zero_sub]
  · -- leading block: cancellation `Q_{⟨j⟩,l} = ⟪v_j, u_l⟫`
    rw [ite_eq_right hj]
    push Not at hj
    have hcollapse : ∑ k, Q k l * (if j = Fin.castLE hd k then (1:ℝ) else 0) = Q ⟨(j:ℕ), hj⟩ l := by
      rw [Finset.sum_eq_single ⟨(j:ℕ), hj⟩]
      · have hje : j = Fin.castLE hd ⟨(j:ℕ), hj⟩ := by apply Fin.ext; simp [Fin.castLE]
        rw [ite_eq_left hje, mul_one]
      · intro k _ hk
        have hne : j ≠ Fin.castLE hd k := by
          intro h; apply hk; apply Fin.ext
          have heq : (j : ℕ) = ((Fin.castLE hd k : Fin n) : ℕ) := by rw [h]
          simp only [Fin.val_castLE] at heq; exact heq.symm
        rw [ite_eq_right hne, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    rw [hcollapse]
    -- `Q_{⟨j⟩,l} = ⟪v_{castLE ⟨j⟩}, u_l⟫ = ⟪v_j, u_l⟫`, so the difference is 0
    have hjcast : Fin.castLE hd ⟨(j:ℕ), hj⟩ = j := by apply Fin.ext; simp [Fin.castLE]
    have : Q ⟨(j:ℕ), hj⟩ l = ⟪v j, u (Fin.castLE hd l)⟫_ℝ := by
      rw [hQ, Acharyya2025.Overlap.overlap, hjcast]
    rw [this, sub_self]

/-- Internal helper / algebraic step (**Term-3 defect squared norm**):
`‖w_l‖² = ∑_{j ≥ d} ⟪v_j, u_l⟫²` — the defect's energy equals the trailing
cross-energy later controlled by `crossPop_yws_le`. -/
private theorem defect_norm_sq (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (l : Fin d) :
    -- Conclusion: the `l`-th defect's squared norm equals its trailing cross energy.
    ‖(∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
        - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)‖^2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq (Fin.castLE hd l)⟫_ℝ)^2 := by
  set w := (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
        - hT.eigenvectorBasis hn_eq (Fin.castLE hd l) with hw
  rw [← Acharyya2025.Weyl.sum_repr_sq_eq_norm_sq (hS.eigenvectorBasis hn_eq) w]
  -- Split the full sum into leading (`0`) and trailing (`⟪v_j,u_l⟫²`) blocks.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => d ≤ (j : ℕ))]
  have hlead : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (d ≤ (j : ℕ))),
      ((hS.eigenvectorBasis hn_eq).repr w j)^2 = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hjlt : ¬ (d ≤ (j : ℕ)) := (Finset.mem_filter.mp hj).2
    rw [hw, defect_repr hT hS hd l j, ite_eq_right hjlt]; ring
  rw [hlead, add_zero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjge : d ≤ (j : ℕ) := (Finset.mem_filter.mp hj).2
  rw [hw, defect_repr hT hS hd l j, ite_eq_left hjge]
  ring

/-! ### Frobenius packaging

The total error and the three terms are packaged as elements of
`EuclideanSpace ℝ (Fin n × Fin d)`, so the Minkowski (triangle) inequality is
just `norm_add_le`. -/

/-- Internal helper / algebraic step: the squared Frobenius norm of a
product-space vector as an iterated (rows × columns) sum. -/
private theorem frob_sq (t : EuclideanSpace ℝ (Fin n × Fin d)) :
    -- Conclusion: the squared norm equals the double sum of squared entries.
    ‖t‖^2 = ∑ i : Fin n, ∑ l : Fin d, (t (i, l))^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp [Real.norm_eq_abs, sq_abs]

/-- Notation abbreviation: the `k`-th sample top-block eigenvalue `λ̂_k`. -/
private noncomputable abbrev lamHat (hS : S.IsSymmetric) (hd : d ≤ n) (k : Fin d) : ℝ :=
  hS.eigenvalues hn_eq (Fin.castLE hd k)

/-- Notation abbreviation: the `l`-th population top-block eigenvalue `λ_l`. -/
private noncomputable abbrev lamPop (hT : T.IsSymmetric) (hd : d ≤ n) (l : Fin d) : ℝ :=
  hT.eigenvalues hn_eq (Fin.castLE hd l)

/-- The **Term-2 (commutator) vector**, packaged as a Frobenius vector:
`(i,l) ↦ ∑_k Q_{kl}(√λ̂_k − √λ_l) v_k(i)`. This is the second of the three terms
in the decomposition `ψ̂W − ψ = Term1 + Term2 + Term3`; a plain definition. -/
private noncomputable def term2vec (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 (fun p : Fin n × Fin d =>
    ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k p.2
        * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd p.2))
        * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) p.1)

/-- The **Term-3 (subspace reconstruction-defect) vector**, packaged as a
Frobenius vector: `(i,l) ↦ √λ_l (∑_k Q_{kl} v_k(i) − u_l(i))`. Third of the three
decomposition terms; a plain definition. -/
private noncomputable def term3vec (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 (fun p : Fin n × Fin d =>
    Real.sqrt (lamPop hT hd p.2)
      * (((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k p.2
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
          - hT.eigenvectorBasis hn_eq (Fin.castLE hd p.2)) p.1))

/-- Internal helper / algebraic step: coordinate formula for `term3vec`. -/
private theorem term3vec_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (i : Fin n) (l : Fin d) :
    -- Conclusion: the `(i,l)` entry of the Term-3 vector unfolds to its defining expression.
    (term3vec hT hS hd) (i, l)
      = Real.sqrt (lamPop hT hd l)
        * (((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
            - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) i) := rfl

/-- Internal helper / algebraic step (**Term-3 squared Frobenius bound**):
`‖term3vec‖² ≤ Λ · (4 d ε² / α²)`. Bounds the reconstruction-defect term
using the eigenvalue cap `Λ` and the YWS population-gap cross energy.

Hypotheses combine the eigenvalue floor `α` (`hα_pos`, `hα`), the rank-`d` tail
(`htail`, Assumption 1), the cap `Λ` (`hΛ`, Assumption 2 upper bound), and
operator-norm closeness `ε`; no sample-gap smallness condition is required. -/
private theorem term3_norm_sq_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α Λ ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues hn_eq j = 0)
    (hΛ : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    -- Conclusion: the Term-3 Frobenius energy is `≤ Λ · 4dε²/α²`.
    ‖term3vec hT hS hd‖^2 ≤ Λ * (4 * (d : ℝ) * ε^2 / α^2) := by
  -- `0 ≤ Λ`: when `n = 0` both sides vanish; otherwise eigenvalue `0` witnesses it.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hd0 : d = 0 := Nat.le_zero.mp hd
    subst d
    have hterm : term3vec hT hS hd = 0 := by
      ext p; exact (Fin.elim0 p.1)
    rw [hterm]
    simp
  have hΛ0 : 0 ≤ Λ := by
    set z : Fin n := ⟨0, hnpos⟩ with hz
    by_cases hd0 : 0 < d
    · have hlt : (z : ℕ) < d := by rw [hz]; simpa using hd0
      exact le_trans (le_of_lt hα_pos) (le_trans (hα z hlt) (hΛ z))
    · push Not at hd0
      have hdz : d = 0 := Nat.le_zero.mp hd0
      have hge : d ≤ (z : ℕ) := by omega
      have hez := htail z hge
      linarith [hΛ z, hez]
  -- `‖t3‖² = ∑_l λ_l ‖w_l‖²`.
  set w := fun l : Fin d => (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
        - hT.eigenvectorBasis hn_eq (Fin.castLE hd l) with hw
  have hpop_nonneg : ∀ l : Fin d, 0 ≤ lamPop hT hd l := by
    intro l
    have hlt : ((Fin.castLE hd l : Fin n) : ℕ) < d := by simp [Fin.castLE]
    exact le_trans (le_of_lt hα_pos) (hα (Fin.castLE hd l) hlt)
  have hstep : ‖term3vec hT hS hd‖^2 = ∑ l : Fin d, (lamPop hT hd l) * ‖w l‖^2 := by
    rw [frob_sq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    -- ∑_i (√λ_l · (w l) i)² = λ_l · ∑_i ((w l) i)² = λ_l ‖w l‖²
    have hsqrt : (Real.sqrt (lamPop hT hd l))^2 = lamPop hT hd l :=
      Real.sq_sqrt (hpop_nonneg l)
    have hnormw : ∑ i : Fin n, ((w l) i)^2 = ‖w l‖^2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
    calc ∑ i : Fin n, ((term3vec hT hS hd) (i, l))^2
        = ∑ i : Fin n, (lamPop hT hd l) * ((w l) i)^2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [term3vec_apply, mul_pow, hsqrt]
      _ = (lamPop hT hd l) * ∑ i : Fin n, ((w l) i)^2 := by rw [Finset.mul_sum]
      _ = (lamPop hT hd l) * ‖w l‖^2 := by rw [hnormw]
  rw [hstep]
  -- Each `‖w l‖² = ∑_{j≥d}⟪v_j,u_l⟫²`; `λ_l ≤ Λ`.
  have hnormwl : ∀ l : Fin d, ‖w l‖^2
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hS.eigenvectorBasis hn_eq j, hT.eigenvectorBasis hn_eq (Fin.castLE hd l)⟫_ℝ)^2 :=
    fun l => defect_norm_sq hT hS hd l
  -- `∑_l λ_l ‖w_l‖² ≤ Λ ∑_l ‖w_l‖²` and `∑_l ‖w_l‖² = crossPop' ≤ 4dε²/α²`.
  have hbound1 : ∑ l : Fin d, (lamPop hT hd l) * ‖w l‖^2
      ≤ ∑ l : Fin d, Λ * ‖w l‖^2 := by
    refine Finset.sum_le_sum (fun l _ => ?_)
    exact mul_le_mul_of_nonneg_right (hΛ (Fin.castLE hd l)) (sq_nonneg _)
  -- `∑_l ‖w_l‖² = ∑_{l<d (castLE)}∑_{j≥d}⟪v_j,u_l⟫² ≤ crossPop`.
  have hcrossPop := crossPop_yws_le hd hT hS hα_pos hα htail hε
  -- Bridge: ∑_{l:Fin d} (column at castLE l) = ∑_{i ∈ filter <d} (column at i).
  have hbridge : ∑ l : Fin d, ‖w l‖^2
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d),
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
    -- rewrite each ‖w_l‖² and reindex castLE → filter
    have hrw : ∑ l : Fin d, ‖w l‖^2
        = ∑ l : Fin d, ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
            (⟪hT.eigenvectorBasis hn_eq (Fin.castLE hd l), hS.eigenvectorBasis hn_eq j⟫_ℝ)^2 := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hnormwl l]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_comm]
    rw [hrw]
    -- reindex castLE ↦ filter (<d)
    rw [sum_castLE_eq_filter hd
        (fun i : Fin n => ∑ j ∈ Finset.univ.filter (fun j : Fin n => d ≤ (j : ℕ)),
          (⟪hT.eigenvectorBasis hn_eq i, hS.eigenvectorBasis hn_eq j⟫_ℝ)^2)]
  calc ∑ l : Fin d, (lamPop hT hd l) * ‖w l‖^2
      ≤ ∑ l : Fin d, Λ * ‖w l‖^2 := hbound1
    _ = Λ * ∑ l : Fin d, ‖w l‖^2 := by rw [Finset.mul_sum]
    _ ≤ Λ * (4 * (d : ℝ) * ε^2 / α^2) :=
        mul_le_mul_of_nonneg_left (le_trans hbridge hcrossPop) hΛ0

/-- Internal helper / algebraic step: coordinate formula for `term2vec`. -/
private theorem term2vec_apply (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hd : d ≤ n)
    (i : Fin n) (l : Fin d) :
    -- Conclusion: the `(i,l)` entry of the Term-2 vector unfolds to its defining expression.
    (term2vec hT hS hd) (i, l)
      = ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
          * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))
          * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i := rfl

/-- Square-root difference controlled from the positive right endpoint only.
The left endpoint may be negative; `Real.sqrt` then clamps it to zero. -/
private theorem abs_sqrt_sub_sqrt_le_abs_sub_div_sqrt_right
    {a b : ℝ} (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / Real.sqrt b := by
  have hsb_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  by_cases ha : 0 ≤ a
  · have hden_pos : 0 < Real.sqrt a + Real.sqrt b := by positivity
    have hsqrt : Real.sqrt a - Real.sqrt b =
        (a - b) / (Real.sqrt a + Real.sqrt b) := by
      rw [eq_div_iff (ne_of_gt hden_pos)]
      have h1 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
      have h2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
      nlinarith [h1, h2]
    rw [hsqrt, abs_div, abs_of_pos hden_pos]
    rw [div_le_div_iff₀ hden_pos hsb_pos]
    exact mul_le_mul_of_nonneg_left
      (by have := Real.sqrt_nonneg a; linarith) (abs_nonneg _)
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [Real.sqrt_eq_zero_of_nonpos ha', zero_sub, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg b)]
    rw [le_div_iff₀ hsb_pos, Real.mul_self_sqrt hb.le]
    rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith

/-- Internal helper / algebraic step.  The Term-2 coefficient is controlled by
the corresponding perturbation residual, before the operator norm is applied:

`|Q_kl (sqrt(lamHat_k) - sqrt(lam_l))|
  <= |<v_k, (S - T) u_l>| / sqrt(alpha)`.

Keeping the residual on the right is the key strengthening over the entrywise
bound below: Parseval can sum these residual coordinates for a fixed `l` before
the operator-norm hypothesis is used, so the final Term-2 estimate pays one
factor of `d` rather than `d^2`. -/
private theorem abs_term2_coeff_le_residual
    (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (k l : Fin d) :
    |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
        * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))|
      ≤ |⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
            (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ|
          / Real.sqrt α := by
  set a := lamHat hS hd k with ha
  set b := lamPop hT hd l with hb
  have hbpos : α ≤ b := by
    have hlt : ((Fin.castLE hd l : Fin n) : ℕ) < d := by simp [Fin.castLE]
    exact hα (Fin.castLE hd l) hlt
  have hb_pos : 0 < b := lt_of_lt_of_le hα_pos hbpos
  have hsqrt := abs_sqrt_sub_sqrt_le_abs_sub_div_sqrt_right (a := a) (b := b) hb_pos
  have hmul :
      |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l *
          (Real.sqrt a - Real.sqrt b)|
        ≤ |(a - b) * (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l| /
            Real.sqrt b := by
    calc
      |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l *
          (Real.sqrt a - Real.sqrt b)|
          = |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l| *
              |Real.sqrt a - Real.sqrt b| := abs_mul _ _
      _ ≤ |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l| *
            (|a - b| / Real.sqrt b) :=
          mul_le_mul_of_nonneg_left hsqrt (abs_nonneg _)
      _ = |(a - b) * (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l| /
            Real.sqrt b := by
          rw [abs_mul]
          ring
  have hcomm :
      (a - b) * (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
        = ⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
            (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ :=
    Acharyya2025.Overlap.eigenvalue_commutator_eq hT hS hn_eq hd k l
  rw [hcomm] at hmul
  have hroot : Real.sqrt α ≤ Real.sqrt b := Real.sqrt_le_sqrt hbpos
  have hαroot_pos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα_pos
  have hbroot_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb_pos
  calc
    |(Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l *
        (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))|
        ≤ |⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
              (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ| /
            Real.sqrt b := by simpa [ha, hb] using hmul
    _ ≤ |⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
              (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ| /
            Real.sqrt α := by
      rw [div_le_div_iff₀ hbroot_pos hαroot_pos]
      exact mul_le_mul_of_nonneg_left hroot (abs_nonneg _)

/-- Internal helper / algebraic step (**Term-2 squared Frobenius bound**):
`‖term2vec‖² ≤ d · (ε / √α)²`.

For each population column `l`, the commutator identity leaves the residual
coordinates `⟪v_k, (S - T) u_l⟫`.  Parseval/Bessel sums those coordinates first,
giving at most `‖(S - T) u_l‖² ≤ ε²`; only then do we sum over the `d`
population columns.  This avoids the previous entrywise `d²` count. -/
private theorem term2_norm_sq_le (hd : d ≤ n) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {α ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    -- Conclusion: the Term-2 Frobenius energy is `≤ d·(ε/√α)²`.
    ‖term2vec hT hS hd‖^2 ≤ (d : ℝ) * (ε / Real.sqrt α)^2 := by
  set c := fun (k l : Fin d) => (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
      * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l)) with hc
  set r := fun (k l : Fin d) =>
      ⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
        (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ with hr
  set ρ : ℝ := Real.sqrt α with hρ
  have hρ_pos : 0 < ρ := by rw [hρ]; exact Real.sqrt_pos.mpr hα_pos
  -- `‖t2‖² = ∑_l ∑_k c_{kl}²` via Parseval per `l`.
  have hstep : ‖term2vec hT hS hd‖^2 = ∑ l : Fin d, ∑ k : Fin d, (c k l)^2 := by
    rw [frob_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    -- ∑_i (∑_k c_{kl} v_k(i))² = ‖∑_k c_{kl} • v_k‖² = ∑_k c_{kl}²
    have hcoord : ∀ i : Fin n, (term2vec hT hS hd) (i, l)
        = (∑ k, (c k l) • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) i := by
      intro i
      rw [smul_sum_apply, term2vec_apply]
    calc ∑ i : Fin n, ((term2vec hT hS hd) (i, l))^2
        = ∑ i : Fin n, ((∑ k, (c k l) • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) i)^2 := by
          refine Finset.sum_congr rfl (fun i _ => by rw [hcoord i])
      _ = ‖∑ k, (c k l) • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)‖^2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
          refine Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
      _ = ∑ k : Fin d, (c k l)^2 := by
          have hortho : Orthonormal ℝ (fun k : Fin d =>
              hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) :=
            (hS.eigenvectorBasis hn_eq).orthonormal.comp _ (Fin.castLE_injective hd)
          exact norm_sq_smul_sum_orthonormal hortho (fun k => c k l)
  rw [hstep]
  -- Keep the residual coordinate instead of replacing it entrywise by `ε`.
  have hcoeff : ∀ k l : Fin d, (c k l)^2 ≤ (r k l / ρ)^2 := by
    intro k l
    have habs_strong := abs_term2_coeff_le_residual hd hT hS hα_pos hα k l
    have habs : |c k l| ≤ |r k l| / ρ := by
      rw [hρ]
      simpa only [c, r] using habs_strong
    have hsquare := pow_le_pow_left₀ (abs_nonneg (c k l)) habs 2
    calc
      (c k l)^2 = |c k l|^2 := by rw [sq_abs]
      _ ≤ (|r k l| / ρ)^2 := hsquare
      _ = (r k l / ρ)^2 := by
          have habsdiv : |r k l| / ρ = |r k l / ρ| := by
            rw [abs_div, abs_of_pos hρ_pos]
          rw [habsdiv, sq_abs]
  have hcol : ∀ l : Fin d, ∑ k : Fin d, (c k l)^2 ≤ (ε / ρ)^2 := by
    intro l
    have hortho : Orthonormal ℝ (fun k : Fin d =>
        hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) :=
      (hS.eigenvectorBasis hn_eq).orthonormal.comp _ (Fin.castLE_injective hd)
    have hresidual : ∑ k : Fin d, (r k l)^2 ≤ ε^2 := by
      have hparseval :
          ∑ k : Fin d,
              ‖⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
                  (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ‖^2
            ≤ ‖(S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))‖^2 :=
        _root_.Orthonormal.sum_inner_products_le _ hortho
      have hclose := hε (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))
      rw [(hT.eigenvectorBasis hn_eq).orthonormal.1 (Fin.castLE hd l), mul_one] at hclose
      calc
        ∑ k : Fin d, (r k l)^2
            = ∑ k : Fin d,
                ‖⟪hS.eigenvectorBasis hn_eq (Fin.castLE hd k),
                    (S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))⟫_ℝ‖^2 := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              simp [r, Real.norm_eq_abs, sq_abs]
        _ ≤ ‖(S - T) (hT.eigenvectorBasis hn_eq (Fin.castLE hd l))‖^2 := hparseval
        _ ≤ ε^2 := pow_le_pow_left₀ (norm_nonneg _) hclose 2
    calc
      ∑ k : Fin d, (c k l)^2
          ≤ ∑ k : Fin d, (r k l / ρ)^2 :=
            Finset.sum_le_sum (fun k _ => hcoeff k l)
      _ = (∑ k : Fin d, (r k l)^2) / ρ^2 := by
          simp_rw [div_pow]
          rw [Finset.sum_div]
      _ ≤ ε^2 / ρ^2 := div_le_div_of_nonneg_right hresidual (sq_nonneg ρ)
      _ = (ε / ρ)^2 := by rw [div_pow]
  calc
    ∑ l : Fin d, ∑ k : Fin d, (c k l)^2
        ≤ ∑ _l : Fin d, (ε / ρ)^2 := Finset.sum_le_sum (fun l _ => hcol l)
    _ = (d : ℝ) * (ε / ρ)^2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (d : ℝ) * (ε / Real.sqrt α)^2 := by rw [hρ]

/-! ### Step 4 (Term 1): total energy of the spectral embedding `ψ̂`

`∑_i ‖ψ̂ i‖² = ∑_k λ̂_k ≤ d (Λ + ε)`, where the orthonormality of the sample
eigenbasis collapses the `i`-sum and Weyl bounds each `λ̂_k`. -/

/-- Internal helper / algebraic step: coordinate of the spectral embedding,
`ψ̂ i k = √λ̂_k · v_k(i)`. -/
private theorem spectralConfig_apply (hS : S.IsSymmetric) (hd : d ≤ n) (i : Fin n) (k : Fin d) :
    -- Conclusion: the `(i,k)` coordinate of the embedding unfolds to `√λ̂_k · v_k(i)`.
    spectralConfig S hS hd i k
      = Real.sqrt (lamHat hS hd k) * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i := rfl

/-- Internal helper / algebraic step (**total spectral energy bound**):
`∑_i ‖ψ̂ i‖² ≤ d (Λ + ε)`. The sample embedding has bounded total energy (its
columns are the orthonormal eigenvectors scaled by `√λ̂_k`, each `λ̂_k ≤ Λ + ε`
by Weyl). Feeds the Term-1 bound. Uses the cap `Λ` (Assumption 2 upper bound) and
operator-norm closeness `ε`. -/
private theorem sum_norm_sq_spectralConfig_le (hd : d ≤ n) (hT : T.IsSymmetric)
    (hS : S.IsSymmetric) {α Λ ε : ℝ} (hα_pos : 0 < α)
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues hn_eq i)
    (hΛ : ∀ l : Fin n, hT.eigenvalues hn_eq l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    -- Conclusion: the sample embedding's total energy is `≤ d(Λ+ε)`.
    ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2 ≤ (d : ℝ) * (Λ + ε) := by
  by_cases hd0 : d = 0
  · subst d
    have hsum : ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      have hzero : spectralConfig S hS hd i = 0 := by
        ext k
        exact Fin.elim0 k
      rw [hzero, norm_zero]
      norm_num
    rw [hsum]
    norm_num
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  let k0 : Fin d := ⟨0, hdpos⟩
  have hk0lt : ((Fin.castLE hd k0 : Fin n) : ℕ) < d := by simp [Fin.castLE]
  have hΛpos : 0 < Λ :=
    lt_of_lt_of_le hα_pos (le_trans (hα (Fin.castLE hd k0) hk0lt) (hΛ (Fin.castLE hd k0)))
  have hε0 : 0 ≤ ε := by
    have hc := hε (hT.eigenvectorBasis hn_eq (Fin.castLE hd k0))
    rw [(hT.eigenvectorBasis hn_eq).orthonormal.norm_eq_one (Fin.castLE hd k0), mul_one] at hc
    exact le_trans (norm_nonneg _) hc
  have hΛε0 : 0 ≤ Λ + ε := by linarith
  have hsqrtsq_ub : ∀ k : Fin d,
      (Real.sqrt (lamHat hS hd k))^2 ≤ Λ + ε := by
    intro k
    by_cases hk : 0 ≤ lamHat hS hd k
    · rw [Real.sq_sqrt hk]
      exact sample_eig_ub hd hT hS hΛ hε k
    · have hk' : lamHat hS hd k ≤ 0 := le_of_not_ge hk
      rw [Real.sqrt_eq_zero_of_nonpos hk']
      simpa using hΛε0
  -- `‖ψ̂ i‖² = ∑_k (√λ̂_k)² v_k(i)²`; negative sample eigenvalues contribute zero.
  have hnormi : ∀ i : Fin n, ‖spectralConfig S hS hd i‖^2
      = ∑ k : Fin d, (Real.sqrt (lamHat hS hd k))^2 *
          (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2 := by
    intro i
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (spectralConfig S hS hd i).ofLp k = spectralConfig S hS hd i k from rfl,
      spectralConfig_apply, Real.norm_eq_abs, sq_abs, mul_pow]
  have hstep : ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2
      = ∑ k : Fin d, (Real.sqrt (lamHat hS hd k))^2
          * ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2 := by
    rw [Finset.sum_congr rfl (fun i _ => hnormi i), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
  -- `∑_i v_k(i)² = ‖v_k‖² = 1`.
  have hunit : ∀ k : Fin d, ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2 = 1 := by
    intro k
    have h1 : ‖hS.eigenvectorBasis hn_eq (Fin.castLE hd k)‖ = 1 :=
      (hS.eigenvectorBasis hn_eq).orthonormal.1 (Fin.castLE hd k)
    have heq : ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2
        = ‖hS.eigenvectorBasis hn_eq (Fin.castLE hd k)‖^2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl (fun i _ => by simp [Real.norm_eq_abs, sq_abs])
    rw [heq, h1]; norm_num
  rw [hstep]
  -- `∑_k (√λ̂_k)² ≤ ∑_k (Λ + ε) = d(Λ+ε)`.
  calc ∑ k : Fin d, (Real.sqrt (lamHat hS hd k))^2
          * ∑ i : Fin n, (hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)^2
      = ∑ k : Fin d, (Real.sqrt (lamHat hS hd k))^2 := by
        refine Finset.sum_congr rfl (fun k _ => by rw [hunit k, mul_one])
    _ ≤ ∑ _k : Fin d, (Λ + ε) := by
        exact Finset.sum_le_sum (fun k _ => hsqrtsq_ub k)
    _ = (d : ℝ) * (Λ + ε) := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The configuration-perturbation theorem (WP7(c4)) -/

/-- Frobenius error between two finite configurations, viewing the `n` points in
`ℝ^d` as an `n × d` matrix.  This is the matrix Frobenius norm used by the
perturbation proof before the legacy `ConfigError` conversion. -/
noncomputable def ConfigFrobError {n d : ℕ}
    (ψhat ψ : Acharyya2024.Config n d) : ℝ :=
  Real.sqrt (∑ i : Fin n, ‖ψhat i - ψ i‖^2)

/-- Every row error is bounded by the Frobenius configuration error. -/
theorem norm_config_le_ConfigFrobError {n d : ℕ}
    (ψhat ψ : Acharyya2024.Config n d) (i : Fin n) :
    ‖ψhat i - ψ i‖ ≤ ConfigFrobError ψhat ψ := by
  rw [ConfigFrobError, ← Real.sqrt_sq (norm_nonneg (ψhat i - ψ i))]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg ‖ψhat j - ψ j‖) (Finset.mem_univ i)

/-- The legacy `ℓ¹`-over-points `ConfigError` is at most `√n` times the
Frobenius configuration error. -/
theorem configError_le_sqrt_mul_ConfigFrobError {n d : ℕ}
    (ψhat ψ : Acharyya2024.Config n d) :
    Acharyya2024.ConfigError ψhat ψ ≤ Real.sqrt n * ConfigFrobError ψhat ψ := by
  unfold Acharyya2024.ConfigError ConfigFrobError
  have hcard :
      (∑ i : Fin n, ‖ψhat i - ψ i‖)^2 ≤
        (n : ℝ) * ∑ i : Fin n, ‖ψhat i - ψ i‖^2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => ‖ψhat i - ψ i‖)
    simpa [Finset.card_univ] using h
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, ‖ψhat i - ψ i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  calc
    ∑ i : Fin n, ‖ψhat i - ψ i‖
        = Real.sqrt ((∑ i : Fin n, ‖ψhat i - ψ i‖)^2) := by
            rw [Real.sqrt_sq hsum_nonneg]
    _ ≤ Real.sqrt ((n : ℝ) * ∑ i : Fin n, ‖ψhat i - ψ i‖^2) :=
      Real.sqrt_le_sqrt hcard
    _ = Real.sqrt n * Real.sqrt (∑ i : Fin n, ‖ψhat i - ψ i‖^2) := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ (n : ℝ) by positivity)]

/-- The Frobenius part of the explicit spectral configuration bound.  After the
selected-block Davis--Kahan and residual/Parseval sharpenings, this expression
has no direct ambient-`n` factor; ambient size enters only through whatever
operator perturbation `ε` is supplied by the statistical/matrix layer. -/
noncomputable def configFrobBound (d : ℕ) (α Λ ε : ℝ) : ℝ :=
  Real.sqrt ((2 * ((d : ℝ) * (4 * (d : ℝ) * ε^2 / α^2)))^2 * ((d : ℝ) * (Λ + ε)))
    + Real.sqrt ((d : ℝ) * (ε / Real.sqrt α)^2)
    + Real.sqrt (Λ * (4 * (d : ℝ) * ε^2 / α^2))


/-- Linear coefficient in the local polynomial majorant for `configFrobBound`.
The two linear pieces are the square-root commutator term and the
Davis--Kahan reconstruction term. -/
noncomputable def configFrobLinearCoeff (d : ℕ) (α Λ : ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) * (1 / Real.sqrt α)^2)
    + Real.sqrt (Λ * (4 * (d : ℝ) / α^2))

/-- Quadratic coefficient in the local polynomial majorant for
`configFrobBound`.  The bound `ε ≤ 1` replaces the sample-energy factor
`Λ + ε` by the fixed ceiling `Λ + 1`. -/
noncomputable def configFrobQuadraticCoeff (d : ℕ) (α Λ : ℝ) : ℝ :=
  Real.sqrt
    ((2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 * ((d : ℝ) * (Λ + 1)))

/-- A degree-at-most-two polynomial envelope for the sharpened Frobenius
spectral perturbation bound.  It is written as a degree-three-compatible
polynomial (zero constant and cubic coefficients) because this is the local
spectral object that is compared with the paper's `Poly₃` rate. -/
noncomputable def configFrobQuadraticMajorant (d : ℕ) (α Λ ε : ℝ) : ℝ :=
  configFrobLinearCoeff d α Λ * ε + configFrobQuadraticCoeff d α Λ * ε^2

/-- On the perturbative regime `0 ≤ ε ≤ 1`, the DK-sharpened Frobenius
configuration bound is explicitly polynomial in the operator perturbation:

`configFrobBound d α Λ ε ≤ C₁ ε + C₂ ε²`.

Thus the spectral stage itself needs no cubic loss.  Any remaining difference
between the formal end-to-end rate and the paper's
`Poly₃((n³/r)^(1/2-δ))` bookkeeping comes from the upstream statistical/CMDS
transport into `ε`, not from the selected-block Davis--Kahan step. -/
theorem configFrobBound_le_configFrobQuadraticMajorant
    (d : ℕ) (α Λ ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    configFrobBound d α Λ ε ≤ configFrobQuadraticMajorant d α Λ ε := by
  have hfirst_factor :
      (2 * ((d : ℝ) * (4 * (d : ℝ) * ε^2 / α^2)))^2 * ((d : ℝ) * (Λ + ε))
        = ε^4 *
            ((2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 *
              ((d : ℝ) * (Λ + ε))) := by
    ring
  have hfirst_inside :
      ε^4 *
          ((2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 *
            ((d : ℝ) * (Λ + ε)))
        ≤ ε^4 *
          ((2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 *
            ((d : ℝ) * (Λ + 1))) := by
    have hΛadd : Λ + ε ≤ Λ + 1 := by
      linarith
    have hΛ : (d : ℝ) * (Λ + ε) ≤ (d : ℝ) * (Λ + 1) :=
      mul_le_mul_of_nonneg_left hΛadd (by positivity)
    have hc : 0 ≤ (2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 := sq_nonneg _
    have hx : 0 ≤ ε^4 := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛ hc) hx
  have hfirst :
      Real.sqrt
          ((2 * ((d : ℝ) * (4 * (d : ℝ) * ε^2 / α^2)))^2 *
            ((d : ℝ) * (Λ + ε)))
        ≤ ε^2 * configFrobQuadraticCoeff d α Λ := by
    rw [hfirst_factor]
    calc
      Real.sqrt
          (ε^4 *
            ((2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 *
              ((d : ℝ) * (Λ + ε))))
          ≤ Real.sqrt
            (ε^4 *
              ((2 * ((d : ℝ) * (4 * (d : ℝ) / α^2)))^2 *
                ((d : ℝ) * (Λ + 1)))) := Real.sqrt_le_sqrt hfirst_inside
      _ = Real.sqrt (ε^4) * configFrobQuadraticCoeff d α Λ := by
          rw [configFrobQuadraticCoeff, Real.sqrt_mul (by positivity : 0 ≤ ε^4)]
      _ = ε^2 * configFrobQuadraticCoeff d α Λ := by
          rw [show ε^4 = (ε^2)^2 by ring, Real.sqrt_sq (sq_nonneg ε)]
  have hsecond_factor :
      (d : ℝ) * (ε / Real.sqrt α)^2
        = ε^2 * ((d : ℝ) * (1 / Real.sqrt α)^2) := by
    ring
  have hsecond :
      Real.sqrt ((d : ℝ) * (ε / Real.sqrt α)^2)
        = ε * Real.sqrt ((d : ℝ) * (1 / Real.sqrt α)^2) := by
    rw [hsecond_factor, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0]
  have hthird_factor :
      Λ * (4 * (d : ℝ) * ε^2 / α^2)
        = ε^2 * (Λ * (4 * (d : ℝ) / α^2)) := by
    ring
  have hthird :
      Real.sqrt (Λ * (4 * (d : ℝ) * ε^2 / α^2))
        = ε * Real.sqrt (Λ * (4 * (d : ℝ) / α^2)) := by
    rw [hthird_factor, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0]
  unfold configFrobBound configFrobQuadraticMajorant configFrobLinearCoeff
  rw [hsecond, hthird]
  calc
    Real.sqrt
          ((2 * ((d : ℝ) * (4 * (d : ℝ) * ε ^ 2 / α ^ 2))) ^ 2 *
            ((d : ℝ) * (Λ + ε))) +
        ε * Real.sqrt ((d : ℝ) * (1 / Real.sqrt α) ^ 2) +
        ε * Real.sqrt (Λ * (4 * (d : ℝ) / α ^ 2))
      ≤ ε^2 * configFrobQuadraticCoeff d α Λ +
          ε * Real.sqrt ((d : ℝ) * (1 / Real.sqrt α) ^ 2) +
          ε * Real.sqrt (Λ * (4 * (d : ℝ) / α ^ 2)) := by
            exact add_le_add (add_le_add hfirst le_rfl) le_rfl
    _ = (Real.sqrt ((d : ℝ) * (1 / Real.sqrt α) ^ 2) +
          Real.sqrt (Λ * (4 * (d : ℝ) / α ^ 2))) * ε +
          configFrobQuadraticCoeff d α Λ * ε^2 := by
            ring

/-- Compatibility bound for the older `ConfigError` API.  It is definitionally
`√n` times `configFrobBound`; the expression is kept expanded so existing
downstream proofs that unfold `configBound` keep their previous normal form. -/
noncomputable def configBound (n d : ℕ) (α Λ ε : ℝ) : ℝ :=
  Real.sqrt n *
    ( Real.sqrt ((2 * ((d : ℝ) * (4 * (d : ℝ) * ε^2 / α^2)))^2 * ((d : ℝ) * (Λ + ε)))
    + Real.sqrt ((d : ℝ) * (ε / Real.sqrt α)^2)
    + Real.sqrt (Λ * (4 * (d : ℝ) * ε^2 / α^2)) )

/-- The legacy `configBound` is exactly the Frobenius bound followed by the
`ConfigError ≤ √n · ConfigFrobError` conversion. -/
theorem configBound_eq_sqrt_mul_configFrobBound (n d : ℕ) (α Λ ε : ℝ) :
    configBound n d α Λ ε = Real.sqrt n * configFrobBound d α Λ ε := by
  rfl

/--
**Frobenius configuration perturbation for the classical-MDS spectral embedding.**

Under the same rank-`d`, spectral-floor/cap, and operator-perturbation hypotheses
as the legacy `ConfigError` theorem, there is an aligning isometry `W` such that

`ConfigFrobError (W ∘ spectralConfig S) (spectralConfig T) ≤ configFrobBound d α Λ ε`.

This is the natural endpoint of the three-term product-space proof: the norm on
`EuclideanSpace ℝ (Fin n × Fin d)` is exactly the Frobenius norm of the
configuration matrix.  No Cauchy--Schwarz conversion across the `n` rows is
needed, so the explicit deterministic bound has no extra `√n` factor.

PAPER CORRESPONDENCE: the retained arXiv v1 source is internally inconsistent:
its displayed Theorem 2 carries a `2,∞` subscript, while its discussion says the
proved error is Frobenius and lists a two-to-infinity result as future work.  The
appendix proof works with ordinary matrix norms.  This declaration records the
Frobenius quantity actually controlled by the formal three-term argument.  The
rowwise bound follows separately from `norm_config_le_ConfigFrobError`; it is not
presented here as the literal v1 theorem statement.
-/
theorem exists_isometry_configFrobError_spectralConfig_le
    {n d : ℕ} (hd : d ≤ n)               -- embedding dimension/rank `d ≤ n` (Assumption 1: rank = d)
    (T S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))  -- `T` population, `S` sample Gram operators
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)  -- extra (encoding) assumption: operators are symmetric/self-adjoint
    {α Λ ε : ℝ} (hα_pos : 0 < α) (_hε_nonneg : 0 ≤ ε)  -- floor `α > 0`, perturbation `ε ≥ 0`
    -- Assumption 2 (lower): leading `d` population eigenvalues `≥ α` (paper's `λ_d`/`C1`):
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues finrank_euclideanSpace_fin i)
    -- Assumption 1 (rank = d, encoded): all trailing population eigenvalues vanish:
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues finrank_euclideanSpace_fin j = 0)
    -- Assumption 2 (upper): all population eigenvalues `≤ Λ` (paper's `λ_1`/`C2`):
    (hΛ : ∀ l : Fin n, hT.eigenvalues finrank_euclideanSpace_fin l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) : -- sample/population operator-norm closeness `‖S − T‖ ≤ ε`
    -- Conclusion: there is an isometry `W` aligning the sample and population
    -- spectral configurations in Frobenius norm.
    ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      ConfigFrobError (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd)
        ≤ configFrobBound d α Λ ε  := by
  set δ : ℝ := (d : ℝ) * (4 * (d : ℝ) * ε^2 / α^2) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- The near-isometry `M` and its Gram-deviation bound feed the local branch.
  -- For `δ < 1`, the sharp TauCeti polar estimate gives an isometry within `δ`.
  -- For `δ ≥ 1`, YWS supplies a global Procrustes alignment; since both the
  -- overlap map and the alignment are contractions/isometries, their distance
  -- is at most `2 ≤ 2δ`.  This removes the former `δ ≤ 1/2` hypothesis while
  -- preserving the existing `2δ` Term-1 envelope.
  set M := nearIsometry hT hS hd with hM
  have hclose : ∀ x : EuclideanSpace ℝ (Fin d),
      |⟪M x, M x⟫_ℝ - ⟪x, x⟫_ℝ| ≤ δ * ⟪x, x⟫_ℝ := by
    intro x
    rw [hM, hδ]
    exact gram_dev_le hd hT hS hα_pos hα htail hε x
  obtain ⟨W, hWiso, hWclose⟩ :
      ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
        (∀ x, ‖(M - W) x‖ ≤ 2 * δ * ‖x‖) := by
    by_cases hδlt : δ < 1
    · obtain ⟨W, hWsharp⟩ :=
        TauCeti.LinearMap.exists_linearIsometryEquiv_norm_sub_apply_le M hδlt hclose
      refine ⟨W.toLinearEquiv.toLinearMap,
        fun x y => W.inner_map_map x y, fun x => ?_⟩
      rw [LinearMap.sub_apply]
      have hprod : 0 ≤ δ * ‖x‖ := mul_nonneg hδ0 (norm_nonneg x)
      exact (hWsharp x).trans (by nlinarith)
    · have hδge : 1 ≤ δ := le_of_not_gt hδlt
      let e : Fin d ↪ Fin n := Fin.castLEEmb hd
      have hu := TauCeti.isOrderedEigenframe_eigenvectorBasis hT hn_eq e
      have hv := TauCeti.isOrderedEigenframe_eigenvectorBasis hS hn_eq e
      have hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
          α ≤ |hT.eigenvalues hn_eq (e i) - hT.eigenvalues hn_eq k| := by
        intro i k hk
        have hkge : d ≤ (k : ℕ) := by
          by_contra hkd
          apply hk
          refine ⟨⟨(k : ℕ), Nat.lt_of_not_ge hkd⟩, ?_⟩
          apply Fin.ext
          rfl
        have hlead : α ≤ hT.eigenvalues hn_eq (e i) := by
          apply hα
          simp [e]
        have hlead0 : 0 ≤ hT.eigenvalues hn_eq (e i) :=
          le_trans (le_of_lt hα_pos) hlead
        rw [htail k hkge, sub_zero, abs_of_nonneg hlead0]
        exact hlead
      obtain ⟨W, hWiso, _hWalign⟩ :=
        YuWangSamworth2015.yuWangSamworth_alignmentMap_sub_overlapOp_apply_le
          hu hv hα_pos hgap
      have hM_overlap :
          M = TauCeti.overlapOp hu.orthonormal hv.orthonormal := by
        apply LinearMap.ext
        intro x
        ext l
        rw [hM, nearIsometry_apply, TauCeti.overlapOp_coord,
          TauCeti.familyIsometry_apply, inner_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [real_inner_smul_right]
        simp only [Acharyya2025.Overlap.overlap]
        rw [real_inner_comm]
        simp [e, mul_comm]
      refine ⟨W, hWiso, fun x => ?_⟩
      have hMnorm : ‖M x‖ ≤ ‖x‖ := by
        rw [hM_overlap]
        exact TauCeti.overlapOp_contraction hu.orthonormal hv.orthonormal x
      have hWnorm : ‖W x‖ = ‖x‖ := by
        have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
            hWiso x x]
        nlinarith [norm_nonneg (W x), norm_nonneg x]
      rw [LinearMap.sub_apply]
      calc
        ‖M x - W x‖ ≤ ‖M x‖ + ‖W x‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖x‖ := add_le_add hMnorm (le_of_eq hWnorm)
        _ = 2 * ‖x‖ := by ring
        _ ≤ 2 * δ * ‖x‖ := by
          have hprod : 0 ≤ (δ - 1) * ‖x‖ :=
            mul_nonneg (sub_nonneg.mpr hδge) (norm_nonneg x)
          nlinarith
  refine ⟨W, hWiso, ?_⟩
  -- The total error and the three terms as product-space vectors.
  set etot : EuclideanSpace ℝ (Fin n × Fin d) :=
    WithLp.toLp 2 (fun p : Fin n × Fin d =>
      (W (spectralConfig S hS hd p.1)) p.2 - (spectralConfig T hT hd p.1) p.2) with hetot
  set t1 : EuclideanSpace ℝ (Fin n × Fin d) :=
    WithLp.toLp 2 (fun p : Fin n × Fin d =>
      ((W - M) (spectralConfig S hS hd p.1)) p.2) with ht1
  have hsplit : etot = t1 + term2vec hT hS hd + term3vec hT hS hd := by
    apply (WithLp.linearEquiv 2 ℝ _).injective
    ext p
    obtain ⟨i, l⟩ := p
    -- expand each coordinate
    show (W (spectralConfig S hS hd i)) l - (spectralConfig T hT hd i) l
      = _
    -- LHS pieces; RHS pieces via term apply lemmas
    have hMpsi : (M (spectralConfig S hS hd i)) l
        = ∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k)
                * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i) := by
      rw [hM, nearIsometry_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show (spectralConfig S hS hd i) k = spectralConfig S hS hd i k from rfl,
        spectralConfig_apply]
    have ht1coord : t1 (i, l) = (W (spectralConfig S hS hd i)) l - (M (spectralConfig S hS hd i)) l := by
      show ((W - M) (spectralConfig S hS hd i)) l = _
      rw [LinearMap.sub_apply]; rfl
    have ht3coord : (term3vec hT hS hd) (i, l)
        = Real.sqrt (lamPop hT hd l)
          * ((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
                * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)
              - hT.eigenvectorBasis hn_eq (Fin.castLE hd l) i) := by
      rw [term3vec_apply]
      congr 1
      rw [show (((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k))
          - hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) i)
          = ((∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            • hS.eigenvectorBasis hn_eq (Fin.castLE hd k)) i)
            - (hT.eigenvectorBasis hn_eq (Fin.castLE hd l)) i from rfl]
      rw [smul_sum_apply]
    have hψcoord : (spectralConfig T hT hd i) l
        = Real.sqrt (lamPop hT hd l) * hT.eigenvectorBasis hn_eq (Fin.castLE hd l) i := by
      rw [show (spectralConfig T hT hd i) l = spectralConfig T hT hd i l from rfl]
      rfl
    show (W (spectralConfig S hS hd i)) l - (spectralConfig T hT hd i) l
      = t1 (i, l) + (term2vec hT hS hd) (i, l) + (term3vec hT hS hd) (i, l)
    rw [ht1coord, hMpsi, term2vec_apply, ht3coord, hψcoord]
    -- telescoping
    have h1 : (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k) - Real.sqrt (lamPop hT hd l))
            * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)
        = (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
            * (Real.sqrt (lamHat hS hd k)
              * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i))
          - (∑ k, Real.sqrt (lamPop hT hd l)
              * ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
                * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    have h2 : Real.sqrt (lamPop hT hd l)
          * (∑ k, (Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i)
        = ∑ k, Real.sqrt (lamPop hT hd l)
            * ((Acharyya2025.Overlap.overlap hT hS hn_eq hd) k l
              * hS.eigenvectorBasis hn_eq (Fin.castLE hd k) i) := by
      rw [Finset.mul_sum]
    rw [h1, mul_sub, h2]
    ring
  -- Minkowski: `‖etot‖ ≤ ‖t1‖ + ‖t2‖ + ‖t3‖`.
  have hmink : ‖etot‖ ≤ ‖t1‖ + ‖term2vec hT hS hd‖ + ‖term3vec hT hS hd‖ := by
    rw [hsplit]
    refine le_trans (norm_add_le (t1 + term2vec hT hS hd) (term3vec hT hS hd)) ?_
    gcongr
    exact norm_add_le t1 (term2vec hT hS hd)
  -- Term-1 norm bound.
  have ht1bound : ‖t1‖ ≤
      Real.sqrt ((2 * δ)^2 * ((d : ℝ) * (Λ + ε))) := by
    have ht1sq : ‖t1‖^2 ≤ (2 * δ)^2 * ((d : ℝ) * (Λ + ε)) := by
      rw [frob_sq]
      have hperi : ∀ i : Fin n, ∑ l : Fin d, (t1 (i, l))^2
          ≤ (2 * δ)^2 * ‖spectralConfig S hS hd i‖^2 := by
        intro i
        have hcoord : ∀ l : Fin d, t1 (i, l) = ((W - M) (spectralConfig S hS hd i)) l := by
          intro l; rfl
        have hnorm : ∑ l : Fin d, (t1 (i, l))^2 = ‖(W - M) (spectralConfig S hS hd i)‖^2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcoord l]; simp [Real.norm_eq_abs, sq_abs]
        rw [hnorm]
        have hWM : ‖(W - M) (spectralConfig S hS hd i)‖ = ‖(M - W) (spectralConfig S hS hd i)‖ := by
          rw [show (W - M) (spectralConfig S hS hd i) = -((M - W) (spectralConfig S hS hd i)) by
            rw [LinearMap.sub_apply, LinearMap.sub_apply]; abel, norm_neg]
        rw [hWM]
        have h2δ := hWclose (spectralConfig S hS hd i)
        have h0 : 0 ≤ ‖(M - W) (spectralConfig S hS hd i)‖ := norm_nonneg _
        calc ‖(M - W) (spectralConfig S hS hd i)‖^2
            ≤ (2 * δ * ‖spectralConfig S hS hd i‖)^2 := by
              apply sq_le_sq'
              · linarith [h0, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ0)
                  (norm_nonneg (spectralConfig S hS hd i))]
              · exact h2δ
          _ = (2 * δ)^2 * ‖spectralConfig S hS hd i‖^2 := by ring
      calc ∑ i : Fin n, ∑ l : Fin d, (t1 (i, l))^2
          ≤ ∑ i : Fin n, (2 * δ)^2 * ‖spectralConfig S hS hd i‖^2 := Finset.sum_le_sum (fun i _ => hperi i)
        _ = (2 * δ)^2 * ∑ i : Fin n, ‖spectralConfig S hS hd i‖^2 := by rw [Finset.mul_sum]
        _ ≤ (2 * δ)^2 * ((d : ℝ) * (Λ + ε)) :=
            mul_le_mul_of_nonneg_left
              (sum_norm_sq_spectralConfig_le hd hT hS hα_pos hα hΛ hε) (by positivity)
    calc ‖t1‖ = Real.sqrt (‖t1‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((2 * δ)^2 * ((d : ℝ) * (Λ + ε))) := Real.sqrt_le_sqrt ht1sq
  -- Term-2 norm bound.
  have ht2bound : ‖term2vec hT hS hd‖ ≤ Real.sqrt ((d : ℝ) * (ε / Real.sqrt α)^2) := by
    calc ‖term2vec hT hS hd‖ = Real.sqrt (‖term2vec hT hS hd‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((d : ℝ) * (ε / Real.sqrt α)^2) :=
          Real.sqrt_le_sqrt (term2_norm_sq_le hd hT hS hα_pos hα hε)
  -- Term-3 norm bound.
  have ht3bound : ‖term3vec hT hS hd‖ ≤ Real.sqrt (Λ * (4 * (d : ℝ) * ε^2 / α^2)) := by
    calc ‖term3vec hT hS hd‖ = Real.sqrt (‖term3vec hT hS hd‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (Λ * (4 * (d : ℝ) * ε^2 / α^2)) :=
          Real.sqrt_le_sqrt (term3_norm_sq_le hd hT hS hα_pos hα htail hΛ hε)
  -- The product-space norm is exactly the Frobenius configuration error.
  have hai : ∀ i : Fin n,
      ‖W (spectralConfig S hS hd i) - spectralConfig T hT hd i‖
        = Real.sqrt (∑ l : Fin d, (etot (i, l))^2) := by
    intro i
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    show ‖(W (spectralConfig S hS hd i) - spectralConfig T hT hd i) l‖^2 =
      (etot (i, l))^2
    rw [hetot]
    show ‖(W (spectralConfig S hS hd i)) l - (spectralConfig T hT hd i) l‖^2 = _
    rw [Real.norm_eq_abs, sq_abs]
  have hfrob : ConfigFrobError
      (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd) = ‖etot‖ := by
    unfold ConfigFrobError
    have hsumsq :
        (∑ i : Fin n,
          ‖W (spectralConfig S hS hd i) - spectralConfig T hT hd i‖^2) =
          ∑ i : Fin n, ∑ l : Fin d, (etot (i, l))^2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hai i, Real.sq_sqrt (by positivity)]
    rw [hsumsq, ← frob_sq etot, Real.sqrt_sq (norm_nonneg _)]
  rw [hfrob]
  calc
    ‖etot‖ ≤ ‖t1‖ + ‖term2vec hT hS hd‖ + ‖term3vec hT hS hd‖ := hmink
    _ ≤ configFrobBound d α Λ ε := by
      rw [configFrobBound]
      exact add_le_add (add_le_add ht1bound ht2bound) ht3bound


/--
Compatibility form of the configuration perturbation theorem in the repository's
legacy `ConfigError` metric.  It is now a direct corollary of the Frobenius
paper-facing theorem plus `ConfigError ≤ √n · ConfigFrobError`.
-/
theorem exists_isometry_configError_spectralConfig_le
    {n d : ℕ} (hd : d ≤ n)               -- embedding dimension/rank `d ≤ n` (Assumption 1: rank = d)
    (T S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))  -- `T` population, `S` sample Gram operators
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)  -- extra (encoding) assumption: operators are symmetric/self-adjoint
    {α Λ ε : ℝ} (hα_pos : 0 < α) (hε_nonneg : 0 ≤ ε)  -- floor `α > 0`, perturbation `ε ≥ 0`
    -- Assumption 2 (lower): leading `d` population eigenvalues `≥ α` (paper's `λ_d`/`C1`):
    (hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues finrank_euclideanSpace_fin i)
    -- Assumption 1 (rank = d, encoded): all trailing population eigenvalues vanish:
    (htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues finrank_euclideanSpace_fin j = 0)
    -- Assumption 2 (upper): all population eigenvalues `≤ Λ` (paper's `λ_1`/`C2`):
    (hΛ : ∀ l : Fin n, hT.eigenvalues finrank_euclideanSpace_fin l ≤ Λ)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :  -- sample/population operator-norm closeness `‖S − T‖ ≤ ε`
    -- Conclusion: there is an isometry `W` of `ℝ^d` aligning the sample embedding to the
    -- population embedding with configuration error `≤ configBound n d α Λ ε`.
    ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      Acharyya2024.ConfigError (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd)
        ≤ configBound n d α Λ ε  := by
  obtain ⟨W, hWiso, hWfrob⟩ :=
    exists_isometry_configFrobError_spectralConfig_le hd T S hT hS hα_pos hε_nonneg
      hα htail hΛ hε
  refine ⟨W, hWiso, ?_⟩
  calc
    Acharyya2024.ConfigError (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd)
        ≤ Real.sqrt n * ConfigFrobError
            (fun i => W (spectralConfig S hS hd i)) (spectralConfig T hT hd) :=
          configError_le_sqrt_mul_ConfigFrobError _ _
    _ ≤ Real.sqrt n * configFrobBound d α Λ ε :=
      mul_le_mul_of_nonneg_left hWfrob (Real.sqrt_nonneg _)
    _ = configBound n d α Λ ε :=
      (configBound_eq_sqrt_mul_configFrobBound n d α Λ ε).symm

end Acharyya2025.ConfigPerturbation
