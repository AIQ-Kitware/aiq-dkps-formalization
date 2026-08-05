/-
WP6-core — matrix-world assembly (transport layer) of `planning/acharyya-plan.md`.

The operator-world configuration-perturbation theorem
`Acharyya2025.ConfigPerturbation.exists_isometry_configError_spectralConfig_le`
is stated for symmetric operators `T, S` on `EuclideanSpace ℝ (Fin n)` with the
sorted-eigenvalue hypotheses (spectral floor `α`, rank-`d` tail, top eigenvalue
`≤ Λ`).  This file is the *transport layer* that lets the matrix world
(`B, Bhat : Matrix (Fin n) (Fin n) ℝ`) invoke that theorem.

Given a population Gram matrix `B` that is positive semidefinite with
`B.rank ≤ d` and an entrywise-close Hermitian sample `Bhat`, set
`T := Matrix.toEuclideanLin B`, `S := Matrix.toEuclideanLin Bhat`.  We prove:

The sorted-eigenvalue hypotheses are stated against Mathlib's
`Matrix.IsHermitian.eigenvalues₀`; nonnegativity and the vanishing rank-`d` tail are
`TauCeti.Matrix.PosSemidef.eigenvalues₀_nonneg` and
`TauCeti.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le`.  We prove:

* `rank_eq_finrank_range_toEuclideanLin` — the matrix rank of `B` is the finrank of the
  range of `toEuclideanLin B`, which is what carries the rank hypothesis across;
* `gram_spectralConfig_eq` — the Gram matrix of the spectral configuration
  `spectralConfig T` equals `B` (operator spectral expansion evaluated at the
  standard basis vectors);
* `exists_isometry_configError_le_of_entrywise_close` — the **matrix-world
  assembly**: for any external configuration `ψ` realizing `B` as its Gram
  matrix, the sample spectral embedding `spectralConfig S`, transported by a
  single linear isometry `W`, is `configBound`-close to `ψ`.

The assembly combines the operator bound (via `OperatorBridge`), the rank/PSD
eigenvalue transport, the Gram identity, and Gram rigidity
(`Acharyya2025.GramRigidity`).

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/

import Mathlib
import Acharyya2024.Common
import Acharyya2025.ConfigPerturbation
import Acharyya2025.OperatorBridge
import Acharyya2025.GramRigidity
import Acharyya2025.GramRealization
import ForTauCeti.Analysis.Matrix.Spectrum
import ForTauCeti.Analysis.Matrix.SpectralFunctionMeasurable

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix
open Module (finrank)

namespace Acharyya2025.MatrixPerturbation

open Acharyya2025.ConfigPerturbation
open Acharyya2025.OperatorBridge
open TauCeti.Matrix (opSym eigenvalues₀_eq_eigenvalues_toEuclideanLin
  eigenvalues_toEuclideanLin_eq_eigenvalues₀)

variable {n d : ℕ}

/-! The sorted (decreasing) eigenvalues `λ₀ ≥ λ₁ ≥ …` of a Hermitian `B` are Mathlib's
`Matrix.IsHermitian.eigenvalues₀`, indexed by `Fin (Fintype.card (Fin n))`.  Consumers state
spectral floors (the paper's `α`, from Assumption 2) and the rank-`d` vanishing tail against
that.  The operator layer of this development enumerates the same eigenvalues at index
`Fin n`, through `finrank_euclideanSpace_fin`; `TauCeti.Matrix` carries the transport
between the two indexings, which is not definitional because `Fintype.card (Fin n) = n` is a
theorem. -/

/-! ### Deliverable (2a): nonnegativity of the sorted eigenvalues

A positive semidefinite matrix `B` induces a *positive* operator
`toEuclideanLin B`: the quadratic form `⟪T x, x⟫` equals the matrix quadratic
form `ofLp x ⬝ᵥ (B *ᵥ ofLp x)`, which is `≥ 0` by definition of `PosSemidef`.
`LinearMap.IsPositive.nonneg_eigenvalues` then gives nonnegativity. -/

/-- Internal helper.
The quadratic form of `toEuclideanLin B` equals the matrix quadratic form
`star x ⬝ᵥ (B *ᵥ x)` on the underlying coordinate vector (over ℝ, `star = id`). -/
private theorem inner_toEuclideanLin_self {B : Matrix (Fin n) (Fin n) ℝ}
    (x : EuclideanSpace ℝ (Fin n)) :
    -- Conclusion: operator quadratic form ⟪Bx, x⟫ = the matrix quadratic form xᵀ B x.
    ⟪Matrix.toEuclideanLin B x, x⟫_ℝ
      = star (WithLp.ofLp x) ⬝ᵥ (B *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  show WithLp.ofLp x ⬝ᵥ star (B *ᵥ WithLp.ofLp x) = _
  -- over ℝ, `star = id`.
  simp only [star_trivial]

/-- Internal helper.
A positive semidefinite matrix induces a positive operator (the operator
encoding of PSD: its quadratic form is `≥ 0`). -/
-- `hB` : `B` is positive semidefinite (PSD) — the paper's Gram/doubly-centered B.
theorem isPositive_toEuclideanLin {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    -- Conclusion: `toEuclideanLin B` is a positive operator.
    (Matrix.toEuclideanLin B).IsPositive := by
  refine ⟨opSym hB.isHermitian, fun x => ?_⟩
  rw [inner_toEuclideanLin_self x]
  -- the inner product is real, so `re` is the identity
  simpa using hB.dotProduct_mulVec_nonneg (WithLp.ofLp x)

/-- The canonical spectral ceiling of a nonempty positive-semidefinite matrix:
its largest sorted eigenvalue.

The upper spectral bound used by the configuration perturbation estimate is not
an independent assumption in finite dimension.  Antitonicity of the sorted
eigenvalues makes the leading eigenvalue a canonical valid ceiling. -/
noncomputable def topEigenvalue {B : Matrix (Fin n) (Fin n) ℝ}
    (hn : 0 < n) (hB : B.PosSemidef) : ℝ :=
  hB.isHermitian.eigenvalues₀ ⟨0, by simpa using hn⟩

/-- The canonical spectral ceiling is nonnegative. -/
theorem topEigenvalue_nonneg {B : Matrix (Fin n) (Fin n) ℝ}
    (hn : 0 < n) (hB : B.PosSemidef) :
    0 ≤ topEigenvalue hn hB :=
  TauCeti.Matrix.PosSemidef.eigenvalues₀_nonneg hB _

/-- Every sorted eigenvalue is bounded by the canonical leading-eigenvalue
ceiling. -/
theorem eigenvalues₀_le_topEigenvalue {B : Matrix (Fin n) (Fin n) ℝ}
    (hn : 0 < n) (hB : B.PosSemidef) (i : Fin (Fintype.card (Fin n))) :
    hB.isHermitian.eigenvalues₀ i ≤ topEigenvalue hn hB :=
  hB.isHermitian.eigenvalues₀_antitone (Fin.mk_le_of_le_val (Nat.zero_le _))

/-! ### Deliverable (2b): tail eigenvalues vanish (rank transport)

For positive semidefinite `B` with `B.rank ≤ d` the sorted eigenvalues vanish from index
`d` on — the paper's rank-`d` structure (Assumption 1).  That is
`TauCeti.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le`, which counts nonzero sorted
eigenvalues against the rank; the transport below relates the matrix rank to the range of
the induced operator and is what the configuration bound consumes. -/

/-- Internal helper (rank transport).
The matrix rank of `B` equals the dimension of the range of `toEuclideanLin B`.
This ties the paper's matrix rank (Assumption 1, rank(B) = d) to the operator's
range dimension. -/
theorem rank_eq_finrank_range_toEuclideanLin (B : Matrix (Fin n) (Fin n) ℝ) :
    -- Conclusion: matrix rank of B = dim of the operator's range.
    B.rank = finrank ℝ (LinearMap.range (Matrix.toEuclideanLin B)) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin B
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-! ### Deliverable (3): the Gram identity

The Gram matrix of the spectral configuration of `T := toEuclideanLin B` is `B`.
This is the operator spectral expansion `T x = ∑_k λ_k ⟪u_k, x⟫ • u_k`, evaluated
at the standard basis vector `x := single j 1`, whose `i`-th coordinate gives
`B i j`. -/

/-- Internal helper (entry recovery).
The `(i, j)` matrix entry is the `i`-th coordinate of `T (single j 1)`. -/
private theorem toEuclideanLin_single_apply (B : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    -- Conclusion: applying the operator to the j-th basis vector recovers column j of B.
    (Matrix.toEuclideanLin B (EuclideanSpace.single j (1 : ℝ))) i = B i j := by
  show (B *ᵥ WithLp.ofLp (EuclideanSpace.single j (1 : ℝ))) i = B i j
  rw [PiLp.ofLp_single, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- Internal helper (operator spectral expansion, coordinatewise).
`(T x) i = ∑_k λ_k ⟪u_k, x⟫ u_k(i)` — the eigen-decomposition read off one
coordinate at a time. -/
private theorem toEuclideanLin_apply_eq_sum {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian)            -- `B` Hermitian (real symmetric)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    -- Conclusion: i-th coordinate of T x equals the eigen-expansion ∑ₖ λₖ ⟪uₖ,x⟫ uₖ(i).
    (Matrix.toEuclideanLin B x) i
      = ∑ k : Fin n, (opSym hB).eigenvalues finrank_euclideanSpace_fin k
          * ⟪(opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k, x⟫_ℝ
          * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i) := by
  set hS := opSym hB with hSdef
  set u := hS.eigenvectorBasis finrank_euclideanSpace_fin with hu
  -- expand `x` in the eigenbasis, apply `T`, use the diagonal action.
  have hTx : Matrix.toEuclideanLin B x
      = ∑ k : Fin n, ((opSym hB).eigenvalues finrank_euclideanSpace_fin k * ⟪u k, x⟫_ℝ) • u k := by
    conv_lhs => rw [← u.sum_repr' x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, hu, hS.apply_eigenvectorBasis]
    rw [smul_smul]
    congr 1
    show ⟪hS.eigenvectorBasis finrank_euclideanSpace_fin k, x⟫_ℝ * ((opSym hB).eigenvalues finrank_euclideanSpace_fin k : ℝ) = _
    rw [mul_comm]
  rw [hTx]
  -- read off the `i`-th coordinate of the finite sum.
  have hcoord : (∑ k : Fin n, ((opSym hB).eigenvalues finrank_euclideanSpace_fin k * ⟪u k, x⟫_ℝ) • u k) i
      = ∑ k : Fin n, ((opSym hB).eigenvalues finrank_euclideanSpace_fin k * ⟪u k, x⟫_ℝ) * (u k) i := by
    show (∑ k : Fin n, ((opSym hB).eigenvalues finrank_euclideanSpace_fin k * ⟪u k, x⟫_ℝ) • u k).ofLp i = _
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [WithLp.ofLp_smul]; rfl
  rw [hcoord]

/-- Internal helper.
The operator spectral expansion of a single matrix entry:
`B i j = ∑_k λ_k u_k(i) u_k(j)` (spectral theorem, entrywise). -/
private theorem entry_eq_sum_eigenvalues {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian)            -- `B` Hermitian (real symmetric)
    (i j : Fin n) :
    -- Conclusion: B i j = ∑ₖ λₖ uₖ(i) uₖ(j) (entrywise spectral decomposition).
    B i j = ∑ k : Fin n, (opSym hB).eigenvalues finrank_euclideanSpace_fin k
        * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k i)
        * ((opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j) := by
  rw [← toEuclideanLin_single_apply B i j, toEuclideanLin_apply_eq_sum hB]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- `⟪u_k, single j 1⟫ = u_k(j)` over ℝ.
  have hinner : ⟪(opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k, EuclideanSpace.single j (1 : ℝ)⟫_ℝ
      = (opSym hB).eigenvectorBasis finrank_euclideanSpace_fin k j := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [hinner]; ring

/-- Internal helper (reindexing bookkeeping).
Local copy of the `castLE`-image reindexing
(`ConfigPerturbation.sum_castLE_eq_filter` is private):
`∑_{m : Fin d} f (castLE m) = ∑_{j : j < d} f j`. -/
private theorem sum_castLE_eq_filter {d : ℕ} (hd : d ≤ n) (f : Fin n → ℝ) :
    -- Conclusion: a sum over the first d indices equals the filtered sum {j < d}.
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

/-- **Deliverable (3): the Gram identity.**  The Gram matrix of the spectral
configuration of `T := toEuclideanLin B` equals `B`, for positive semidefinite
`B` with `B.rank ≤ d`.  In paper terms: the `d`-dimensional spectral embedding
(classical MDS coordinates) of the population matrix `B` reproduces `B` as its
Gram matrix — the embedding really does realize `B`. -/
theorem gram_spectralConfig_eq {d : ℕ} (hd : d ≤ n)
    {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef)             -- `B` positive semidefinite (PSD)
    (hrank : B.rank ≤ d) :          -- rank bound: rank(B) ≤ d (Assumption 1)
    -- Conclusion: the Gram matrix of the spectral embedding equals B (the embedding realizes B).
    ∀ i j : Fin n,
      (∑ k : Fin d, spectralConfig (Matrix.toEuclideanLin B) (opSym hB.isHermitian) hd i k
          * spectralConfig (Matrix.toEuclideanLin B) (opSym hB.isHermitian) hd j k)
        = B i j := by
  intro i j
  set hS := opSym hB.isHermitian with hSdef
  set u := hS.eigenvectorBasis finrank_euclideanSpace_fin with hu
  set lam := hS.eigenvalues finrank_euclideanSpace_fin with hlam
  have hlam_nonneg : ∀ k : Fin n, 0 ≤ lam k := by
    intro k
    rw [hlam, eigenvalues_toEuclideanLin_eq_eigenvalues₀]
    exact TauCeti.Matrix.PosSemidef.eigenvalues₀_nonneg hB _
  -- `√λ_{castLE k} · √λ_{castLE k} = λ_{castLE k}` since `λ ≥ 0`.
  have hsqsq : ∀ k : Fin d,
      spectralConfig (Matrix.toEuclideanLin B) hS hd i k
        * spectralConfig (Matrix.toEuclideanLin B) hS hd j k
        = lam (Fin.castLE hd k) * (u (Fin.castLE hd k) i) * (u (Fin.castLE hd k) j) := by
    intro k
    show (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) i)
        * (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) j) = _
    have hsq : Real.sqrt (lam (Fin.castLE hd k)) * Real.sqrt (lam (Fin.castLE hd k))
        = lam (Fin.castLE hd k) :=
      Real.mul_self_sqrt (hlam_nonneg _)
    calc (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) i)
            * (Real.sqrt (lam (Fin.castLE hd k)) * u (Fin.castLE hd k) j)
        = (Real.sqrt (lam (Fin.castLE hd k)) * Real.sqrt (lam (Fin.castLE hd k)))
            * (u (Fin.castLE hd k) i * u (Fin.castLE hd k) j) := by ring
      _ = lam (Fin.castLE hd k) * (u (Fin.castLE hd k) i) * (u (Fin.castLE hd k) j) := by
            rw [hsq]; ring
  -- the configuration sum over `Fin d` collapses to the leading filtered sum.
  rw [Finset.sum_congr rfl (fun k _ => hsqsq k)]
  rw [sum_castLE_eq_filter hd (fun k : Fin n => lam k * (u k i) * (u k j))]
  -- extend the leading sum to all of `Fin n`: tail terms vanish (`λ = 0`).
  have htail : ∀ k : Fin n, d ≤ (k : ℕ) → lam k = 0 := by
    intro k hk
    rw [hlam, eigenvalues_toEuclideanLin_eq_eigenvalues₀]
    exact TauCeti.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le hB hrank (by simpa using hk)
  have hext : ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < d),
        (lam k * (u k i) * (u k j))
      = ∑ k : Fin n, (lam k * (u k i) * (u k j)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => (k : ℕ) < d)]
    have hzero : ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ ((k : ℕ) < d)),
        (lam k * (u k i) * (u k j)) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hge : d ≤ (k : ℕ) := by
        have := (Finset.mem_filter.mp hk).2; omega
      rw [htail k hge]; ring
    rw [hzero, add_zero]
  rw [hext]
  -- the full spectral sum is `B i j`.
  rw [entry_eq_sum_eigenvalues hB.isHermitian i j]

/-! ### Deliverable (4): the matrix-world assembly

Assemble: operator closeness (`OperatorBridge`), the rank/PSD eigenvalue
transport, the operator-world configuration bound
(`ConfigPerturbation.exists_isometry_configError_spectralConfig_le`), the Gram
identity, and Gram rigidity (`GramRigidity.exists_linearIsometryEquiv_of_gram_eq`). -/

/-- **Matrix-world assembly.**

Let `B` be a positive semidefinite Gram matrix with `B.rank ≤ d` (population),
and `Bhat` a Hermitian sample matrix entrywise `η`-close to `B`.  Set
`ε := n·η`.  Under the operator-side hypotheses (spectral floor `α`, top
eigenvalue `≤ Λ`, smallness `n·η ≤ α/2`, polar-factor smallness), for *any*
external configuration `ψ` realizing `B` as its Gram matrix, the sample spectral
embedding `spectralConfig (toEuclideanLin Bhat)`, transported by a single linear
isometry `W`, is `configBound n d α Λ (n·η)`-close to `ψ`.

This is the matrix-world deterministic core *behind* the paper's **Theorem 2**
(`‖ψ̂W* − ψ‖ ≤ κ` with high probability): once the sample matrix B̂ is entrywise
close to the population B, the spectral embedding of B̂ — after an aligning
isometry `W` (playing the role of the paper's `W*`; optimality/uniqueness is not
established here) — is uniformly close to the true embedding `ψ`.  Theorem 2 is
itself probabilistic; this lemma is the deterministic perturbation bound that
*corresponds to / feeds* it.  The probabilistic step (concentration of
`‖B̂ − B‖`) is *not* part of this lemma; this provides the deterministic
perturbation bound that Weyl and Davis–Kahan feed.

Formalized by Claude Fable 5 (claude-fable-5[1m]). -/
theorem exists_isometry_configError_le_of_entrywise_close
    {n d : ℕ} (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef)             -- population `B` positive semidefinite (PSD)
    (hBhat : Bhat.IsHermitian)      -- sample `Bhat` Hermitian (real symmetric)
    (hrank : B.rank ≤ d)            -- rank bound: rank(B) ≤ d (Assumption 1)
    {α Λ η : ℝ} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    -- eigenvalue floor α (Assumption 2, lower)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    -- eigenvalue ceiling Λ (Assumption 2, upper)
    (hΛ : ∀ l : Fin (Fintype.card (Fin n)), hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)   -- entrywise closeness: |B̂ᵢⱼ − Bᵢⱼ| ≤ η
    (hsmall : (n : ℝ) * η ≤ α / 2)              -- smallness: perturbation ≤ half the floor (Weyl/gap)
    (hpolar : (d : ℝ) * (4 * (n : ℝ) * ((n : ℝ) * η)^2 / α^2) ≤ 1/2) -- polar-factor smallness (Davis–Kahan term ≤ 1/2)
    (ψ : Acharyya2024.Config n d)               -- any external configuration realizing B
    (hψ : ∀ i j, (∑ k : Fin d, ψ i k * ψ j k) = B i j) :  -- ψ has Gram matrix B
    -- Conclusion: ∃ a linear isometry W (an aligning isometry playing the role of the paper's `W*`;
    -- optimality/uniqueness is not established here) such that the W-transported sample spectral
    -- embedding is configBound-close to ψ (the deterministic core feeding Theorem 2).
    ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      Acharyya2024.ConfigError
        (fun i => W (spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i)) ψ
        ≤ configBound n d α Λ ((n : ℝ) * η) := by
  set T := Matrix.toEuclideanLin B with hTdef
  set S := Matrix.toEuclideanLin Bhat with hSdef
  set hT := opSym hB.isHermitian with hTsym
  set hSsym := opSym hBhat with hSsymdef
  set ε : ℝ := (n : ℝ) * η with hε
  have hε_nonneg : 0 ≤ ε := by rw [hε]; positivity
  -- operator-norm closeness: `‖(S − T) x‖ ≤ ε ‖x‖`.
  have hclose : ∀ x : EuclideanSpace ℝ (Fin n), ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    have hbridge := matrixL2OperatorClose_of_entrywise
      (A := Bhat) (B := B) (ε := η) hentry
    intro x
    -- `(S − T) x = toEuclideanLin (Bhat − B) x` via `map_sub`.
    have hmapsub : (S - T) x = Matrix.toEuclideanLin (Bhat - B) x := by
      rw [hSdef, hTdef, ← map_sub]
    rw [hmapsub]
    exact hbridge x
  -- the eigenvalue hypotheses, restated against the operator's sorted eigenvalues.
  have hα : ∀ i : Fin n, (i : ℕ) < d → α ≤ hT.eigenvalues finrank_euclideanSpace_fin i := by
    intro i hi
    rw [hTsym, eigenvalues_toEuclideanLin_eq_eigenvalues₀]
    exact hfloor _ (by simpa using hi)
  have htail : ∀ j : Fin n, d ≤ (j : ℕ) → hT.eigenvalues finrank_euclideanSpace_fin j = 0 := by
    intro j hj
    rw [hTsym, eigenvalues_toEuclideanLin_eq_eigenvalues₀]
    exact TauCeti.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le hB hrank (by simpa using hj)
  have hΛ' : ∀ l : Fin n, hT.eigenvalues finrank_euclideanSpace_fin l ≤ Λ := by
    intro l
    rw [hTsym, eigenvalues_toEuclideanLin_eq_eigenvalues₀]
    exact hΛ _
  -- operator-world configuration bound: alignment `W₀`.
  obtain ⟨W₀, hW₀_isom, hW₀_bound⟩ :=
    exists_isometry_configError_spectralConfig_le hd T S hT hSsym hα_pos hε_nonneg
      hα htail hΛ' hclose hsmall hpolar
  -- Gram rigidity: Gram(spectralConfig T) = B = Gram(ψ), so an isometry `V` aligns them.
  have hgramT : ∀ i j : Fin n,
      (∑ k : Fin d, spectralConfig T hT hd i k * spectralConfig T hT hd j k) = B i j :=
    gram_spectralConfig_eq hd hB hrank
  obtain ⟨V, hV⟩ := Acharyya2025.GramRigidity.exists_linearIsometryEquiv_of_gram_eq
    (spectralConfig T hT hd) ψ (fun i j => by rw [hgramT i j, hψ i j])
  -- the combined isometry `W := V ∘ W₀`.
  refine ⟨V.toLinearMap ∘ₗ W₀, ?_, ?_⟩
  · -- `W` preserves inner products (composition of isometries).
    intro x y
    show ⟪V (W₀ x), V (W₀ y)⟫_ℝ = ⟪x, y⟫_ℝ
    rw [V.inner_map_map, hW₀_isom x y]
  · -- ConfigError comparison: `V` linear isometry preserves norms.
    have hConfigEq : Acharyya2024.ConfigError
        (fun i => (V.toLinearMap ∘ₗ W₀) (spectralConfig S hSsym hd i)) ψ
        = Acharyya2024.ConfigError
            (fun i => W₀ (spectralConfig S hSsym hd i)) (spectralConfig T hT hd) := by
      unfold Acharyya2024.ConfigError
      refine Finset.sum_congr rfl (fun i _ => ?_)
      -- `‖V(W₀ ψ̂ᵢ) − ψᵢ‖ = ‖V(W₀ ψ̂ᵢ) − V(spectralConfig T ᵢ)‖ = ‖W₀ ψ̂ᵢ − spectralConfig T ᵢ‖`.
      have hψi : ψ i = V (spectralConfig T hT hd i) := (hV i).symm
      show ‖V (W₀ (spectralConfig S hSsym hd i)) - ψ i‖
          = ‖W₀ (spectralConfig S hSsym hd i) - spectralConfig T hT hd i‖
      rw [hψi, ← map_sub, V.norm_map]
    rw [hConfigEq]
    exact hW₀_bound


/-- Matrix-world assembly with the spectral ceiling chosen canonically as the
largest population eigenvalue.

This removes the redundant `Λ` and `hΛ` inputs from the deterministic theorem.
Only the positive lower spectral floor remains a genuine stability condition. -/
theorem exists_isometry_configError_le_of_entrywise_close_topEigenvalue
    {n d : ℕ} (hn : 0 < n) (hd : d ≤ n)
    (B Bhat : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef)
    (hBhat : Bhat.IsHermitian)
    (hrank : B.rank ≤ d)
    {α η : ℝ} (hα_pos : 0 < α) (hη_nonneg : 0 ≤ η)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hentry : ∀ i j, |Bhat i j - B i j| ≤ η)
    (hsmall : (n : ℝ) * η ≤ α / 2)
    (hpolar : (d : ℝ) * (4 * (n : ℝ) * ((n : ℝ) * η)^2 / α^2) ≤ 1/2)
    (ψ : Acharyya2024.Config n d)
    (hψ : ∀ i j, (∑ k : Fin d, ψ i k * ψ j k) = B i j) :
    ∃ W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x y, ⟪W x, W y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
      Acharyya2024.ConfigError
        (fun i => W (spectralConfig (Matrix.toEuclideanLin Bhat) (opSym hBhat) hd i)) ψ
        ≤ configBound n d α (topEigenvalue hn hB) ((n : ℝ) * η) := by
  exact exists_isometry_configError_le_of_entrywise_close hd B Bhat hB hBhat hrank
    hα_pos hη_nonneg hfloor (eigenvalues₀_le_topEigenvalue hn hB)
    hentry hsmall hpolar ψ hψ

end Acharyya2025.MatrixPerturbation
