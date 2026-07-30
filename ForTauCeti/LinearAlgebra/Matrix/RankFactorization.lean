/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Rank factorization

Every matrix over a field factors as `M = L * R` with inner dimension exactly
`M.rank` (the classical *rank factorization* / full-rank factorization), hence
through `Fin r` for any `r ≥ M.rank`; and conversely any product through `Fin r`
has rank at most `r`.

Mathlib has the rank API (`Matrix.rank`, `rank_mul_le`, …) but no factorization
realizing the rank as an inner dimension; this supplies the missing converse
making `M.rank ≤ r ↔ ∃ L R, M = L * R` an equivalence.

The construction: the columns of `M` span the column space
`LinearMap.range M.mulVecLin`, whose dimension is `M.rank`; choosing a basis of
the column space, `L` lists the basis vectors and `R` the coordinates of each
column of `M` in that basis.

## Main results

* `TauCeti.Matrix.exists_eq_mul_rank`: the exact rank factorization, inner
  dimension `Fin M.rank`.
* `TauCeti.Matrix.exists_eq_mul_of_rank_le`: zero-padded to `Fin r` for any
  `M.rank ≤ r`.
* `TauCeti.Matrix.rank_le_iff_exists_eq_mul`: the characterization
  `M.rank ≤ r ↔ ∃ L R, M = L * R`.

## Staging note

Staged for Tau Ceti, roadmap topic T21.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/LinearAlgebra/Matrix/Rank.lean`
(rank factorization).
Formalized by Claude Fable 5 (claude-fable-5[1m]).

## Known linter warnings, and why they stay

Mathlib's `linter.unusedDecidableInType` flags `[DecidableEq n]` on the three theorems
below: it is in their type and never used, and the linter's advice is to drop it and call
`classical` in the proof.  That advice is right for Mathlib and wrong for us, because the
same three signatures are pinned as **data**: `Challenge/MathlibPending/RankFactorization/`
restates them in an immutable `Conformance.lean` — with the identical
`variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]` line — and
`Leaderboard.lean` names `TauCeti.Matrix.rank_le_iff_exists_eq_mul` in `#print axioms`.
Dropping the instance here would change the signature and desynchronise the two, and
`AGENTS.md` makes a `Conformance.lean` statement immutable, so it cannot move to meet us.

The disagreement is therefore real and is not this file's to settle: the conformance
statement and the eventual Mathlib statement cannot both be right, and the Mathlib one is
the one without `[DecidableEq n]`.  What this file *can* do is stop the disagreement from
costing the whole library its gate.  Each of the three carries a
`set_option linter.unusedDecidableInType false in` naming this note, so the exception is
exactly three declarations wide and visible at the point it applies — and
`lean_lib ForMathlib` can then carry `warningAsError`, which it now does.  Before that,
three known warnings kept the gate off and so let *every* new warning through as well; six
had accumulated unnoticed in the modules the target was not even building.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `7bc63b8`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/LinearAlgebra/Matrix/Rank.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (rule 2 of
  `scripts/check_dependency_layers.py`); this module imports Mathlib only.

## Provenance

*Moved, not restated.*  This file was `ForMathlib/LinearAlgebra/Matrix/RankFactorization.lean`
until 2026-07-29, when lane FM-RETIRE retired `ForMathlib` entirely: its four
surviving modules moved here and the library, its root module and its directory
were deleted.  Statements, proofs and signatures are unchanged.

**FM-RETIRE was worked twice, and the two versions disagreed on the namespace.**
The `main` version (`c85510d6`) kept `namespace ForMathlib.Matrix` here, reasoning
that `Challenge/**/Conformance.lean` is immutable so its `ForMathlib.*` pins could
not be re-issued.  Reconciled on merge in favour of `TauCeti.Matrix`; the rationale
and the list of pins updated to match is recorded once, in
`ForTauCeti/Topology/Berge.lean`.

-/

/-!
### Provenance

Moved from `ForMathlib/LinearAlgebra/Matrix/` to `ForTauCeti/LinearAlgebra/Matrix/`
on 2026-07-29 by lane FM-RETIRE, which finishes the `ForMathlib` retirement.  The
namespace changed from `ForMathlib.Matrix` to `TauCeti.Matrix` to match the
destination package; declaration names, statements and proofs are unchanged.
-/

namespace TauCeti.Matrix

open Module (finrank)
open _root_.Matrix

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

-- `[DecidableEq n]` is pinned by an immutable Challenge statement; see the module note.
set_option linter.unusedDecidableInType false in
/--
**Rank factorization (exact).** Every matrix factors as `M = L * R` with inner
dimension `Fin M.rank`: `L` lists a basis of the column space of `M` and `R` the
coordinates of each column of `M` in that basis.
-/
theorem exists_eq_mul_rank (M : Matrix m n 𝕜) :
    ∃ (L : Matrix m (Fin M.rank) 𝕜) (R : Matrix (Fin M.rank) n 𝕜), M = L * R := by
  -- A basis of the column space, indexed by `Fin M.rank`.
  have hdim : finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank := rfl
  let b : Module.Basis (Fin M.rank) 𝕜 (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq 𝕜 _ hdim
  -- Each column of `M` lies in the column space.
  have hcol : ∀ j : n, (fun i => M i j) ∈ LinearMap.range M.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨fun i k => (b k : m → 𝕜) i, fun k j => b.repr ⟨_, hcol j⟩ k, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  -- Expand column `j` in the basis and evaluate the resulting identity at row `i`.
  have hrepr := congrArg Subtype.val (b.sum_repr ⟨_, hcol j⟩)
  rw [Submodule.coe_sum] at hrepr
  have := congrFun hrepr i
  simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Finset.sum_congr rfl fun k _ => mul_comm ((b k : m → 𝕜) i) (b.repr ⟨_, hcol j⟩ k)]
  exact this.symm

-- `[DecidableEq n]` is pinned by an immutable Challenge statement; see the module note.
set_option linter.unusedDecidableInType false in
/--
**Rank factorization (padded).** A matrix `M` with `M.rank ≤ r` factors as
`M = L * R` with `L : Matrix m (Fin r) 𝕜` and `R : Matrix (Fin r) n 𝕜`
(the exact factorization, zero-padded to inner dimension `r`).
-/
theorem exists_eq_mul_of_rank_le (M : Matrix m n 𝕜) {r : ℕ} (h : M.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  obtain ⟨L₀, R₀, hM⟩ := exists_eq_mul_rank M
  refine ⟨fun i k => if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0,
    fun k j => if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0, ?_⟩
  ext i j
  -- Reduce the padded sum over `Fin r` to the exact sum over `Fin M.rank`.
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
    -- The padding terms vanish above `M.rank`.
    refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le h))
      fun k _ hk => dif_neg (by simpa using hk)).symm
  rw [Matrix.mul_apply, hsum, ← Matrix.mul_apply, ← hM]

-- `[DecidableEq n]` is pinned by an immutable Challenge statement; see the module note.
set_option linter.unusedDecidableInType false in
/--
**Rank-`r` factorization characterization.** A matrix has rank at most `r` if
and only if it factors through `Fin r`: `M.rank ≤ r ↔ ∃ L R, M = L * R`.
-/
theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  refine ⟨exists_eq_mul_of_rank_le M, ?_⟩
  rintro ⟨L, R, rfl⟩
  calc (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card (Fin r) := L.rank_le_card_width
    _ = r := Fintype.card_fin r

end TauCeti.Matrix
