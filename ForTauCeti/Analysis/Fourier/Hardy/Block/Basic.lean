/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI gpt-6.1-sol
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Basic
public import ForTauCeti.Analysis.Matrix.EuclideanLin

/-!
# Block Hardy basis enumeration and continuous matrix symbols

These donor additions support the opposite-shift finite-section example. The underlying
block Hardy space and matrix-symbol operations are supplied by Tau Ceti.
-/

public noncomputable section

open AddCircle MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- Enumerate the block Hardy basis by increasing position, then coordinate within the block. -/
def blockHardyBasisNat (r : ℕ) [NeZero r] : HilbertBasis ℕ ℂ (BlockHardySpace r) :=
  (blockHardyBasis r).reindex (Nat.divModEquiv r).symm

/-- Block order sends position `k` and coordinate `i` to `k * r + i`. -/
@[simp] theorem blockHardyBasisNat_apply (r : ℕ) [NeZero r] (k : ℕ) (i : Fin r) :
    blockHardyBasisNat r (k * r + i) = blockHardyBasis r (k, i) := by
  rw [blockHardyBasisNat, HilbertBasis.reindex_apply, Equiv.symm_symm]
  rw [← Nat.divModEquiv_symm_apply r (k, i), Equiv.apply_symm_apply]

/-- An arbitrary scalar index is its quotient block position and remainder coordinate. -/
theorem blockHardyBasisNat_apply_div_mod (r : ℕ) [NeZero r] (m : ℕ) :
    blockHardyBasisNat r m =
      blockHardyBasis r (m / r, ⟨m % r, Nat.mod_lt m (NeZero.pos r)⟩) := by
  rw [blockHardyBasisNat, HilbertBasis.reindex_apply]
  rfl

/-- The scalar entry of a continuous matrix symbol agrees with its entrywise `L∞` class. -/
@[simp high] theorem blockSymbolEntry_toLp_matrix {r : ℕ}
    (F : C(UnitAddCircle, Matrix (Fin r) (Fin r) ℂ)) (i j : Fin r) :
    blockSymbolEntry r i j (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ
      ⟨fun t => Matrix.toEuclideanCLM (𝕜 := ℂ) (F t),
        Matrix.continuous_toEuclideanCLM.comp F.continuous⟩) =
      ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ
        (⟨fun t => F t i j, by fun_prop⟩ : C(UnitAddCircle, ℂ)) := by
  rw [blockSymbolEntry_toLp]
  congr 1
  ext t
  exact congrArg (fun v : EuclideanSpace ℂ (Fin r) => v i)
    (Matrix.toEuclideanCLM_apply_single (F t) j)

end TauCeti
