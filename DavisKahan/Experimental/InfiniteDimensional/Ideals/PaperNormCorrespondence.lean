/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormDefinite
import ForMathlib.Analysis.InnerProductSpace.KyFan

/-!
# Exact correspondence with the norm class of Davis--Kahan 1970

The paper quantifies over one normalized symmetric norming function applied to
finite singular-value lists.  The implementation uses an equivalent coherent
family of finite-dimensional unitarily invariant norms.  This file records both
objects and the two conversions explicitly.

Weak-majorization monotonicity is carried in the symmetric-gauge record as a
derived law.  It is not an additional choice and it is exactly the finite Fan
dominance theorem proved by the T-transform argument.  Bundling the law keeps
the reverse construction independent of matrix coordinates.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

/-- A dimension-coherent normalized symmetric norming function, in the exact
finite-list sense used in the paper. -/
structure PaperSymmetricNormingFunction where
  gauge : ∀ n : ℕ, (Fin n → ℝ) → ℝ
  nonneg : ∀ {n} (x : Fin n → ℝ), 0 ≤ gauge n x
  definite : ∀ {n} (x : Fin n → ℝ), gauge n x = 0 ↔ x = 0
  add_le : ∀ {n} (x y : Fin n → ℝ),
    gauge n (x + y) ≤ gauge n x + gauge n y
  smul : ∀ {n} (c : ℝ) (x : Fin n → ℝ),
    gauge n (c • x) = |c| * gauge n x
  perm : ∀ {n} (x : Fin n → ℝ) (π : Equiv.Perm (Fin n)),
    gauge n (x ∘ π) = gauge n x
  abs : ∀ {n} (x : Fin n → ℝ),
    gauge n (fun i => |x i|) = gauge n x
  zero_pad : ∀ {n} (x : Fin n → ℝ),
    gauge (n + 1) (paperZeroPad x) = gauge n x
  normalized : gauge 1 (fun _ => 1) = 1
  weak_majorization : ∀ {n} {x y : Fin n → ℝ},
    Antitone x → (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ y i) →
    (∀ m : ℕ,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), x i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), y i)) →
    gauge n x ≤ gauge n y

namespace PaperSymmetricNormingFunction

/-- The symmetric norming function extracted from the coherent operator norms. -/
noncomputable def ofPaperNorm (N : PaperUnitaryInvariantNorm) :
    PaperSymmetricNormingFunction where
  gauge := N.finiteGauge
  nonneg := N.finiteGauge_nonneg
  definite := by
    intro n x
    constructor
    · intro hx
      have hdiag : ForMathlib.diagOp
          (EuclideanSpace.basisFun (Fin n) ℂ) x = 0 := by
        apply (N.finiteNorm n).gauge_eq_zero_iff
        simpa [PaperUnitaryInvariantNorm.finiteGauge] using hx
      funext i
      have := ContinuousLinearMap.congr_fun hdiag
        (EuclideanSpace.basisFun (Fin n) ℂ i)
      simpa [ForMathlib.diagOp_apply_basis] using this
    · rintro rfl
      simp [PaperUnitaryInvariantNorm.finiteGauge]
  add_le := N.finiteGauge_add_le
  smul := N.finiteGauge_smul
  perm := by
    intro n x π
    exact (N.finiteNorm n).gauge_perm
      (EuclideanSpace.basisFun (Fin n) ℂ) x π
  abs := by
    intro n x
    exact (N.finiteNorm n).gauge_abs
      (EuclideanSpace.basisFun (Fin n) ℂ) x
  zero_pad := N.finiteGauge_zeroPad
  normalized := N.finiteGauge_one
  weak_majorization := by
    intro n x y hx h0x h0y hpre
    exact (N.finiteNorm n).gauge_le_gauge_of_prefix_sums_le
      (EuclideanSpace.basisFun (Fin n) ℂ) hx h0x h0y hpre

/-- Operator value determined by a symmetric norming function. -/
def finiteOperatorValue (Φ : PaperSymmetricNormingFunction) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Φ.gauge n (fun i => A.singularValues (i : ℕ))

/-- A source symmetric gauge induces the finite-dimensional unitarily
invariant norm used by the implementation. -/
noncomputable def finiteNorm (Φ : PaperSymmetricNormingFunction) (n : ℕ) :
    ForMathlib.UnitarilyInvariantNorm ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun := Φ.finiteOperatorValue n
  add_le' A B := by
    let x : Fin n → ℝ := fun i => (A + B).singularValues (i : ℕ)
    let y : Fin n → ℝ := fun i =>
      A.singularValues (i : ℕ) + B.singularValues (i : ℕ)
    calc
      Φ.gauge n x ≤ Φ.gauge n y := by
        apply Φ.weak_majorization
        · intro i j hij
          exact (A + B).singularValues_antitone (Fin.le_def.mp hij)
        · intro i
          exact (A + B).singularValues_nonneg _
        · intro i
          exact add_nonneg (A.singularValues_nonneg _)
            (B.singularValues_nonneg _)
        · intro m
          simpa [x, y, Finset.sum_add_distrib,
            ForMathlib.kyFanSum] using ForMathlib.kyFanSum_add_le m A B
      _ ≤ Φ.gauge n (fun i => A.singularValues (i : ℕ)) +
          Φ.gauge n (fun i => B.singularValues (i : ℕ)) := Φ.add_le _ _
  smul' c A := by
    rw [finiteOperatorValue, finiteOperatorValue]
    have hsing : (fun i : Fin n => (c • A).singularValues (i : ℕ)) =
        ‖c‖ • (fun i : Fin n => A.singularValues (i : ℕ)) := by
      funext i
      rw [LinearMap.singularValues_smul]
      simp [smul_eq_mul]
    rw [hsing, Φ.smul, abs_of_nonneg (norm_nonneg c)]
  invariant' U V A := by
    rw [finiteOperatorValue, finiteOperatorValue]
    congr 1
    funext i
    rw [ForMathlib.singularValues_unitary_comp,
      ForMathlib.singularValues_comp_unitary]

/-- Reconstruct the coherent operator-norm family from a source symmetric
norming function. -/
noncomputable def toPaperNorm (Φ : PaperSymmetricNormingFunction) :
    PaperUnitaryInvariantNorm where
  finiteNorm := Φ.finiteNorm
  normalized := by
    simpa [PaperUnitaryInvariantNorm.finiteGauge, finiteNorm,
      finiteOperatorValue, ForMathlib.singularValues_diagOp] using Φ.normalized
  zero_pad := by
    intro n x
    simpa [PaperUnitaryInvariantNorm.finiteGauge, finiteNorm,
      finiteOperatorValue, ForMathlib.singularValues_diagOp,
      paperZeroPad] using Φ.zero_pad x

/-- Extracting the source gauge after reconstruction returns it exactly. -/
theorem ofPaperNorm_toPaperNorm (Φ : PaperSymmetricNormingFunction) :
    ofPaperNorm Φ.toPaperNorm = Φ := by
  cases Φ
  rfl

/-- The finite operator values of the reconstructed family agree with the
original coherent family. -/
theorem toPaperNorm_ofPaperNorm_finite_apply
    (N : PaperUnitaryInvariantNorm) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ((ofPaperNorm N).toPaperNorm.finiteNorm n) A = (N.finiteNorm n) A := by
  rw [finiteNorm, finiteOperatorValue]
  exact (N.finiteNorm n).apply_eq_gauge rfl
    (EuclideanSpace.basisFun (Fin n) ℂ) A |>.symm

/-- The coherent finite operator family is completely determined by its source
symmetric norming function. -/
theorem paperNorm_ext
    {N M : PaperUnitaryInvariantNorm}
    (h : ∀ n x, N.finiteGauge n x = M.finiteGauge n x) : N = M := by
  cases N with
  | mk Nf Nnorm Nz =>
    cases M with
    | mk Mf Mnorm Mz =>
      congr
      funext n
      apply ForMathlib.UnitarilyInvariantNorm.ext
      intro A
      rw [(Nf n).apply_eq_gauge rfl
          (EuclideanSpace.basisFun (Fin n) ℂ) A,
        (Mf n).apply_eq_gauge rfl
          (EuclideanSpace.basisFun (Fin n) ℂ) A]
      exact h n _

/-- The current paper norm object and normalized symmetric norming functions
are equivalent, so the universal theorem excludes no norm in the source class. -/
noncomputable def paperNormEquiv :
    PaperUnitaryInvariantNorm ≃ PaperSymmetricNormingFunction where
  toFun := ofPaperNorm
  invFun := toPaperNorm
  left_inv N := by
    apply paperNorm_ext
    intro n x
    rfl
  right_inv := ofPaperNorm_toPaperNorm

end PaperSymmetricNormingFunction

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
