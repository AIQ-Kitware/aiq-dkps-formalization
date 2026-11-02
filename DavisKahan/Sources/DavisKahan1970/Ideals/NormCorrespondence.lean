/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

public import DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormDefinite
public import ForTauCeti.Analysis.InnerProductSpace.KyFan

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

The bridge in both directions rests on one computation: the singular values of
a real diagonal operator are the decreasing rearrangement of the absolute
values of its diagonal.  That is established here as
`exists_perm_singularValues_diagOp`, from the native singular-value theorem for diagonal
operators together with the basis-permutation unitary.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

/-! ### Singular values of a real diagonal operator -/

section DiagonalSingularValues

variable {n : ℕ}

/-- A diagonal operator and the diagonal operator of its absolute values have
the same Gram operator, hence exactly the same singular values. -/
theorem singularValues_diagOp_abs
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : Fin n → ℝ) :
    ((Matrix.toLin (b).toBasis (b).toBasis (Matrix.diagonal fun i => ((x) i : _)))).singularValues =
      ((Matrix.toLin (b).toBasis (b).toBasis (Matrix.diagonal fun i => (((fun i => |x i|)) i :
          _)))).singularValues := by
  apply TauCeti.singularValues_eq_of_gram_eq
  rw [← Matrix.toLin_conjTranspose, ← Matrix.toLin_conjTranspose,
    ← Matrix.toLin_mul, ← Matrix.toLin_mul]
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    abs_mul_abs_self]

/-- Every real vector can be permuted so that its absolute values decrease. -/
theorem exists_perm_abs_antitone (x : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), Antitone fun i => |x (π i)| := by
  refine ⟨Tuple.sort fun i => -|x i|, fun i j hij => ?_⟩
  have h := Tuple.monotone_sort (fun i => -|x i|) hij
  simpa using h

/-- **The singular values of a real diagonal operator are a rearrangement of
the absolute values of its diagonal.**  This is the whole content of the
correspondence between symmetric gauges and unitarily invariant norms. -/
theorem exists_perm_singularValues_diagOp
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n,
      ((Matrix.toLin (b).toBasis (b).toBasis (Matrix.diagonal fun i => ((x) i :
          _)))).singularValues (i : ℕ) = |x (π i)| := by
  obtain ⟨π, hπ⟩ := exists_perm_abs_antitone x
  refine ⟨π, fun i => ?_⟩
  have ha : Antitone fun i => ‖(x (π i) : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hπ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    Matrix.singularValues_toLin_diagonal b (fun i => (x i : ℂ)) π ha i

end DiagonalSingularValues

/-! ### Gauge laws valid for every finite unitarily invariant norm -/

/-- The source diagonal evaluation ignores signs. -/
theorem uinGauge_abs {n : ℕ}
    (N : UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
      (EuclideanSpace ℂ (Fin n)))
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (x : Fin n → ℝ) :
    N (Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal fun i => ((|x i| : ℝ) : ℂ))) =
      N (Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal fun i => (x i : ℂ))) :=
  N.map_eq_of_singularValues_eq (singularValues_diagOp_abs b x).symm

namespace SymmetricNormingFunction

/-- **Normalization forces definiteness**: every coordinate of a vector is
dominated by its source gauge.  Only `normalized` and `zero_pad` are used, via
the gauge value one of a coordinate indicator. -/
theorem abs_le_finiteGauge (N : SymmetricNormingFunction) {n : ℕ}
    (x : Fin n → ℝ) (j : Fin n) : |x j| ≤ N.finiteGauge n x := by
  match n, x, j with
  | 0, _, j => exact j.elim0
  | (m + 1), x, j =>
    have hone : N.finiteGauge (m + 1)
        (Function.update (0 : Fin (m + 1) → ℝ) j 1) = 1 := by
      have hsw : Function.update (0 : Fin (m + 1) → ℝ) j 1
          = firstCoordinateVector m ∘ (Equiv.swap 0 j) := by
        funext i
        rcases eq_or_ne i j with rfl | hij
        · simp [firstCoordinateVector, Equiv.swap_apply_right]
        · rw [Function.update_of_ne hij]
          simp only [Function.comp_apply, Pi.zero_apply, firstCoordinateVector]
          rcases eq_or_ne i 0 with rfl | hi0
          · rw [Equiv.swap_apply_left]
            have hj : (j : ℕ) ≠ 0 := fun h => hij (Fin.ext h).symm
            simp [hj]
          · rw [Equiv.swap_apply_of_ne_of_ne hi0 hij]
            have hi : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
            simp [hi]
      rw [hsw, (N.isSymmetricGauge_finiteGauge (m + 1)).map_comp_perm]
      exact N.finiteGauge_firstCoordinateVector m
    have hupd : Function.update (0 : Fin (m + 1) → ℝ) j |x j|
        = |x j| • Function.update (0 : Fin (m + 1) → ℝ) j 1 := by
      funext i
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Function.update_of_ne hij]
    have hval : N.finiteGauge (m + 1)
        (Function.update (0 : Fin (m + 1) → ℝ) j |x j|) = |x j| := by
      rw [hupd, N.finiteGauge_smul, hone, mul_one, abs_abs]
    have hmono : N.finiteGauge (m + 1)
        (Function.update (0 : Fin (m + 1) → ℝ) j |x j|)
          ≤ N.finiteGauge (m + 1) (fun i => |x i|) := by
      apply (N.isSymmetricGauge_finiteGauge (m + 1)).apply_le_of_abs_le
      intro i
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Function.update_of_ne hij, abs_nonneg]
    rw [hval] at hmono
    exact hmono.trans_eq ((N.isSymmetricGauge_finiteGauge (m + 1)).map_abs x)

/-- The source gauge vanishes only on the zero vector. -/
theorem finiteGauge_eq_zero_iff (N : SymmetricNormingFunction) {n : ℕ}
    (x : Fin n → ℝ) : N.finiteGauge n x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have h := N.abs_le_finiteGauge x i
    rw [hx] at h
    have hxi : x i = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simpa using hxi
  · rintro rfl
    exact map_zero (N.finiteGauge n)

end SymmetricNormingFunction

/-- A dimension-coherent normalized symmetric norming function, in the exact
finite-list sense used in the paper. -/
structure SymmetricNormingFunction.Axiomatic where
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
    gauge (n + 1) (zeroPad x) = gauge n x
  normalized : gauge 1 (fun _ => 1) = 1
  weak_majorization : ∀ {n} {x y : Fin n → ℝ},
    Antitone x → (∀ i, 0 ≤ x i) → (∀ i, 0 ≤ y i) →
    (∀ m : ℕ,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), x i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), y i)) →
    gauge n x ≤ gauge n y

namespace SymmetricNormingFunction.Axiomatic

/-- Two source symmetric norming functions with the same gauge agree. -/
theorem ext {Φ Ψ : SymmetricNormingFunction.Axiomatic}
    (h : ∀ n x, Φ.gauge n x = Ψ.gauge n x) : Φ = Ψ := by
  cases Φ
  cases Ψ
  congr 1
  funext n x
  exact h n x

/-- The symmetric norming function extracted from the coherent operator norms. -/
noncomputable def ofNormingFunction (N : SymmetricNormingFunction) :
    SymmetricNormingFunction.Axiomatic where
  gauge := fun n => N.finiteGauge n
  nonneg := N.finiteGauge_nonneg
  definite := N.finiteGauge_eq_zero_iff
  add_le := N.finiteGauge_add_le
  smul := N.finiteGauge_smul
  perm := by
    intro n x π
    exact (N.isSymmetricGauge_finiteGauge n).map_comp_perm π x
  abs := by
    intro n x
    exact (N.isSymmetricGauge_finiteGauge n).map_abs x
  zero_pad := N.finiteGauge_zeroPad
  normalized := N.finiteGauge_one
  weak_majorization := by
    intro n x y hx h0x _h0y hpre
    exact (N.isSymmetricGauge_finiteGauge n).apply_le_of_prefixSum_le hx h0x
      (by simpa only [TauCeti.prefixSum_def] using hpre)

/-- Operator value determined by a symmetric norming function. -/
def finiteOperatorValue (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Φ.gauge n (fun i => A.singularValues (i : ℕ))

/-- A source symmetric gauge induces the finite-dimensional unitarily
invariant norm used by the implementation. -/
noncomputable def finiteNorm (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ) :
    TauCeti.UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) := by
  let p : Seminorm ℝ (Fin n → ℝ) := Seminorm.of (Φ.gauge n) (Φ.add_le)
    (fun c x => by simpa only [Real.norm_eq_abs] using Φ.smul c x)
  have hp : p.IsSymmetricGauge := by
    refine ⟨fun π x => Φ.perm x π, ?_⟩
    intro x j
    calc
      p (Function.update x j (-x j)) = Φ.gauge n |Function.update x j (-x j)| :=
        (Φ.abs _).symm
      _ = Φ.gauge n |x| := by
        congr 1
        ext i
        by_cases hij : i = j <;> simp [hij]
      _ = p x := Φ.abs x
  exact UnitarilyInvariantSeminorm.ofIsSymmetricGauge p hp

/-- Native reconstruction has the original singular-value formula. -/
theorem finiteNorm_apply (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (Φ.finiteNorm n) A = Φ.finiteOperatorValue n A := by
  unfold finiteNorm
  rw [UnitarilyInvariantSeminorm.ofIsSymmetricGauge_apply]
  rfl

/-- **The induced finite norm has exactly the source gauge.**  Both the
normalization and the zero-padding law of the reconstructed family reduce to
the corresponding source law through this identity. -/
theorem finiteNorm_gauge (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (x : Fin n → ℝ) :
    ((Φ.finiteNorm n)) (Matrix.toLin ((EuclideanSpace.basisFun (Fin n) ℂ)).toBasis ((EuclideanSpace.basisFun (Fin n) ℂ)).toBasis (Matrix.diagonal fun i => ((x) i : _))) =
      Φ.gauge n x := by
  rw [finiteNorm_apply]
  obtain ⟨π, hπ⟩ :=
    exists_perm_singularValues_diagOp (EuclideanSpace.basisFun (Fin n) ℂ) x
  show Φ.gauge n (fun i : Fin n =>
      ((let b' := (EuclideanSpace.basisFun (Fin n) ℂ); Matrix.toLin b'.toBasis b'.toBasis
          (Matrix.diagonal fun i => ((x) i : _)))).singularValues
        (i : ℕ)) = Φ.gauge n x
  have hfun : (fun i : Fin n =>
      ((let b' := (EuclideanSpace.basisFun (Fin n) ℂ); Matrix.toLin b'.toBasis b'.toBasis
          (Matrix.diagonal fun i => ((x) i : _)))).singularValues
        (i : ℕ)) = (fun i => |x i|) ∘ π := by
    funext i
    exact hπ i
  rw [hfun, Φ.perm, Φ.abs]

/-- Reconstruct the coherent operator-norm family from a source symmetric
norming function. -/
noncomputable def toNormingFunction (Φ : SymmetricNormingFunction.Axiomatic) :
    SymmetricNormingFunction where
  finiteNorm := Φ.finiteNorm
  normalized := by
    exact (Φ.finiteNorm_gauge 1 (fun _ => 1)).trans Φ.normalized
  zero_pad := by
    intro n x
    rw [Φ.finiteNorm_gauge, Φ.finiteNorm_gauge]
    exact Φ.zero_pad x

/-- The transported paper norm has finite gauge, so it lands in the ideal. -/
@[simp]
theorem toNormingFunction_finiteGauge (Φ : SymmetricNormingFunction.Axiomatic) (n : ℕ)
    (x : Fin n → ℝ) :
    Φ.toNormingFunction.finiteGauge n x = Φ.gauge n x := by
  rw [SymmetricNormingFunction.finiteGauge_def]
  exact Φ.finiteNorm_gauge n x

/-- Extracting the source gauge after reconstruction returns it exactly. -/
theorem ofNormingFunction_toNormingFunction (Φ : SymmetricNormingFunction.Axiomatic) :
    ofNormingFunction Φ.toNormingFunction = Φ :=
  ext fun n x => Φ.toNormingFunction_finiteGauge n x

/-- The finite operator values of the reconstructed family agree with the
original coherent family. -/
theorem toNormingFunction_ofNormingFunction_finite_apply
    (N : SymmetricNormingFunction) (n : ℕ)
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ((ofNormingFunction N).toNormingFunction.finiteNorm n) A = (N.finiteNorm n) A := by
  change ((ofNormingFunction N).finiteNorm n) A = _
  rw [finiteNorm_apply]
  exact ((N.finiteNorm n).map_eq_gauge_singularValues A).symm

/-- The coherent finite operator family is completely determined by its source
symmetric norming function. -/
theorem ext_finiteGauge
    {N M : SymmetricNormingFunction}
    (h : ∀ n x, N.finiteGauge n x = M.finiteGauge n x) : N = M := by
  cases N with
  | mk Nf Nnorm Nz =>
    cases M with
    | mk Mf Mnorm Mz =>
      congr 1
      funext n
      apply TauCeti.UnitarilyInvariantSeminorm.ext
      intro A
      rw [(Nf n).map_eq_gauge_singularValues A, (Mf n).map_eq_gauge_singularValues A]
      exact h n (fun i => A.singularValues i)

/-- The current paper norm object and normalized symmetric norming functions
are equivalent, so the universal theorem excludes no norm in the source class. -/
noncomputable def equiv :
    SymmetricNormingFunction ≃ SymmetricNormingFunction.Axiomatic where
  toFun := ofNormingFunction
  invFun := toNormingFunction
  left_inv N := by
    apply ext_finiteGauge
    intro n x
    exact (ofNormingFunction N).toNormingFunction_finiteGauge n x
  right_inv := ofNormingFunction_toNormingFunction

end SymmetricNormingFunction.Axiomatic

end

end ExactSinTheta
end DavisKahan
end TauCeti
