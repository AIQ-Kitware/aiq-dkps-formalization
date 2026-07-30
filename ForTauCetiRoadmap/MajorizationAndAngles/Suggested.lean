/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Majorization, unitarily invariant norms, and principal angles: suggested signatures

The roadmap prose is authoritative.  This file records representative target
shapes using names already present in the staged `ForTauCeti` implementation;
it is not exhaustive, and discharging everything here finishes neither a Part
nor the roadmap.
-/

namespace TauCetiRoadmap.MajorizationAndAngles

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {n d : ℕ}

/-! ## Part A -- majorization, Schur-Horn, and unitarily invariant norms (T05)

The vector layer lives in `Analysis/Convex` with no operator imports; the
operator layer pulls it back through singular values. -/

/-- Prefix sum of the first `k` coordinates, the vocabulary of weak majorization. -/
def prefixSum (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x i

/-- A set of real tuples that is convex, transposition-closed, and closed under
the elementary Robin Hood transfer.  Gauge sublevel sets are the motivating
instances. -/
structure IsSymmetricConvex (K : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ K
  transposition_mem : ∀ (σ : Equiv.Perm (Fin n)), ∀ x ∈ K, x ∘ σ ∈ K
  transfer_mem : ∀ x ∈ K, ∀ i j : Fin n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (fun k => if k = i then (1 - t) * x i + t * x j
              else if k = j then t * x i + (1 - t) * x j else x k) ∈ K

/-- **The transfer descent**: a symmetric-convex set containing `y` contains every
antitone nonnegative tuple whose prefix sums `y` dominates.  The engine under
every unitarily invariant norm inequality of this roadmap. -/
theorem IsSymmetricConvex.mem_of_prefixSum_le {K : Set (Fin n → ℝ)}
    (hK : IsSymmetricConvex K) {y z : Fin n → ℝ} (hy : y ∈ K)
    (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (h : ∀ k, prefixSum k z ≤ prefixSum k y) : z ∈ K := sorry

/-- The Schur--Horn weight: squared moduli of the eigenbasis coefficients of an
orthonormal basis, a doubly stochastic matrix. -/
noncomputable def schurWeight {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) (i k : Fin n) : ℝ :=
  ‖⟪hT.eigenvectorBasis hn i, e k⟫_𝕜‖ ^ 2

/-- **Forward Schur--Horn, Karamata form**: convex functions of the diagonal are
dominated by convex functions of the spectrum. -/
theorem convexOn_sum_re_inner_orthonormalBasis_self_le {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E)
    {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ) (hmem : ∀ i, hT.eigenvalues hn i ∈ s)
    (hdiag : ∀ k, RCLike.re ⟪T (e k), e k⟫_𝕜 ∈ s) :
    ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜) ≤ ∑ i, φ (hT.eigenvalues hn i) := sorry

/-- The Ky Fan `k`-sum of singular values. -/
noncomputable def kyFanSum (k : ℕ) (A : E →ₗ[𝕜] E) : ℝ :=
  ∑ i ∈ Finset.range k, A.singularValues i

/-- The Ky Fan triangle inequality: `σ(A+B)` is weakly majorized by `σ(A)+σ(B)`,
so every Ky Fan norm satisfies the triangle inequality at once. -/
theorem kyFanSum_add_le (k : ℕ) (A B : E →ₗ[𝕜] E) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := sorry

/-- A unitarily invariant norm on square operators: the three laws, with
positivity and the rest derived. -/
structure UnitarilyInvariantNorm (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] where
  toFun : (E →ₗ[𝕜] E) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) (A), toFun (a • A) = ‖a‖ * toFun A
  unitary_invariant' : ∀ (U V : unitary (E →ₗ[𝕜] E)) (A),
    toFun ((U : E →ₗ[𝕜] E) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = toFun A

/-- **Fan dominance**: Ky Fan domination implies domination in every unitarily
invariant norm. -/
theorem UnitarilyInvariantNorm.apply_le_of_kyFanSum_le
    (N : UnitarilyInvariantNorm 𝕜 E) {A B : E →ₗ[𝕜] E}
    (h : ∀ k, kyFanSum k A ≤ kyFanSum k B) : N.toFun A ≤ N.toFun B := sorry

/-- A unitarily invariant norm is determined by the singular-value sequence. -/
theorem UnitarilyInvariantNorm.eq_of_same_singularValues
    (N : UnitarilyInvariantNorm 𝕜 E) {A B : E →ₗ[𝕜] E}
    (h : A.singularValues = B.singularValues) : N.toFun A = N.toFun B := sorry

/-! ## Part B -- principal angles, aligned bases, and finite frames (T06)

Angles are singular values of the overlap operator, so nonnegativity, the `≤ 1`
bound, ordering and symmetry are inherited rather than re-proved by induction. -/

/-- The coordinate isometry of an orthonormal family, `eⱼ ↦ vⱼ`. -/
noncomputable def familyIsometry {v : Fin d → E} (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E := sorry

/-- The overlap operator of two orthonormal families: the composite of one
coordinate isometry's adjoint with the other, with matrix `⟪uᵢ, vⱼ⟫`. -/
noncomputable def overlapOp {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  (familyIsometry hu).toLinearMap.adjoint ∘ₗ (familyIsometry hv).toLinearMap

/-- Principal-angle cosines: the singular values of the overlap operator. -/
noncomputable def cosPrincipalAngles {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  sorry

/-- The squared Frobenius sine of the angle configuration. -/
noncomputable def sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℝ :=
  ∑ k : Fin d, (1 - cosPrincipalAngles hu hv (k : ℕ) ^ 2)

/-- **`‖sin Θ‖²_F = d − overlap`**: the squared Frobenius sine equals the
dimension minus the squared Frobenius norm of the overlap operator. -/
theorem sinThetaSq_eq_card_sub_sum_sq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = d - ∑ k : Fin d, cosPrincipalAngles hu hv (k : ℕ) ^ 2 := sorry

/-! ## Part C -- rectangular unitarily invariant norms (T07) -/

/-- A unitarily invariant norm on rectangular operators `E →ₗ[𝕜] F`: the same
three laws, with two-sided unitary invariance. -/
structure RectangularUnitarilyInvariantNorm (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] where
  toFun : (E →ₗ[𝕜] F) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) (A), toFun (a • A) = ‖a‖ * toFun A
  unitary_invariant' : ∀ (U : unitary (F →ₗ[𝕜] F)) (V : unitary (E →ₗ[𝕜] E)) (A),
    toFun ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = toFun A

/-- **Rectangular Fan dominance**: Ky Fan domination of the singular values gives
domination in every rectangular unitarily invariant norm — one estimate yields
the operator, Frobenius, Ky Fan and nuclear norms at once. -/
theorem RectangularUnitarilyInvariantNorm.apply_le_of_kyFanSum_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F) {A B : E →ₗ[𝕜] F}
    (h : ∀ k, ∑ i ∈ Finset.range k, A.singularValues i
            ≤ ∑ i ∈ Finset.range k, B.singularValues i) :
    N.toFun A ≤ N.toFun B := sorry

/-- The gauge of a block sum against the concatenated singular values, the shape
consumed by two-subspace perturbation arguments. -/
theorem RectangularUnitarilyInvariantNorm.blockSum_target : True := sorry

/-! ## Part D -- angle geometry and eigenvalue perturbation (T08) -/

/-- The subspace-level principal cosines agree with the family-level ones on
spans: the theorem that makes the Part B definition well-named. -/
theorem principalCosines_span_eq_cosPrincipalAngles {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) : True := sorry

/-- **The von Neumann trace core**: for symmetric `T`, `S`, the trace of `T ∘ S`
is dominated by the sorted-eigenvalue pairing.  Proved from the rearrangement
inequality, not cited. -/
theorem sum_eigenvalues_mul_re_inner_self_le {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) : True := sorry

/-- **Hoffman--Wielandt**: the squared Euclidean distance between the sorted
spectra of two symmetric operators is at most the squared Frobenius distance. -/
theorem sum_sq_eigenvalues_sub_le_sum_sq_norm_apply {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ k, ‖T (e k) - S (e k)‖ ^ 2 := sorry

/-- **Davis's eigenvalue-change bound**, through Birkhoff's theorem and the
permutation-orbit convex hull: the displacement of the sorted spectrum is
controlled by the perturbation. -/
theorem sum_sq_eigenvalues_sub_ge {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) : True := sorry

end TauCetiRoadmap.MajorizationAndAngles
