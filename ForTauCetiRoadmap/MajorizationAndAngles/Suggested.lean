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

## ✅ DELIVERED — every signature below is proved (verified 2026-07-31)

**This topic is complete.**  All 26 declarations in this file exist and are
proved across 12 modules of `ForTauCeti/**`; `README.md` records where each
one landed.  Read this file as a *record* of the target shapes, not as a list
of open work.

**The `sorry` bodies here are deliberate and must not be "fixed".**  As
`ForTauCetiRoadmap.lean` puts it, this library exists so that a broken
suggested signature is a build failure — a guard that has already caught ten
real elaboration errors.  Replacing a body with a proof duplicates the
library; deleting a signature removes the guard.  The only thing that should
change here is a *statement*, and only to track a deliberate rename.

If you re-verify delivery, build a declaration index rather than grepping per
name: a per-name search reported 17 of these 26 as missing, `cosThetaMap` and
`kyFanSum` among them, because Lean declaration syntax varies too much for a
single pattern.
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
-- DELIVERED: `ForTauCeti.Analysis.Convex.Majorization`
def prefixSum (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), x i

/-- A set of real tuples that is convex, transposition-closed, and closed under
the elementary Robin Hood transfer.  Gauge sublevel sets are the motivating
instances. -/
-- DELIVERED: `ForTauCeti.Analysis.Convex.Majorization`
structure IsSymmetricConvex (K : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ K
  transposition_mem : ∀ (σ : Equiv.Perm (Fin n)), ∀ x ∈ K, x ∘ σ ∈ K
  transfer_mem : ∀ x ∈ K, ∀ i j : Fin n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (fun k => if k = i then (1 - t) * x i + t * x j
              else if k = j then t * x i + (1 - t) * x j else x k) ∈ K

/-- **The transfer descent**: a symmetric-convex set containing `y` contains every
antitone nonnegative tuple whose prefix sums `y` dominates.  The engine under
every unitarily invariant norm inequality of this roadmap. -/
-- DELIVERED: `ForTauCeti.Analysis.Convex.Majorization`
theorem IsSymmetricConvex.mem_of_prefixSum_le {K : Set (Fin n → ℝ)}
    (hK : IsSymmetricConvex K) {y z : Fin n → ℝ} (hy : y ∈ K)
    (hz : Antitone z) (hz0 : ∀ i, 0 ≤ z i)
    (h : ∀ k, prefixSum k z ≤ prefixSum k y) : z ∈ K := sorry

/-- The Schur--Horn weight: squared moduli of the eigenbasis coefficients of an
orthonormal basis, a doubly stochastic matrix. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SchurHorn`
noncomputable def schurWeight {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) (i k : Fin n) : ℝ :=
  ‖⟪hT.eigenvectorBasis hn i, e k⟫_𝕜‖ ^ 2

/-- **Forward Schur--Horn, Karamata form**: convex functions of the diagonal are
dominated by convex functions of the spectrum. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SchurHorn`
theorem convexOn_sum_re_inner_orthonormalBasis_self_le {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E)
    {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ) (hmem : ∀ i, hT.eigenvalues hn i ∈ s)
    (hdiag : ∀ k, RCLike.re ⟪T (e k), e k⟫_𝕜 ∈ s) :
    ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜) ≤ ∑ i, φ (hT.eigenvalues hn i) := sorry

/-- The Ky Fan `k`-sum of singular values. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.KyFan`
noncomputable def kyFanSum (k : ℕ) (A : E →ₗ[𝕜] E) : ℝ :=
  ∑ i ∈ Finset.range k, A.singularValues i

/-- The Ky Fan triangle inequality: `σ(A+B)` is weakly majorized by `σ(A)+σ(B)`,
so every Ky Fan norm satisfies the triangle inequality at once. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.KyFan`
theorem kyFanSum_add_le (k : ℕ) (A B : E →ₗ[𝕜] E) :
    kyFanSum k (A + B) ≤ kyFanSum k A + kyFanSum k B := sorry

/-- A unitarily invariant norm on square operators: the three laws, with
positivity and the rest derived. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm`
structure UnitarilyInvariantNorm (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] where
  toFun : (E →ₗ[𝕜] E) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) (A), toFun (a • A) = ‖a‖ * toFun A
  unitary_invariant' : ∀ (U V : unitary (E →ₗ[𝕜] E)) (A),
    toFun ((U : E →ₗ[𝕜] E) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = toFun A

/-- **Fan dominance**: Ky Fan domination implies domination in every unitarily
invariant norm. -/
-- DELIVERED: AMBIGUOUS -- `apply_le_of_kyFanSum_le` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Majorization`, `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm`); disambiguate before trusting this
theorem UnitarilyInvariantNorm.apply_le_of_kyFanSum_le
    (N : UnitarilyInvariantNorm 𝕜 E) {A B : E →ₗ[𝕜] E}
    (h : ∀ k, kyFanSum k A ≤ kyFanSum k B) : N.toFun A ≤ N.toFun B := sorry

/-- A unitarily invariant norm is determined by the singular-value sequence. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm`
theorem UnitarilyInvariantNorm.eq_of_same_singularValues
    (N : UnitarilyInvariantNorm 𝕜 E) {A B : E →ₗ[𝕜] E}
    (h : A.singularValues = B.singularValues) : N.toFun A = N.toFun B := sorry

/-! ## Part B -- principal angles, aligned bases, and finite frames (T06)

Angles are singular values of the overlap operator, so nonnegativity, the `≤ 1`
bound, ordering and symmetry are inherited rather than re-proved by induction. -/

/-- The coordinate isometry of an orthonormal family, `eⱼ ↦ vⱼ`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.AlignedBasis`
noncomputable def familyIsometry {v : Fin d → E} (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E := sorry

/-- The overlap operator of two orthonormal families: the composite of one
coordinate isometry's adjoint with the other, with matrix `⟪uᵢ, vⱼ⟫`. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.AlignedBasis`
noncomputable def overlapOp {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  (familyIsometry hu).toLinearMap.adjoint ∘ₗ (familyIsometry hv).toLinearMap

/-- Principal-angle cosines: the singular values of the overlap operator. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles`
noncomputable def cosPrincipalAngles {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  sorry

/-- The squared Frobenius sine of the angle configuration. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles`
noncomputable def sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℝ :=
  ∑ k : Fin d, (1 - cosPrincipalAngles hu hv (k : ℕ) ^ 2)

/-- **`‖sin Θ‖²_F = d − overlap`**: the squared Frobenius sine equals the
dimension minus the squared Frobenius norm of the overlap operator. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles`
theorem sinThetaSq_eq_card_sub_sum_sq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = d - ∑ k : Fin d, cosPrincipalAngles hu hv (k : ℕ) ^ 2 := sorry

/-! ## Part C -- rectangular unitarily invariant norms (T07) -/

/-- A unitarily invariant norm on rectangular operators `E →ₗ[𝕜] F`: the same
three laws, with two-sided unitary invariance. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Basic`
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
-- DELIVERED: AMBIGUOUS -- `apply_le_of_kyFanSum_le` is declared in 2 modules (`ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Majorization`, `ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantNorm`); disambiguate before trusting this
theorem RectangularUnitarilyInvariantNorm.apply_le_of_kyFanSum_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F) {A B : E →ₗ[𝕜] F}
    (h : ∀ k, ∑ i ∈ Finset.range k, A.singularValues i
            ≤ ∑ i ∈ Finset.range k, B.singularValues i) :
    N.toFun A ≤ N.toFun B := sorry

/-! ### The orthogonal block sum

A single `blockSum_target` placeholder stood here and identified no theorem: the block-sum
layer is **four** results, and they are milestones in sequence rather than alternate names
for one statement.  The last is the consumer-facing one. -/

/-- The orthogonal block sum of two rectangular maps, on `WithLp 2` products. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum`
noncomputable def orthogonalBlockSum {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂) :
    WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (F₁ × F₂) :=
  LinearMap.withLpMap 2 (A.prodMap B)

/-- Doubling repeats every singular value twice; the quotient `i / 2` is the interleaved
sorted order of the two copies. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum`
theorem singularValues_orthogonalBlockSum_self (A : E →ₗ[𝕜] F) (i : ℕ) :
    (orthogonalBlockSum A A).singularValues i = A.singularValues (i / 2) := sorry

/-- **The principal endpoint.**  Two simultaneous rectangular Ky Fan majorizations combine
sharply on the orthogonal block sum.  Not shortened to `blockSum_le`: the hypotheses are
specifically Ky Fan majorization, and the longer name is what makes that interface
discoverable. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum`
theorem orthogonalBlockSum_apply_le_of_kyFanSum_le
    {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (NB : RectangularUnitarilyInvariantNorm 𝕜
      (WithLp 2 (E₁ × E₂)) (WithLp 2 (F₁ × F₂)))
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : ∀ k, ∑ i ∈ Finset.range k, A.singularValues i
            ≤ ∑ i ∈ Finset.range k, C.singularValues i)
    (hB : ∀ k, ∑ i ∈ Finset.range k, B.singularValues i
            ≤ ∑ i ∈ Finset.range k, D.singularValues i) :
    NB.toFun (orthogonalBlockSum A B) ≤ NB.toFun (orthogonalBlockSum C D) := sorry

/-! ## Part D -- angle geometry and eigenvalue perturbation (T08) -/

/-- The cross projection `P_V P_U`, whose singular values are the principal cosines. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry`
noncomputable def cosThetaMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  ((V.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ
    ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)

/-- Principal-angle cosines of a pair of subspaces: the singular values of the cross
projection, sorted decreasingly and padded by zeros beyond the finite rank. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry`
noncomputable def principalCosines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ →₀ ℝ :=
  (cosThetaMap U V).singularValues

/-- The subspace-level principal cosines agree with the family-level ones on
spans: the theorem that makes the Part B definition well-named. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.AngleGeometry`
theorem principalCosines_span_eq_cosPrincipalAngles {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    principalCosines (Submodule.span 𝕜 (Set.range u)) (Submodule.span 𝕜 (Set.range v))
      = cosPrincipalAngles hu hv := sorry

/-- **The von Neumann trace core**: for symmetric `T`, `S`, the trace of `T ∘ S`
is dominated by the sorted-eigenvalue pairing.  Proved from the rearrangement
inequality, not cited. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HoffmanWielandt`
theorem sum_eigenvalues_mul_re_inner_self_le {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) :
    ∑ k, hT.eigenvalues hn k *
        RCLike.re ⟪hT.eigenvectorBasis hn k, S (hT.eigenvectorBasis hn k)⟫_𝕜
      ≤ ∑ i, hT.eigenvalues hn i * hS.eigenvalues hn i := sorry

/-- **Hoffman--Wielandt**: the squared Euclidean distance between the sorted
spectra of two symmetric operators is at most the squared Frobenius distance.

**Quantified over an arbitrary orthonormal basis `e`, and that is the point.**  The
staged proof states the right-hand side against `hT.eigenvectorBasis`, which is enough
to prove it but is not the invariant Frobenius statement a consumer wants.  This clean
name belongs to the arbitrary-basis version; the eigenbasis-specialized theorem should
be private, or qualified `..._eigenvectorBasis` if it stays public. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HoffmanWielandt`
theorem sum_sq_eigenvalues_sub_le_sum_sq_norm_apply {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ k, ‖T (e k) - S (e k)‖ ^ 2 := sorry

/-- **Davis's eigenvalue-change bound**, through Birkhoff's theorem and the
permutation-orbit convex hull: under a spectral separation `γ` for `S`, a Frobenius
perturbation smaller than `γ/√2` cannot move the sorted spectrum by more than it.

The `γ` separation hypothesis and the `γ/√2` smallness threshold are both part of the
statement; a name without them would read as an unconditional bound, which is false. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.EigenvalueChange`
theorem sum_sq_eigenvalues_sub_ge {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hsep : ∀ i j, i ≠ j → γ ≤ |hS.eigenvalues hn i - hS.eigenvalues hn j|)
    (hCH : ∑ i, (RCLike.re ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜) ^ 2
            ≤ (γ / Real.sqrt 2) ^ 2) :
    ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := sorry

end TauCetiRoadmap.MajorizationAndAngles
