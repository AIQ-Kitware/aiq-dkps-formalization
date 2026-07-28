/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum

/-!
# Concrete rectangular unitarily invariant norms

Adjoint transport, composition bounds, the zero extension, and the operator, Frobenius,
Ky Fan and nuclear norms, together with the bridges to and from the square
`UnitarilyInvariantNorm`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm`,
  split out on 2026-07-28 because that file had grown to 2124 lines while Tau Ceti's
  `lean_lib` enforces a hard 1500-line ceiling, and 1000 for a newly added file.
* Extraction class: **split**.  No statement, proof or declaration name changed; only
  `exists_unitary_factorization_of_singularValues_eq` was promoted from `private` to
  public, because the split puts its users in a different module.
* Original authors / copyright: Jon Crall, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

namespace RectangularUnitarilyInvariantNorm

variable (N : RectangularUnitarilyInvariantNorm 𝕜 E F)

/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/
attribute [local instance] realModuleLinearMap


/-- Adjoint transport to the transposed rectangular norm. -/
noncomputable def adjointTransport
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F) :
    RectangularUnitarilyInvariantNorm 𝕜 F E where
  toFun A := N A.adjoint
  add_le' A B := by
    simpa only [map_add] using N.add_le A.adjoint B.adjoint
  smul' a A := by
    rw [map_smulₛₗ]
    calc
      N ((starRingEnd 𝕜) a • A.adjoint) =
          ‖(starRingEnd 𝕜) a‖ * N A.adjoint :=
        N.smul_eq ((starRingEnd 𝕜) a) A.adjoint
      _ = ‖a‖ * N A.adjoint := by
        congr 1
        change ‖star a‖ = ‖a‖
        exact norm_star a
  invariant' U V A := by
    change N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).adjoint = N A.adjoint
    simpa only [LinearMap.adjoint_comp,
      V.adjoint_toLinearMap_eq_symm, U.adjoint_toLinearMap_eq_symm,
      LinearMap.comp_assoc] using
      N.invariant V.symm U.symm A.adjoint


@[simp] theorem adjointTransport_apply (A : E →ₗ[𝕜] F) :
    (adjointTransport N).toFun A.adjoint = N.toFun A := by
  simp only [adjointTransport, LinearMap.adjoint_adjoint]


/-- Left ideal property.  This is Fan dominance applied to the pointwise
singular-value bound for composition by a bounded left factor. -/
theorem comp_le_opNorm_mul (C : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N (C ∘ₗ A) ≤ ‖C.toContinuousLinearMap‖ * N A := by
  let c : ℝ := ‖C.toContinuousLinearMap‖
  have hc : 0 ≤ c := norm_nonneg _
  calc
    N (C ∘ₗ A) ≤ N (((c : 𝕜)) • A) :=
      N.apply_le_of_singularValues_le fun i => by
        rw [singularValues_real_smul A hc i]
        exact singularValues_comp_le hc
          (fun y => C.toContinuousLinearMap.le_opNorm y) A i
    _ = c * N A := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]
    _ = ‖C.toContinuousLinearMap‖ * N A := by rfl

/-- Right ideal property, obtained from the left ideal property by adjoint
transport. -/
theorem comp_le_mul_opNorm (A : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E) :
    N (A ∘ₗ C) ≤ N A * ‖C.toContinuousLinearMap‖ := by
  have h := comp_le_opNorm_mul (adjointTransport N) C.adjoint A.adjoint
  rw [← LinearMap.adjoint_comp, adjointTransport_apply,
    adjointTransport_apply, LinearMap.adjoint_toContinuousLinearMap,
    LinearIsometryEquiv.norm_map] at h
  simpa only [mul_comm] using h

/-- Product-coordinate form of the zero extension, `(x,y) ↦ (0,A x)`. -/
private noncomputable def zeroExtensionProd (A : E →ₗ[𝕜] F) :
    (E × F) →ₗ[𝕜] (E × F) where
  toFun z := (0, A z.1)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Zero extension of a rectangular map to a square endomorphism. -/
noncomputable def zeroExtension (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    zeroExtensionProd A ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] theorem zeroExtension_apply (A : E →ₗ[𝕜] F)
    (z : WithLp 2 (E × F)) :
    zeroExtension A z = WithLp.toLp 2 (0, A (WithLp.ofLp z).1) := by
  rfl

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Zero extension is additive. -/
theorem zeroExtension_add (A B : E →ₗ[𝕜] F) :
    zeroExtension (A + B) = zeroExtension A + zeroExtension B := by
  ext z
  simp only [zeroExtension_apply, LinearMap.add_apply]
  simpa using
    (WithLp.toLp_add (p := 2)
      ((0, A (WithLp.ofLp z).1) : E × F)
      ((0, B (WithLp.ofLp z).1) : E × F))

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Zero extension commutes with scalar multiplication. -/
theorem zeroExtension_smul (a : 𝕜) (A : E →ₗ[𝕜] F) :
    zeroExtension (a • A) = a • zeroExtension A := by
  ext z
  simp only [zeroExtension_apply, LinearMap.smul_apply]
  simpa [smul_zero] using
    (WithLp.toLp_smul (p := 2) a ((0, A (WithLp.ofLp z).1) : E × F))

/-- Isometric embedding into the first coordinate of the `L²` product. -/
private noncomputable def zeroExtensionInl :
    E →ₗᵢ[𝕜] WithLp 2 (E × F) :=
  (((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      LinearMap.inl 𝕜 E F)).isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

/-- Isometric embedding into the second coordinate of the `L²` product. -/
private noncomputable def zeroExtensionInr :
    F →ₗᵢ[𝕜] WithLp 2 (E × F) :=
  (((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      LinearMap.inr 𝕜 E F)).isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] private theorem zeroExtensionInl_apply (x : E) :
    zeroExtensionInl (𝕜 := 𝕜) (F := F) x = WithLp.toLp 2 (x, 0) := by
  rfl

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
@[simp] private theorem zeroExtensionInr_apply (y : F) :
    zeroExtensionInr (𝕜 := 𝕜) (E := E) y = WithLp.toLp 2 (0, y) := by
  rfl

private theorem zeroExtensionInl_adjoint_apply
    (z : WithLp 2 (E × F)) :
    LinearMap.adjoint (zeroExtensionInl (𝕜 := 𝕜) (F := F)).toLinearMap z = z.fst := by
  apply ext_inner_right 𝕜
  intro x
  rw [LinearMap.adjoint_inner_left]
  simp [WithLp.prod_inner_apply]

/-- Singular values are unchanged by zero extension, apart from zero padding.
-/
theorem singularValues_zeroExtension (A : E →ₗ[𝕜] F) :
    (zeroExtension A).singularValues = A.singularValues := by
  let ιE : E →ₗᵢ[𝕜] WithLp 2 (E × F) :=
    zeroExtensionInl (𝕜 := 𝕜) (E := E) (F := F)
  let ιF : F →ₗᵢ[𝕜] WithLp 2 (E × F) :=
    zeroExtensionInr (𝕜 := 𝕜) (E := E) (F := F)
  have hfactor : zeroExtension A =
      ιF.toLinearMap ∘ₗ
        (A ∘ₗ LinearMap.adjoint ιE.toLinearMap) := by
    ext z
    simp only [LinearMap.comp_apply, zeroExtension_apply, ιE, ιF,
      LinearIsometry.coe_toLinearMap, zeroExtensionInr_apply,
      zeroExtensionInl_adjoint_apply, WithLp.ofLp_fst]
  rw [hfactor]
  calc
    (ιF.toLinearMap ∘ₗ
        (A ∘ₗ LinearMap.adjoint ιE.toLinearMap)).singularValues =
        (A ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues :=
      singularValues_linearIsometry_comp ιF _
    _ = A.singularValues :=
      singularValues_comp_adjoint_linearIsometry ιE A

/-- Operator norm as a rectangular UI norm. -/
noncomputable def opNorm : RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A := ‖A.toContinuousLinearMap‖
  add_le' A B := by
    rw [map_add]
    exact norm_add_le _ _
  smul' a A := by
    rw [map_smul]
    exact norm_smul a _
  invariant' U V A := by
    have hcomp :
        (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).toContinuousLinearMap =
          (U : F →L[𝕜] F) ∘L A.toContinuousLinearMap ∘L (V : E →L[𝕜] E) := by
      ext x
      simp
    rw [hcomp]
    simp

@[simp] theorem opNorm_apply (A : E →ₗ[𝕜] F) :
    opNorm A = ‖A.toContinuousLinearMap‖ := rfl

/-- Minkowski for finite Euclidean column-norm vectors. -/
private theorem sqrt_sum_add_sq_le_rect {m : ℕ} (f g : Fin m → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2)
      ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  let x : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm f
  let y : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm g
  have hnx : ‖x‖ = Real.sqrt (∑ i, f i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show x i = f i from rfl, Real.norm_eq_abs, sq_abs])
  have hny : ‖y‖ = Real.sqrt (∑ i, g i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [show y i = g i from rfl, Real.norm_eq_abs, sq_abs])
  have hnxy : ‖x + y‖ = Real.sqrt (∑ i, (f i + g i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by
      rw [PiLp.add_apply, show x i = f i from rfl,
        show y i = g i from rfl, Real.norm_eq_abs, sq_abs])
  rw [← hnx, ← hny, ← hnxy]
  exact norm_add_le x y

/-- Frobenius/Hilbert--Schmidt norm as a rectangular UI norm. -/
noncomputable def frobenius : RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A := Real.sqrt
    (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2)
  add_le' A B := by
    have hmono :
        Real.sqrt (∑ i, ‖(A + B) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) ≤
          Real.sqrt (∑ i, (‖A (stdOrthonormalBasis 𝕜 E i)‖ +
            ‖B (stdOrthonormalBasis 𝕜 E i)‖) ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [LinearMap.add_apply]
      exact norm_add_le _ _
    exact hmono.trans (sqrt_sum_add_sq_le_rect _ _)
  smul' a A := by
    have h : ∀ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
        ‖a‖ ^ 2 * ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 := fun i => by
      rw [LinearMap.smul_apply, norm_smul, mul_pow]
    rw [show (∑ i, ‖(a • A) (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
        ‖a‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => h i,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg a)]
  invariant' U V A := by
    have key : ∀ i,
        ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
            (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
          ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 := fun i => by
      rw [show (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
          (stdOrthonormalBasis 𝕜 E i) =
          U (A (V (stdOrthonormalBasis 𝕜 E i))) from rfl,
        U.norm_map]
    rw [show (∑ i, ‖(U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)
          (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) =
        ∑ i, ‖A (V (stdOrthonormalBasis 𝕜 E i))‖ ^ 2 from
        Finset.sum_congr rfl fun i _ => key i,
      sum_sq_norm_apply_unitary_comp A V rfl (stdOrthonormalBasis 𝕜 E)]

/-- Singular values scale by the norm of an arbitrary scalar. -/
theorem singularValues_smul_rect (a : 𝕜) (A : E →ₗ[𝕜] F) (i : ℕ) :
    (a • A).singularValues i = ‖a‖ * A.singularValues i := by
  have hgram : (a • A).adjoint ∘ₗ (a • A) =
      (((‖a‖ : ℝ) : 𝕜) • A).adjoint ∘ₗ (((‖a‖ : ℝ) : 𝕜) • A) := by
    ext x
    apply ext_inner_right 𝕜
    intro y
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    rw [← mul_assoc, RCLike.mul_conj]
    ring
  calc
    (a • A).singularValues i =
        (((‖a‖ : ℝ) : 𝕜) • A).singularValues i :=
      congrArg (fun s : ℕ →₀ ℝ => s i)
        (singularValues_eq_of_gram_eq hgram)
    _ = ‖a‖ * A.singularValues i :=
      singularValues_real_smul A (norm_nonneg a) i


/-- Bundled singular-value sequence of a scalar multiple.  This is the
Finsupp-level companion to `singularValues_smul_rect`; it is convenient when
a unitarily invariant norm is compared through its complete gauge sequence. -/
theorem singularValues_smul (a : 𝕜) (A : E →ₗ[𝕜] F) :
    (a • A).singularValues = ‖a‖ • A.singularValues := by
  ext i
  simp [singularValues_smul_rect]

/-- Prefix sums stabilize once the prefix length reaches the domain dimension. -/
theorem rectangularKyFanSum_eq_finrank_of_finrank_le
    (A : E →ₗ[𝕜] F) {k : ℕ} (hk : finrank 𝕜 E ≤ k) :
    rectangularKyFanSum k A = rectangularKyFanSum (finrank 𝕜 E) A := by
  unfold rectangularKyFanSum
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono hk)
  intro i hi hiE
  rw [A.singularValues_of_finrank_le]
  exact Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hiE)

private theorem rectangularKyFanSum_eq_zeroExtension
    (k : ℕ) (A : E →ₗ[𝕜] F) :
    rectangularKyFanSum k A = kyFanSum k (zeroExtension A) := by
  rw [kyFanSum_eq_sum_fin]
  unfold rectangularKyFanSum
  rw [singularValues_zeroExtension]

/-- **Rectangular Ky Fan variational principle, upper bound.**

For orthonormal domain and codomain families, the real part of the paired
matrix coefficient sum is bounded by the corresponding singular-value prefix.
The proof embeds both families in the two coordinates of the `L²` product and
applies the square Ky Fan variational principle to `zeroExtension A`. -/
theorem re_sum_inner_map_le_rectangularKyFanSum
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ rectangularKyFanSum k A := by
  let u' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (0, u i)
  let v' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (v i, 0)
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    simpa [u', WithLp.prod_inner_apply] using hu i j
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [v', WithLp.prod_inner_apply] using hv i j
  have hfin : finrank 𝕜 (WithLp 2 (E × F)) =
      finrank 𝕜 E + finrank 𝕜 F := by
    calc
      finrank 𝕜 (WithLp 2 (E × F)) = finrank 𝕜 (E × F) :=
        (WithLp.linearEquiv 2 𝕜 (E × F)).finrank_eq
      _ = finrank 𝕜 E + finrank 𝕜 F := by
        simp [Module.finrank_prod]
  have hk' : k ≤ finrank 𝕜 (WithLp 2 (E × F)) := by
    rw [hfin]
    omega
  have h := TauCeti.re_sum_inner_map_le_sum_singularValues
    (A := zeroExtension A) hk' hu' hv'
  simpa [u', v', zeroExtension_apply, WithLp.prod_inner_apply,
    rectangularKyFanSum, singularValues_zeroExtension] using h

/-- A convenient witness form of the rectangular Ky Fan upper bound. -/
theorem sum_le_rectangularKyFanSum_of_orthonormal
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ RCLike.re ⟪u i, A (v i)⟫_𝕜) :
    ∑ i, t i ≤ rectangularKyFanSum k A := by
  calc
    ∑ i, t i ≤ ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 :=
      Finset.sum_le_sum fun i _ => ht i
    _ = RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) := by
      rw [map_sum]
    _ ≤ rectangularKyFanSum k A :=
      re_sum_inner_map_le_rectangularKyFanSum hk hu hv

private theorem rectangularKyFanSum_add_le (k : ℕ)
    (A B : E →ₗ[𝕜] F) :
    rectangularKyFanSum k (A + B) ≤
      rectangularKyFanSum k A + rectangularKyFanSum k B := by
  have hadd : zeroExtension (A + B) =
      zeroExtension A + zeroExtension B := by
    ext z
    simp only [zeroExtension_apply, LinearMap.add_apply]
    simpa using
      (WithLp.toLp_add (p := 2)
        ((0, A (WithLp.ofLp z).1) : E × F)
        ((0, B (WithLp.ofLp z).1) : E × F))
  rw [rectangularKyFanSum_eq_zeroExtension,
    rectangularKyFanSum_eq_zeroExtension,
    rectangularKyFanSum_eq_zeroExtension, hadd]
  exact kyFanSum_add_le k _ _

/-- Ky Fan `k`-norm. -/
noncomputable def kyFan (k : ℕ) : RectangularUnitarilyInvariantNorm 𝕜 E F where
  toFun A := rectangularKyFanSum k A
  add_le' A B := rectangularKyFanSum_add_le k A B
  smul' a A := by
    unfold rectangularKyFanSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => singularValues_smul_rect a A (i : ℕ)
  invariant' U V A := by
    unfold rectangularKyFanSum
    rw [singularValues_unitary_comp, singularValues_comp_unitary]

/-- Nuclear/trace norm. -/
noncomputable def nuclear : RectangularUnitarilyInvariantNorm 𝕜 E F :=
  kyFan (finrank 𝕜 E)

/-- The rectangular Frobenius norm is the square root of the sum of squared
column norms in any orthonormal basis of the domain.
-/
theorem frobenius_apply (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    frobenius A = Real.sqrt (∑ i, ‖A (b i)‖ ^ 2) := by
  change Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) = _
  rw [← sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E),
    ← sum_sq_singularValues A rfl b]

/-- Postcomposition by a linear isometry preserves the Frobenius norm. -/
theorem frobenius_linearIsometry_comp
    (ι : F →ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    frobenius (ι.toLinearMap ∘ₗ A) = frobenius A := by
  rw [frobenius_apply _ (stdOrthonormalBasis 𝕜 E),
    frobenius_apply _ (stdOrthonormalBasis 𝕜 E)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, ι.norm_map]

/-- Orthogonal projection on the codomain is contractive for the Frobenius norm. -/
theorem frobenius_projection_comp_le
    (U : Submodule 𝕜 F) [U.HasOrthogonalProjection] (A : E →ₗ[𝕜] F) :
    frobenius (((U.starProjection : F →L[𝕜] F) : F →ₗ[𝕜] F) ∘ₗ A) ≤ frobenius A := by
  rw [frobenius_apply _ (stdOrthonormalBasis 𝕜 E),
    frobenius_apply _ (stdOrthonormalBasis 𝕜 E)]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (U.norm_starProjection_apply_le _) 2

/-- Passing from a subtype-valued map to its ambient inclusion preserves the
Frobenius norm. -/
theorem frobenius_subtype_comp
    (U : Submodule 𝕜 F) (A : E →ₗ[𝕜] U) :
    frobenius (U.subtypeₗᵢ.toLinearMap ∘ₗ A) = frobenius A :=
  frobenius_linearIsometry_comp U.subtypeₗᵢ A

/-- The Ky Fan norm evaluates to the prefix sum of singular values.
-/
theorem kyFan_apply (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFan k A = rectangularKyFanSum k A :=
  rfl

/-- A finite two-sided unitary-orbit certificate bounds every rectangular
Ky Fan prefix by the same certificate mass.

This is the exact bridge used by the arbitrary-spectrum Sylvester theorem. -/
theorem rectangularKyFanSum_le_of_finiteUnitaryOrbitCertificate
    {mass : ℝ} {X C : E →ₗ[𝕜] F} (k : ℕ)
    (hcert : HasFiniteUnitaryOrbitCertificate mass X C) :
    rectangularKyFanSum k X ≤ mass * rectangularKyFanSum k C := by
  change kyFan k X ≤ mass * kyFan k C
  exact (kyFan k).apply_le_of_finiteUnitaryOrbitCertificate hcert

/-- The nuclear norm is the full domain-length singular-value sum; singular
values past the rank are zero automatically. -/
theorem nuclear_apply (A : E →ₗ[𝕜] F) :
    nuclear A = ∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) :=
  rfl

/-- The rectangular Frobenius norm is the Euclidean norm of the complete
finite singular-value list. -/
theorem frobenius_eq_sqrt_sum_sq_singularValues (A : E →ₗ[𝕜] F) :
    frobenius A = Real.sqrt
      (∑ i : Fin (finrank 𝕜 E), A.singularValues (i : ℕ) ^ 2) := by
  rw [frobenius_apply A (stdOrthonormalBasis 𝕜 E),
    sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E)]



/-- The nuclear norm of a Gram operator is the squared Frobenius energy, written
as a column-norm sum in any orthonormal basis. -/
theorem nuclear_adjoint_comp_self_eq_sum_sq_norm
    (A : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    nuclear (A.adjoint ∘ₗ A) = ∑ i, ‖A (b i)‖ ^ 2 := by
  let G := A.adjoint ∘ₗ A
  have hG : G.IsPositive := LinearMap.isPositive_adjoint_comp_self A
  have hGabs : TauCeti.abs G = G := by
    symm
    exact (LinearMap.isPositive_adjoint_comp_self G).sqrt_unique hG (by
      rw [hG.adjoint_eq])
  rw [nuclear_apply,
    ← sum_re_inner_abs_self_eq_sum_singularValues G rfl b,
    hGabs]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [G, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq]

/-- The nuclear norm is bounded by the square root of the domain dimension
times the Frobenius norm.  This is the finite Cauchy--Schwarz inequality for
the complete singular-value list, including its trailing zeros. -/
theorem nuclear_le_sqrt_finrank_mul_frobenius (A : E →ₗ[𝕜] F) :
    nuclear A ≤ Real.sqrt (finrank 𝕜 E) * frobenius A := by
  rw [nuclear_apply, frobenius_eq_sqrt_sum_sq_singularValues]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (s := Finset.univ)
    (f := fun _ : Fin (finrank 𝕜 E) => (1 : ℝ))
    (g := fun i : Fin (finrank 𝕜 E) => A.singularValues (i : ℕ))
  simpa [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    using hcs

end RectangularUnitarilyInvariantNorm

/-- Restrict a rectangular UI norm to square maps. -/
noncomputable def RectangularUnitarilyInvariantNorm.toSquare
    (N : RectangularUnitarilyInvariantNorm 𝕜 E E) :
    UnitarilyInvariantNorm 𝕜 E where
  toFun := N.toFun
  add_le' := N.add_le'
  smul' := N.smul'
  invariant' := N.invariant'

end DavisKahanTheory

namespace UnitarilyInvariantNorm

open DavisKahanTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Embed the existing square abstraction into the rectangular API. -/
noncomputable def toRectangular
    (N : UnitarilyInvariantNorm 𝕜 E) :
    RectangularUnitarilyInvariantNorm 𝕜 E E where
  toFun := N.toFun
  add_le' := N.add_le'
  smul' := N.smul'
  invariant' := N.invariant'


@[simp] theorem toRectangular_apply
    (N : UnitarilyInvariantNorm 𝕜 E) (A : E →ₗ[𝕜] E) :
    N.toRectangular A = N A :=
  rfl

end UnitarilyInvariantNorm
end TauCeti
