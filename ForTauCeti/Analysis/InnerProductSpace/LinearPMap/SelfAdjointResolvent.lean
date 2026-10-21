/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Shift
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-!
# A self-adjoint operator has real spectrum

The basic criterion: for a self-adjoint `A : E →ₗ.[ℂ] E` and `z` off the real
axis, `A - z` has a bounded two-sided inverse, with `‖(A - z)⁻¹‖ ≤ |Im z|⁻¹`.
Hence `spectrum A ⊆ ℝ`.

The argument is the classical one, in three steps:

1. **the estimate** `‖(A - z) x‖ ≥ |Im z| ‖x‖` — because `⟪A x, x⟫` is real, the
   cross term in `‖(A - Re z) x - i (Im z) x‖²` is purely imaginary and drops
   out, leaving `‖(A - Re z)x‖² + (Im z)² ‖x‖²`;
2. **closed range** — the estimate plus closedness of `A` (self-adjoint
   operators are closed) makes the range of `A - z` closed;
3. **dense range** — a vector orthogonal to the range is an eigenvector of `A`
   for the eigenvalue `conj z`, and self-adjointness forces its eigenvalues to
   be real, so it vanishes.

## Provenance

* **Extraction class:** mixed. The shift estimate, closed-range argument, and
  gap-specific bounded inverse remain donor mathematics. Tau Ceti now owns the
  general off-real resolvent criterion, its norm bound, and the adjoint and
  self-adjointness laws for resolvents; the corresponding local proofs forward
  to those declarations.
* **Representation boundary:** the older donor resolvent lives under
  `TauCeti.LinearPMap`, while the accepted API extends root `LinearPMap`. A
  single private conversion layer keeps existing consumers compiling while
  they move to the accepted resolver and spectrum. It is temporary migration
  support, not a second public API.
* **Spectra influence:** Spectra's resolvent criterion helped identify the
  needed result. The accepted Tau Ceti statements and proofs are the maintained
  implementation.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Estimate
-- The estimate needs no completeness; `Star` on `LinearPMap` does, so the
-- self-adjointness results below open their own section.

/-- **The exact norm identity.**  `‖(A - z)x‖² = ‖(A - Re z)x‖² + (Im z)²‖x‖²`.

The cross term vanishes because `⟪A x - (Re z) x, x⟫` is real while the vector
subtracted from it is `i (Im z) x`. -/
theorem norm_sub_smul_sq {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    ‖A x - z • (x : E)‖ ^ 2
      = ‖A x - (z.re : ℂ) • (x : E)‖ ^ 2 + (z.im) ^ 2 * ‖(x : E)‖ ^ 2 := by
  set u : E := A x - (z.re : ℂ) • (x : E) with hu
  have hsplit : A x - z • (x : E) = u - ((z.im : ℂ) * Complex.I) • (x : E) := by
    rw [hu]
    have : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
    rw [show z • (x : E) = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • (x : E) by rw [← this]]
    rw [add_smul]
    abel
  -- `⟪u, x⟫` is real
  have hreal : (starRingEnd ℂ) ⟪u, (x : E)⟫_ℂ = ⟪u, (x : E)⟫_ℂ := by
    rw [hu, inner_sub_left, inner_smul_left, map_sub, map_mul]
    rw [inner_apply_self_isReal hsym x]
    simp [Complex.conj_ofReal]
  -- the cross term is purely imaginary
  have hcross : RCLike.re ⟪u, (((z.im : ℂ) * Complex.I) • (x : E))⟫_ℂ = 0 := by
    have hr : (⟪u, (x : E)⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
    rw [inner_smul_right]
    simp [hr]
  rw [hsplit, @norm_sub_sq ℂ, hcross, norm_smul]
  simp [Complex.norm_I, Complex.norm_real, mul_pow, sq_abs]

/-- **The basic estimate.**  `‖(A - z) x‖ ≥ |Im z| ‖x‖` for symmetric `A`. -/
theorem norm_sub_smul_ge_abs_im {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖ := by
  have hsq := norm_sub_smul_sq hsym z x
  nlinarith [norm_nonneg (A x - z • (x : E)), norm_nonneg (A x - (z.re : ℂ) • (x : E)),
    norm_nonneg ((x : E)), abs_nonneg z.im, sq_abs z.im,
    sq_nonneg ‖A x - (z.re : ℂ) • (x : E)‖, hsq,
    mul_nonneg (abs_nonneg z.im) (norm_nonneg ((x : E)))]

end Estimate

/-! ### Temporary compatibility for consumers of the donor resolvent API

Tau Ceti's resolvent and the donor's older resolvent have the same inverse
fields, but live under different namespace-level definitions. Keep the conversion
in one place while dependent modules migrate to the upstream representation. -/

private theorem root_mem_resolventSet_toLocal {A : E →ₗ.[ℂ] E} {z : ℂ}
    (h : z ∈ _root_.LinearPMap.resolventSet A) : z ∈ resolventSet A := by
  obtain ⟨R, hR⟩ := _root_.LinearPMap.mem_resolventSet_iff.mp h
  exact mem_resolventSet_iff.mpr ⟨R, ⟨hR.mem_domain, hR.smul_sub_apply, hR.apply_smul_sub⟩⟩

private theorem local_mem_resolventSet_toRoot {A : E →ₗ.[ℂ] E} {z : ℂ}
    (h : z ∈ resolventSet A) : z ∈ _root_.LinearPMap.resolventSet A := by
  obtain ⟨R, hR⟩ := mem_resolventSet_iff.mp h
  exact _root_.LinearPMap.mem_resolventSet_iff.mpr ⟨R, ⟨hR.mem_domain, hR.smul_sub_apply,
    hR.apply_smul_sub⟩⟩

private theorem local_resolvent_eq_root {A : E →ₗ.[ℂ] E} {z : ℂ}
    (h : z ∈ _root_.LinearPMap.resolventSet A) :
    resolvent A z = _root_.LinearPMap.resolvent A z := by
  have hR := _root_.LinearPMap.isResolventAt_resolvent h
  have hLocal : IsResolventAt A z (_root_.LinearPMap.resolvent A z) := {
    mem_domain := hR.mem_domain
    smul_sub_apply := hR.smul_sub_apply
    apply_smul_sub := hR.apply_smul_sub
  }
  exact resolvent_eq_of_isResolventAt hLocal

section SelfAdjoint

variable [CompleteSpace E]

/-- **Dense range.**  A vector orthogonal to the range of `A - z` would make
`z ⟪y, y⟫` real; since `⟪y, y⟫` is a nonnegative real, a non-real `z` forces
`y = 0`.

This is the usual "a self-adjoint operator has no non-real eigenvalue" argument,
arranged so that it never has to name the eigenvector equation — only the
quadratic form appears, which avoids transporting `A† = A` under a dependent
domain membership. -/
theorem eq_zero_of_orthogonal_shiftRange {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) {y : E}
    (hy : ∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_ℂ = 0) : y = 0 := by
  have hdense : Dense (A.domain : Set E) := hA.dense_domain
  -- `⟪conj z • y, x⟫ = ⟪y, A x⟫`, which puts `y` in the adjoint's domain
  have hEq : ∀ x : A.domain, ⟪(starRingEnd ℂ) z • y, (x : E)⟫_ℂ = ⟪y, A x⟫_ℂ :=
    inner_conj_smul_eq_of_orthogonal_shiftRange hy
  have hmem : y ∈ (_root_.LinearPMap.adjoint A).domain :=
    _root_.LinearPMap.mem_adjoint_domain_of_exists _ ⟨(starRingEnd ℂ) z • y, hEq⟩
  have hmemA : y ∈ A.domain := by
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmem
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hdense
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  -- `⟪y, A y⟫` is real, and equals `z * ⟪y, y⟫`
  have hkey : (starRingEnd ℂ) ⟪y, A ⟨y, hmemA⟩⟫_ℂ = ⟪y, A ⟨y, hmemA⟩⟫_ℂ := by
    rw [inner_conj_symm]
    exact hsym ⟨y, hmemA⟩ ⟨y, hmemA⟩
  have hzy : z * ⟪y, y⟫_ℂ = ⟪y, A ⟨y, hmemA⟩⟫_ℂ := by
    have h := hEq ⟨y, hmemA⟩
    rwa [inner_smul_left, starRingEnd_self_apply] at h
  rw [← hzy, map_mul, inner_self_conj] at hkey
  -- `conj z * ⟪y,y⟫ = z * ⟪y,y⟫`
  by_contra hy0
  have hnz : ⟪y, y⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hy0
  have : (starRingEnd ℂ) z = z := mul_right_cancel₀ hnz hkey
  exact hz (Complex.conj_eq_iff_im.mp this)

/-- **Closed range.**  The estimate turns a convergent sequence in the range into
a Cauchy sequence of preimages; closedness of `A` (which self-adjointness
supplies) identifies the limit. -/
theorem isClosed_range_shiftMap {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    IsClosed (Set.range (shiftMap A z)) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact isClosed_range_shiftMap_of_lower_bound hA (abs_pos.mpr hz)
    (norm_sub_smul_ge_abs_im hsym z)

omit [CompleteSpace E] in
/-- The shifted map `A - z` is injective for non-real `z`: the imaginary part of the quadratic form
bounds it below. -/
theorem injective_shiftMap {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : Function.Injective (shiftMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h := norm_sub_smul_ge_abs_im hsym z x
  rw [show A x - z • (x : E) = shiftMap A z x from rfl, hx, norm_zero] at h
  have hxz : ‖(x : E)‖ = 0 := by
    nlinarith [abs_pos.mpr hz, norm_nonneg ((x : E))]
  exact Subtype.ext (by simpa using hxz)

/-- The shifted map is surjective.  This is the harder half -- it needs closed range, which comes
from the same lower bound plus closedness of `A`. -/
theorem surjective_shiftMap {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : Function.Surjective (shiftMap A z) := by
  have hclosed := isClosed_range_shiftMap hA hz
  set K : Submodule ℂ E := LinearMap.range (shiftMap A z) with hK
  have hKclosed : IsClosed (K : Set E) := hclosed
  have : K.HasOrthogonalProjection :=
    haveI : CompleteSpace K := hKclosed.completeSpace_coe
    inferInstance
  have hperp : Kᗮ = ⊥ :=
    orthogonal_range_shiftMap_eq_bot fun _ hy => eq_zero_of_orthogonal_shiftRange hA hz hy
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  intro y
  have : y ∈ K := hKtop ▸ Submodule.mem_top
  exact this

/-- **A self-adjoint operator has real spectrum**, quantitatively: every `z` off
the real axis lies in the local resolvent set.

The proof uses Tau Ceti's general `RCLike` resolvent theorem. The final conversion
only adapts its root `LinearPMap.IsResolventAt` witness to the still-local
`TauCeti.LinearPMap.IsResolventAt` API; remove this adapter when consumers finish
migrating to Tau Ceti's canonical resolvent set. -/
theorem mem_resolventSet_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A := by
  have hroot : z ∈ _root_.LinearPMap.resolventSet A :=
    hA.mem_resolventSet_of_im_ne_zero hz
  exact root_mem_resolventSet_toLocal hroot

/-- The resolvent of a self-adjoint operator at a non-real point is bounded by
the reciprocal distance to the real axis. -/
theorem norm_resolvent_le_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A z‖ ≤ |z.im|⁻¹ := by
  have hroot : z ∈ _root_.LinearPMap.resolventSet A :=
    hA.mem_resolventSet_of_im_ne_zero hz
  rw [local_resolvent_eq_root hroot]
  exact hA.norm_resolvent_le hz

/-- The resolvent of a self-adjoint operator at a **real** point is a
self-adjoint bounded operator. -/
theorem isSelfAdjoint_resolvent_ofReal {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {c : ℝ} (hc : (c : ℂ) ∈ resolventSet A) :
    _root_.IsSelfAdjoint (resolvent A (c : ℂ)) := by
  let hcRoot := local_mem_resolventSet_toRoot hc
  rw [local_resolvent_eq_root hcRoot]
  exact hA.isSelfAdjoint_resolvent hcRoot (by simp)

/-- **The adjoint of the resolvent is the resolvent at the conjugate point:**
`R(z)⋆ = R(z̄)`.

Both sides are pinned by the two-sided inverse property: writing `u = R(z) x` and
`v = R(z̄) y`, symmetry of `A` turns `⟪u, (z • I - A) v⟫` into `⟪(z̄ • I - A) u, v⟫`. -/
theorem adjoint_resolvent {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ resolventSet A) (hzc : (starRingEnd ℂ) z ∈ resolventSet A) :
    ContinuousLinearMap.adjoint (resolvent A z) = resolvent A ((starRingEnd ℂ) z) := by
  let hzRoot := local_mem_resolventSet_toRoot hz
  let hzcRoot := local_mem_resolventSet_toRoot hzc
  rw [local_resolvent_eq_root hzRoot, local_resolvent_eq_root hzcRoot]
  exact hA.adjoint_resolvent hzRoot

/-! ### The Cayley transform

`U = (A - i)(A + i)⁻¹`, written as `1 - 2i·R(-i)` so that boundedness is manifest
and no domain bookkeeping is needed.  It is the bridge from the unbounded
self-adjoint `A` to a *bounded unitary*, where Mathlib's continuous functional
calculus applies. -/

/-- `-i` is a resolvent point of a self-adjoint operator. -/
theorem negI_mem_resolventSet {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    (-Complex.I) ∈ resolventSet A :=
  mem_resolventSet_of_im_ne_zero hA (by simp)

/-- `i` is a resolvent point of a self-adjoint operator. -/
theorem I_mem_resolventSet {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    Complex.I ∈ resolventSet A :=
  mem_resolventSet_of_im_ne_zero hA (by simp)

/-- **The Cayley transform** `(A - i)(A + i)⁻¹`, in the manifestly bounded form
`1 + 2i·R(-i)`.

The canonical resolvent inverts `-i • I - A`, so `(A + i)⁻¹ = -R(-i)` and the
`-2i` of the `(A - z)` convention becomes `+2i` here. -/
@[expose]
noncomputable def cayley {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  1 + (2 * Complex.I) • resolvent A (-Complex.I)

/-- Rewrite form of `cayley`, so call sites need not unfold the definition.

Added 2026-07-30: `SpectralMeasure/Construction` was doing `simp [cayley]`, which needs
the body exposed. Tau Ceti's `api-design` rubric asks for the lemma instead. -/
theorem cayley_def {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    cayley hA = 1 + (2 * Complex.I) • resolvent A (-Complex.I) := (rfl)

/-- On a vector, `U ξ = (i • I - A) R(-i) ξ`, i.e. `(A - i)` applied to the
preimage of `ξ` under `A + i`, that preimage being `-R(-i) ξ`.

Deliberately **not** `@[simp]`: it rewrites the Cayley
transform into a resolvent expression, which is not a normal form — downstream proofs
work with `cayley` folded and unfold it by name where they mean to. -/
theorem cayley_apply {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (ξ : E) :
    cayley hA ξ
      = Complex.I • resolvent A (-Complex.I) ξ
        - A ⟨resolvent A (-Complex.I) ξ,
            resolvent_mem_domain (negI_mem_resolventSet hA) ξ⟩ := by
  set h := negI_mem_resolventSet hA with hh
  set x := resolvent A (-Complex.I) ξ with hx
  have hmem : x ∈ A.domain := resolvent_mem_domain h ξ
  have hsolve : (-Complex.I) • x - A ⟨x, hmem⟩ = ξ := smul_sub_apply_resolvent h ξ
  have hAx : A ⟨x, hmem⟩ = -(Complex.I • x) - ξ := by
    rw [← hsolve]; module
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ξ + (2 * Complex.I) • x = Complex.I • x - A ⟨x, hmem⟩
  rw [hAx]
  module

/-- **The Cayley transform is isometric.**  Both `‖(A - i)x‖²` and `‖(A + i)x‖²`
equal `‖Ax‖² + ‖x‖²`, by the exact norm identity. -/
@[simp]
theorem norm_cayley_apply {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (ξ : E) :
    ‖cayley hA ξ‖ = ‖ξ‖ := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  set h := negI_mem_resolventSet hA with hh
  set x := resolvent A (-Complex.I) ξ with hx
  have hmem : x ∈ A.domain := resolvent_mem_domain h ξ
  have hsolve : (-Complex.I) • x - A ⟨x, hmem⟩ = ξ := smul_sub_apply_resolvent h ξ
  -- both shifts have the same norm, by the exact identity at `z = ±i`
  have hplus := norm_sub_smul_sq hsym (-Complex.I) ⟨x, hmem⟩
  have hminus := norm_sub_smul_sq hsym Complex.I ⟨x, hmem⟩
  simp only [Complex.neg_re, Complex.I_re, neg_zero, Complex.neg_im, Complex.I_im,
    Complex.ofReal_zero, zero_smul, sub_zero, neg_one_sq, one_pow, one_mul] at hplus hminus
  have hsq : ‖cayley hA ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    -- do not rewrite `ξ` in the goal: it occurs inside `x = R(-i) ξ`
    have hxi : ‖ξ‖ ^ 2 = ‖A ⟨x, hmem⟩ - (-Complex.I) • x‖ ^ 2 := by
      rw [← hsolve, norm_sub_rev]
    rw [cayley_apply hA ξ, norm_sub_rev, hxi, hminus, hplus]
  have h2 := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- The Cayley transform preserves inner products (polarisation of isometry). -/
theorem inner_cayley {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (ξ η : E) :
    ⟪cayley hA ξ, cayley hA η⟫_ℂ = ⟪ξ, η⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E :=
    { toLinearMap := (cayley hA : E →ₗ[ℂ] E)
      norm_map' := norm_cayley_apply hA }
  exact L.inner_map_map ξ η

/-- **The Cayley transform is surjective.**  Given `η`, solve `(i • I - A) y = η` —
possible because `i` is a resolvent point — and take `ξ = (-i • I - A) y`, which is
`-(A + i) y`. -/
theorem surjective_cayley {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    Function.Surjective (cayley hA) := by
  intro η
  set hi := I_mem_resolventSet hA with hhi
  set hni := negI_mem_resolventSet hA with hhni
  set y : E := resolvent A Complex.I η with hy
  have hymem : y ∈ A.domain := resolvent_mem_domain hi η
  have hsolve : Complex.I • y - A ⟨y, hymem⟩ = η := smul_sub_apply_resolvent hi η
  -- `ξ := (-i • I - A) y`
  refine ⟨(-Complex.I) • y - A ⟨y, hymem⟩, ?_⟩
  -- `R(-i)` inverts `-i • I - A` on the domain
  have hR : resolvent A (-Complex.I) ((-Complex.I) • y - A ⟨y, hymem⟩) = y :=
    resolvent_smul_sub_apply hni ⟨y, hymem⟩
  rw [cayley_apply hA]
  -- both the operator application and the shift collapse via `hR`
  have hdom : (⟨resolvent A (-Complex.I) ((-Complex.I) • y - A ⟨y, hymem⟩),
      resolvent_mem_domain hni _⟩ : A.domain) = ⟨y, hymem⟩ := Subtype.ext hR
  rw [hdom, hR]
  exact hsolve

/-- **The Cayley transform of a self-adjoint operator is unitary.** -/
theorem cayley_mem_unitary {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    cayley hA ∈ unitary (E →L[ℂ] E) := by
  have hstar : ContinuousLinearMap.adjoint (cayley hA) * cayley hA = 1 := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    refine ext_inner_right ℂ fun η => ?_
    calc ⟪(ContinuousLinearMap.adjoint (cayley hA) * cayley hA) ξ, η⟫_ℂ
        = ⟪cayley hA ξ, cayley hA η⟫_ℂ := by
          rw [show (ContinuousLinearMap.adjoint (cayley hA) * cayley hA) ξ
              = ContinuousLinearMap.adjoint (cayley hA) (cayley hA ξ) from rfl,
            ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪ξ, η⟫_ℂ := inner_cayley hA ξ η
      _ = ⟪(1 : E →L[ℂ] E) ξ, η⟫_ℂ := (rfl)
  have hmul : cayley hA * ContinuousLinearMap.adjoint (cayley hA) = 1 := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    obtain ⟨ζ, rfl⟩ := surjective_cayley hA ξ
    have : ContinuousLinearMap.adjoint (cayley hA) (cayley hA ζ) = ζ := by
      have := congrArg (fun T : E →L[ℂ] E => T ζ) hstar
      simpa using this
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change cayley hA (ContinuousLinearMap.adjoint (cayley hA) (cayley hA ζ)) = _
    rw [this]
    rfl
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
  exact ⟨hstar, hmul⟩

/-- The Cayley transform is star-normal, so Mathlib's continuous functional
calculus applies to it. -/
instance isStarNormal_cayley {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    IsStarNormal (cayley hA) :=
  isStarNormal_of_mem_unitary (cayley_mem_unitary hA)

end SelfAdjoint

end LinearPMap
end TauCeti
