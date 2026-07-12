/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Basic
import ForMathlib.Analysis.InnerProductSpace.KyFan
import ForMathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Convex.Caratheodory

/-!
# Rectangular unitarily invariant norms

The residual forms of the Davis--Kahan theorems compare maps between different
finite-dimensional Hilbert spaces.  The existing
`ForMathlib.UnitarilyInvariantNorm` is square.  This file scaffolds the
rectangular abstraction needed for the final literature-faithful API.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 3, 6, and 7.
* Davis--Kahan (1970), Sections 1--2 and Lemmas 6.1--6.3.
* Mirsky's symmetric-gauge correspondence, as invoked in Davis--Kahan (1970).

The intended proof path is singular-value majorization plus the ideal
property.  Square norms should be recovered without duplicating the existing
`UnitarilyInvariantNorm` development.
-/


/-! ## Remaining construction plan

Complete this module in the following order: adjoint transport, zero extension,
singular values of zero extension, square/rectangular conversion, then concrete
norm objects.  Define rectangular operator, Frobenius, Ky Fan, nuclear, and
Schatten norms from rectangular singular values (or zero extension) and prove
unitary invariance and ideal inequalities before using them in residual
results.  The evaluation lemmas should be definitional or short consequences
of `singularValues_zeroExtension`, so later concrete wrappers carry no new
analytic content.
-/


/-! ## Weak-agent execution plan: rectangular singular values and UI norms

Treat this file as an API-building project, not as a list of independent
unproved leaves.  The following order avoids circularity and uses machinery already
present in this repository.

### A. Establish the rectangular SVD/gauge seam first

The hard root of `apply_le_of_kyFanSum_le` is not zero extension.  It is the
fact that a rectangular UI seminorm depends only on the singular values.
Introduce private helpers before attempting Fan dominance:

* `rectangularDiagonal` on fixed orthonormal bases, sending the first
  `min (finrank 𝕜 E) (finrank 𝕜 F)` basis vectors to the corresponding
  nonnegative diagonal entries and the rest to zero;
* `exists_rectangular_svd`, returning `U : F ≃ₗᵢ[𝕜] F`,
  `V : E ≃ₗᵢ[𝕜] E`, and a diagonal map `D` with
  `A = U.toLinearMap ∘ₗ D ∘ₗ V.toLinearMap`;
* `singularValues_rectangularDiagonal`, including the zero-padding statement;
* a finite symmetric gauge obtained by evaluating `N` on
  `rectangularDiagonal`.

Build `exists_rectangular_svd` from eigenbases of `A.adjoint ∘ₗ A` and the
polar vectors `A vᵢ / σᵢ`.  Split indices with `σᵢ = 0`; complete the resulting
orthonormal family in `F`.  Do not divide before introducing the nonzero
singular-value hypothesis.  Equality of maps should be proved by
`LinearMap.ext` followed by expansion in the domain eigenbasis.

Once this seam exists, copy the gauge-level weak-majorization descent from
`UnitarilyInvariantNorm.apply_le_of_kyFanSum_le`; do not duplicate operator
algebra from that file.  This yields rectangular Fan dominance directly and
makes `apply_le_of_singularValues_le` a finite-sum corollary.

### B. Prove the ideal inequalities only after Fan dominance

The repository already contains the rectangular singular-value estimate
`singularValues_comp_le` in `KyFan.lean`.  For the left ideal property, set
`c := ‖C.toContinuousLinearMap‖`, prove

`(C ∘ₗ A).singularValues i ≤ c * A.singularValues i`,

identify the right side with the singular values of `((c : 𝕜) • A)` using
`singularValues_real_smul`, apply `apply_le_of_singularValues_le`, and finish
with `N.smul_eq`.  The right ideal property should be obtained by applying the
left result to adjoints after `adjointTransport` is available; this avoids
reproving the Gram-order argument for a genuinely rectangular right factor.

### C. Implement `adjointTransport` directly

Use `toFun A := N A.adjoint`.  The additive and scalar fields follow from the
adjoint laws; remember that the adjoint of `c • A` uses `star c`, whose norm is
`‖c‖`.  For invariance, adjoint reverses composition, so the two unitary
arguments swap and become their adjoints/symmetries.  Prove
`adjointTransport_apply` by `rfl` if possible.  Add private simp lemmas for the
adjoint of the relevant threefold composition rather than asking `simp` to
normalize every coercion at once.

### D. Keep zero extension secondary and define it pointwise

The existing `LinearMap.singularValues` is already rectangular, so zero
extension is only a compatibility tool.  Define

`zeroExtension A (x,y) = (0, A x)`

on `WithLp 2 (E × F)`.  A robust implementation constructs the map with
`toFun z := WithLp.toLp 2 (0, A (WithLp.ofLp z).1)` and proves linearity by
extensionality on the two product coordinates.  Immediately add simp lemmas
for its application and adjoint.  For `singularValues_zeroExtension`, prove the
Gram operator is block diagonal with blocks `A.adjoint ∘ₗ A` and `0`; then use
an orthonormal basis formed by concatenating eigenvectors of the first block
with any orthonormal basis of `F`.  Handle `i < finrank 𝕜 E` and the zero tail
as separate cases; do not attempt a single `simp` proof of the sorted sequence.

### E. Concrete norms

Construct concrete norms in this order:

1. `kyFan k` from `rectangularKyFanSum`; prove its triangle inequality by the
   rectangular Ky Fan variational principle already used in `KyFan.lean`.
2. `nuclear` as `kyFan (finrank 𝕜 E)`; zero padding makes this valid even when
   the codomain is smaller.
3. `opNorm` either from the ordinary continuous-linear-map norm or from
   `kyFan 1`; the ordinary norm gives the shortest structure proof.
4. `frobenius` from the basis sum of squares, using the existing square proof
   as a template and a rectangular Parseval calculation.
5. `schatten p` only after a finite `ℓp` symmetric-gauge lemma is available.

Do not define all five through `ofSquareFamily`; that constructor is useful for
compatibility tests, but it hides the evaluation lemmas needed downstream.
`toRectangular` in the square case should be the direct structure copy, making
`toRectangular_apply` definitional.  `ofSquareFamily` may use zero extension,
but its documentation must not claim dimension-independent uniqueness unless
compatibility between the supplied square norms is added as a hypothesis.

### F. Elaboration traps

* Distinguish `A.adjoint` as a `LinearMap` from continuous-map adjoints.
* Normalize `LinearMap.comp_apply` explicitly before rewriting pointwise.
* Use real scalar coercions `((c : ℝ) : 𝕜)` when invoking
  `singularValues_real_smul`.
* Split zero-dimensional spaces before using a norm-one or basis witness.
* Prove sequence equalities with `funext i` and explicit rank cases; sorted
  singular-value functions rarely close by `simp` globally.
-/

namespace ForMathlib
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

/-- A unitarily invariant seminorm on rectangular linear maps.

As in the existing square `UnitarilyInvariantNorm`, definiteness is deliberately
not bundled: the Davis--Kahan inequalities and Fan dominance use only
subadditivity, absolute homogeneity, and two-sided unitary invariance. -/
structure RectangularUnitarilyInvariantNorm (𝕜 E F : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] where
  toFun : (E →ₗ[𝕜] F) → ℝ
  add_le' : ∀ A B, toFun (A + B) ≤ toFun A + toFun B
  smul' : ∀ (a : 𝕜) A, toFun (a • A) = ‖a‖ * toFun A
  invariant' : ∀ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) A,
    toFun (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = toFun A

namespace RectangularUnitarilyInvariantNorm

/-- Prefix sum of singular values for a rectangular map. -/
noncomputable def rectangularKyFanSum (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)

instance : CoeFun (RectangularUnitarilyInvariantNorm 𝕜 E F)
    fun _ => (E →ₗ[𝕜] F) → ℝ :=
  ⟨RectangularUnitarilyInvariantNorm.toFun⟩

variable (N : RectangularUnitarilyInvariantNorm 𝕜 E F)

/--
Lean proof route for a weaker agent:

1. Derive `N 0 ≤ N 0 + N 0` from `add_le'` and use homogeneity at scalar zero to rewrite the left side.
2. Use nonnegativity of the codomain real norm value, or the same triangle/homogeneity argument used by the square UI-norm implementation.
3. Finish with antisymmetry; keep this as a structure-level lemma with no singular-value dependency.
-/
@[simp] theorem apply_zero : N (0 : E →ₗ[𝕜] F) = 0 := by
  have h := N.smul' 0 (0 : E →ₗ[𝕜] F)
  simpa using h

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem nonneg (A : E →ₗ[𝕜] F) : 0 ≤ N A := by
  have h := N.add_le' A (-A)
  rw [add_neg_cancel] at h
  have hneg : N.toFun (-A) = N.toFun A := by
    have h1 := N.smul' (-1) A
    simpa using h1
  have hz : N.toFun (0 : E →ₗ[𝕜] F) = 0 := apply_zero N
  rw [hz, hneg] at h
  linarith

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem add_le (A B : E →ₗ[𝕜] F) : N (A + B) ≤ N A + N B :=
  N.add_le' A B

/-- A rectangular UI seminorm of a finite sum is bounded by the sum of the
individual seminorms.

Proof strategy:

1. induct on the finite index set;
2. use `apply_zero` in the empty case;
3. use `add_le` for the inserted term and the induction hypothesis for the
   remaining sum.

This is the finite replacement for the integral triangle inequality in the
unitary-orbit proof of the `π/2` Sylvester theorem. -/
theorem sum_le {ι : Type*} (s : Finset ι) (A : ι → E →ₗ[𝕜] F) :
    N (∑ i ∈ s, A i) ≤ ∑ i ∈ s, N (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (N.add_le _ _).trans (add_le_add_right ih _)

/-- The two-sided unitary orbit of a rectangular map.

A point of `twoSidedUnitaryOrbit C` has the form `U ∘ C ∘ V` with unitary
left and right factors.  The phase of a complex Fourier coefficient is intended
to be absorbed into `U`, so the convex hull of this set is the correct
barycentric target for the arbitrary-spectrum `π/2` proof.

Proof strategy for later uses:

1. unfold membership to recover the two unitary factors;
2. use `RectangularUnitarilyInvariantNorm.invariant` to erase them in norm
   estimates;
3. use `mem_convexHull_iff_exists_fintype` to turn convex-hull membership into
   an exact finite convex combination.

The definition is field-uniform: over `ℝ`, the only scalar phases absorbed into
the orbit are the real unitary signs, while a complex proof must descend to a
real orbit before invoking this API. -/
def twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {Y | ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E),
    Y = U.toLinearMap ∘ₗ C ∘ₗ V.toLinearMap}

/-- A finite two-sided unitary-orbit certificate for bounding `X` by `C`.

A certificate of mass `mass` writes `X` as a finite linear combination of maps
`Uᵢ ∘ C ∘ Vᵢ`, where each `Uᵢ` and `Vᵢ` is unitary and the sum of coefficient
norms is at most `mass`.

Proof strategy for uses of this definition:

1. apply finite-sum subadditivity to the represented map;
2. use absolute homogeneity on each coefficient;
3. erase the two unitary factors by invariance;
4. bound the resulting coefficient sum by `mass`.

For the arbitrary-spectrum `π/2` theorem, the difficult analytic task is exactly
to construct such a certificate for `((δ : 𝕜) • X)` from the Sylvester defect
`C` with mass `π / 2`. -/
def HasFiniteUnitaryOrbitCertificate
    (mass : ℝ) (X C : E →ₗ[𝕜] F) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → 𝕜,
    ∃ U : Fin n → F ≃ₗᵢ[𝕜] F,
      ∃ V : Fin n → E ≃ₗᵢ[𝕜] E,
        X = ∑ i, a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap) ∧
        ∑ i, ‖a i‖ ≤ mass

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Reindex a finite certificate candidate from an arbitrary finite type by `Fin n`.

Proof strategy:

1. use `(Fintype.equivFin ι).symm` to enumerate the original finite type;
2. transport the exact operator sum with `Equiv.sum_comp`;
3. transport the coefficient-mass sum by the same equivalence;
4. package the reindexed data in `HasFiniteUnitaryOrbitCertificate`.

This lemma keeps all `Fin n` bookkeeping out of the convex-geometric proof.
It is purely finite algebra and has no analytic or field-specific content. -/
theorem hasFiniteUnitaryOrbitCertificate_of_fintype
    {ι : Type*} [Fintype ι] {mass : ℝ} {X C : E →ₗ[𝕜] F}
    (a : ι → 𝕜) (U : ι → F ≃ₗᵢ[𝕜] F) (V : ι → E ≃ₗᵢ[𝕜] E)
    (hX : X = ∑ i, a i •
      ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap))
    (hmass : ∑ i, ‖a i‖ ≤ mass) :
    HasFiniteUnitaryOrbitCertificate mass X C := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun j => a (e j), fun j => U (e j),
    fun j => V (e j), ?_, ?_⟩
  · calc
      X = ∑ i, a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap) := hX
      _ = ∑ j, a (e j) •
          ((U (e j)).toLinearMap ∘ₗ C ∘ₗ (V (e j)).toLinearMap) :=
        (e.sum_comp (fun i => a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap))).symm
  · calc
      ∑ j, ‖a (e j)‖ = ∑ i, ‖a i‖ :=
        e.sum_comp (fun i => ‖a i‖)
      _ ≤ mass := hmass

/-- Restrict scalars on the rectangular-map space from `𝕜` to `ℝ` for the
real convex-hull argument.

Proof strategy:

1. reuse the existing `𝕜`-module structure on `E →ₗ[𝕜] F`;
2. compose its scalar action with `algebraMap ℝ 𝕜` via `Module.compHom`;
3. keep the instance local so the convex-geometric API does not install a
   competing global scalar action on linear maps.

At the one boundary where real convex weights become `𝕜` coefficients,
unfold this exact `Module.compHom` action.  Since the `RCLike` coercion from
`ℝ` is the same algebra map, the bundled-map scalar equality is definitional;
no scalar-tower or codomain real-module instance is required. -/
local instance realModuleLinearMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Convert an exact convex-hull barycentric representation into a finite
unitary-orbit certificate.

Suppose `Y` lies in the real convex hull of the two-sided unitary orbit of `C`,
and `X = m • Y` for a nonnegative real mass `m ≤ mass`.  Then `X` has a finite
unitary-orbit certificate of mass `mass`.

Proof strategy:

1. apply `mem_convexHull_iff_exists_fintype` to write `Y` as an exact finite
   convex combination `Σ wᵢ zᵢ`, with `wᵢ ≥ 0` and `Σ wᵢ = 1`;
2. unfold `twoSidedUnitaryOrbit` and choose unitary factors for every `zᵢ`;
3. use coefficients `((m * wᵢ : ℝ) : 𝕜)` and distribute the scalar `m` across
   the finite sum;
4. unfold the file-local `Module.compHom` action to identify a real scalar
   on the bundled map with the corresponding coerced `𝕜` scalar definitionally;
5. compute the coefficient mass exactly as `m * Σ wᵢ = m`, then use
   `m ≤ mass`;
6. invoke `hasFiniteUnitaryOrbitCertificate_of_fintype` for the final `Fin n`
   reindexing.

This theorem discharges the entire exact finite-dimensional convex-combination
stage of the `π/2` proof.  The remaining analytic theorem only has to produce a
bounded-mass barycentric orbit representation.  The argument is valid over
both `ℝ` and `ℂ`; any complexification/descent issue must already have been
resolved before establishing the real convex-hull hypothesis. -/
theorem hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
    {m mass : ℝ} (hm : 0 ≤ m) (hmass : m ≤ mass)
    {X Y C : E →ₗ[𝕜] F}
    (hY : Y ∈ convexHull ℝ (twoSidedUnitaryOrbit C))
    (hX : X = ((m : 𝕜)) • Y) :
    HasFiniteUnitaryOrbitCertificate mass X C := by
  classical
  rcases (mem_convexHull_iff_exists_fintype.mp hY) with
    ⟨ι, instι, w, z, hw, hwsum, hz, hzsum⟩
  letI : Fintype ι := instι
  have hz' : ∀ i, ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E),
      z i = U.toLinearMap ∘ₗ C ∘ₗ V.toLinearMap := by
    intro i
    exact hz i
  choose U V hUV using hz'
  refine hasFiniteUnitaryOrbitCertificate_of_fintype
    (a := fun i => (((m * w i : ℝ) : 𝕜))) U V ?_ ?_
  · have real_smul_linearMap_eq (r : ℝ) (T : E →ₗ[𝕜] F) :
        r • T = ((r : 𝕜)) • T := by
      -- The local real module was defined by `Module.compHom` along
      -- `algebraMap ℝ 𝕜`, and the `RCLike` coercion is that algebra map.
      -- Hence the two bundled-map scalar actions are definitionally equal;
      -- no real module or scalar-tower instance on the codomain is needed.
      change (algebraMap ℝ 𝕜 r) • T = ((r : 𝕜)) • T
      rfl
    have hzsum' : ∑ i, (((w i : ℝ) : 𝕜)) • z i = Y := by
      calc
        ∑ i, (((w i : ℝ) : 𝕜)) • z i = ∑ i, w i • z i := by
          apply Finset.sum_congr rfl
          intro i _
          exact (real_smul_linearMap_eq (w i) (z i)).symm
        _ = Y := hzsum
    calc
      X = ((m : 𝕜)) • Y := hX
      _ = ((m : 𝕜)) • ∑ i, (((w i : ℝ) : 𝕜)) • z i := by rw [hzsum']
      _ = ∑ i, (((m * w i : ℝ) : 𝕜)) • z i := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, RCLike.ofReal_mul]
      _ = ∑ i, (((m * w i : ℝ) : 𝕜)) •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hUV i]
  · calc
      ∑ i, ‖(((m * w i : ℝ) : 𝕜))‖ = ∑ i, m * w i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [RCLike.norm_ofReal, abs_of_nonneg (mul_nonneg hm (hw i))]
      _ = m * ∑ i, w i := by rw [Finset.mul_sum]
      _ = m := by rw [hwsum, mul_one]
      _ ≤ mass := hmass

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem smul_eq (a : 𝕜) (A : E →ₗ[𝕜] F) : N (a • A) = ‖a‖ * N A :=
  N.smul' a A

/-- A rectangular UI seminorm is invariant under negation. -/
@[simp] theorem apply_neg (A : E →ₗ[𝕜] F) : N (-A) = N A := by
  have h := N.smul_eq (-1 : 𝕜) A
  simpa using h

/--
Lean proof route for a weaker agent:

1. For `add_le`, apply `N.add_le' A B` directly; for `smul_eq`, apply `N.smul' a A`; for `invariant`, apply `N.invariant' U V A`.
2. Use `change` to expose `N.toFun` if coercion prevents field application.
3. Close by `simpa` after normalizing the coercion from the structure to its function field.
-/
theorem invariant (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) :
    N (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) = N A :=
  N.invariant' U V A

/-- Every rectangular UI seminorm is bounded by the mass of a finite two-sided
unitary-orbit certificate.

Proof strategy:

1. destruct the certificate into coefficients and left/right unitary factors;
2. rewrite `X` by the certified finite sum;
3. invoke `sum_le`, then `smul_eq` and `invariant` term by term;
4. factor out `N C` and use its nonnegativity to apply the mass bound.

This theorem deliberately contains all norm-theoretic content needed by the
`π/2` front. The remaining hard theorem may therefore focus solely on
constructing the orbit certificate. -/
theorem apply_le_of_finiteUnitaryOrbitCertificate
    {mass : ℝ} {X C : E →ₗ[𝕜] F}
    (hcert : HasFiniteUnitaryOrbitCertificate mass X C) :
    N X ≤ mass * N C := by
  classical
  rcases hcert with ⟨n, a, U, V, hX, hmass⟩
  rw [hX]
  calc
    N (∑ i, a i •
        ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap)) ≤
        ∑ i, N (a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap)) :=
      N.sum_le (Finset.univ : Finset (Fin n))
        (fun i => a i •
          ((U i).toLinearMap ∘ₗ C ∘ₗ (V i).toLinearMap))
    _ = ∑ i, ‖a i‖ * N C := by
      apply Finset.sum_congr rfl
      intro i _
      rw [N.smul_eq, N.invariant (U i) (V i) C]
    _ = (∑ i, ‖a i‖) * N C := by
      rw [Finset.sum_mul]
    _ ≤ mass * N C :=
      mul_le_mul_of_nonneg_right hmass (N.nonneg C)


/-- Equal singular-value data determines a rectangular map up to left and right
unitary factors.  The right unitary aligns the two Gram eigenbases; Gram
rigidity then supplies the left unitary. -/
private theorem exists_unitary_factorization_of_singularValues_eq
    {A B : E →ₗ[𝕜] F} (hσ : A.singularValues = B.singularValues) :
    ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E),
      A = U.toLinearMap ∘ₗ B ∘ₗ V.toLinearMap := by
  let hA := A.isSymmetric_adjoint_comp_self
  let hB := B.isSymmetric_adjoint_comp_self
  let bA := hA.eigenvectorBasis rfl
  let bB := hB.eigenvectorBasis rfl
  let K := bB.equiv bA (Equiv.refl _)
  have hKb : ∀ i, K (bB i) = bA i := fun i => by
    simp [K, bA, bB]
  have hKsymm : ∀ i, K.symm (bA i) = bB i := fun i => by
    rw [← hKb i, LinearIsometryEquiv.symm_apply_apply]
  have heig : hA.eigenvalues rfl = hB.eigenvalues rfl := by
    funext i
    rw [← A.sq_singularValues_fin rfl i,
      ← B.sq_singularValues_fin rfl i, hσ]
  have hgram_conj : A.adjoint ∘ₗ A =
      K.toLinearMap ∘ₗ (B.adjoint ∘ₗ B) ∘ₗ K.symm.toLinearMap := by
    refine bA.toBasis.ext fun i => ?_
    change (A.adjoint ∘ₗ A) (bA i) =
      K ((B.adjoint ∘ₗ B) (K.symm (bA i)))
    rw [hKsymm i]
    change (A.adjoint ∘ₗ A) (hA.eigenvectorBasis rfl i) =
      K ((B.adjoint ∘ₗ B) (hB.eigenvectorBasis rfl i))
    rw [hA.apply_eigenvectorBasis rfl i,
      hB.apply_eigenvectorBasis rfl i, map_smul, hKb i,
      congrFun heig i]
  have hgram : B.adjoint ∘ₗ B =
      (A ∘ₗ K.toLinearMap).adjoint ∘ₗ (A ∘ₗ K.toLinearMap) := by
    ext x
    have hx := congrArg K.symm (LinearMap.congr_fun hgram_conj (K x))
    simpa only [LinearMap.adjoint_comp, K.adjoint_toLinearMap_eq_symm,
      LinearMap.comp_apply,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply] using hx.symm
  have hinner : ∀ x y,
      ⟪B x, B y⟫_𝕜 = ⟪(A ∘ₗ K.toLinearMap) x, (A ∘ₗ K.toLinearMap) y⟫_𝕜 := by
    intro x y
    calc
      ⟪B x, B y⟫_𝕜 = ⟪(B.adjoint ∘ₗ B) x, y⟫_𝕜 := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
      _ = ⟪((A ∘ₗ K.toLinearMap).adjoint ∘ₗ
          (A ∘ₗ K.toLinearMap)) x, y⟫_𝕜 := by rw [hgram]
      _ = ⟪(A ∘ₗ K.toLinearMap) x, (A ∘ₗ K.toLinearMap) y⟫_𝕜 := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  obtain ⟨U, hU⟩ := exists_linearIsometryEquiv_map_eq_of_inner_eq
    (φ := fun x : E => B x)
    (ψ := fun x : E => (A ∘ₗ K.toLinearMap) x) hinner
  refine ⟨U, K.symm, ?_⟩
  ext x
  simpa only [LinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply] using (hU (K.symm x)).symm

/-- A rectangular unitarily invariant norm depends only on the complete
singular-value sequence. -/
theorem apply_eq_of_singularValues_eq {A B : E →ₗ[𝕜] F}
    (hσ : A.singularValues = B.singularValues) : N A = N B := by
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hσ
  rw [hfac]
  exact N.invariant U V B

/-- Pull a rectangular UI norm back along an isometric embedding of the
codomain.  The transported norm measures `A : E → H` by measuring
`ι ∘ A : E → F`. -/
noncomputable def codomainIsometryTransport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) :
    RectangularUnitarilyInvariantNorm 𝕜 E H where
  toFun A := N (ι.toLinearMap ∘ₗ A)
  add_le' A B := by
    have hmap : ι.toLinearMap ∘ₗ (A + B) =
        (ι.toLinearMap ∘ₗ A) + (ι.toLinearMap ∘ₗ B) := by
      ext x
      simp
    rw [hmap]
    exact N.add_le _ _
  smul' a A := by
    have hmap : ι.toLinearMap ∘ₗ (a • A) =
        a • (ι.toLinearMap ∘ₗ A) := by
      ext x
      simp
    rw [hmap]
    exact N.smul_eq _ _
  invariant' U V A := by
    apply N.apply_eq_of_singularValues_eq
    calc
      (ι.toLinearMap ∘ₗ (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)).singularValues =
          (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues :=
        singularValues_linearIsometry_comp ι _
      _ = A.singularValues := by
        rw [singularValues_unitary_comp, singularValues_comp_unitary]
      _ = (ι.toLinearMap ∘ₗ A).singularValues :=
        (singularValues_linearIsometry_comp ι A).symm

@[simp] theorem codomainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] H) :
    N.codomainIsometryTransport ι A = N (ι.toLinearMap ∘ₗ A) :=
  rfl

/-- Pull a rectangular UI norm back along the adjoint of an isometric
embedding of the domain.  The transported norm measures `A : H → F` by the
zero-padded map `A ∘ ι⋆ : E → F`. -/
noncomputable def domainIsometryTransport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] E) :
    RectangularUnitarilyInvariantNorm 𝕜 H F where
  toFun A := N (A ∘ₗ LinearMap.adjoint ι.toLinearMap)
  add_le' A B := by
    have hmap : (A + B) ∘ₗ LinearMap.adjoint ι.toLinearMap =
        (A ∘ₗ LinearMap.adjoint ι.toLinearMap) +
          (B ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
      ext x
      simp
    rw [hmap]
    exact N.add_le _ _
  smul' a A := by
    have hmap : (a • A) ∘ₗ LinearMap.adjoint ι.toLinearMap =
        a • (A ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
      ext x
      simp
    rw [hmap]
    exact N.smul_eq _ _
  invariant' U V A := by
    apply N.apply_eq_of_singularValues_eq
    calc
      ((U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap) ∘ₗ
          LinearMap.adjoint ι.toLinearMap).singularValues =
          (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap).singularValues :=
        singularValues_comp_adjoint_linearIsometry ι _
      _ = A.singularValues := by
        rw [singularValues_unitary_comp, singularValues_comp_unitary]
      _ = (A ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues :=
        (singularValues_comp_adjoint_linearIsometry ι A).symm

@[simp] theorem domainIsometryTransport_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ι : H →ₗᵢ[𝕜] E) (A : H →ₗ[𝕜] F) :
    N.domainIsometryTransport ι A =
      N (A ∘ₗ LinearMap.adjoint ι.toLinearMap) :=
  rfl

/-- Extend a unitary action on an isometrically embedded coordinate space to
an ambient unitary. -/
private theorem exists_ambient_unitary_intertwining
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K]
    (ι : H →ₗᵢ[𝕜] K) (U : H ≃ₗᵢ[𝕜] H) :
    ∃ W : K ≃ₗᵢ[𝕜] K,
      W.toLinearMap ∘ₗ ι.toLinearMap =
        ι.toLinearMap ∘ₗ U.toLinearMap := by
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_map_eq_of_inner_eq
    (φ := fun x : H => ι x) (ψ := fun x : H => ι (U x)) (by
      intro x y
      rw [ι.inner_map_map, ι.inner_map_map, U.inner_map_map])
  refine ⟨W, ?_⟩
  ext x
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] using hW x

/-- Lift an endomorphism of a common coordinate space to a rectangular map by
an isometric codomain embedding and a coisometric domain projection. -/
private noncomputable def coordinateLift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (X : H →ₗ[𝕜] H) : E →ₗ[𝕜] F :=
  ιF.toLinearMap ∘ₗ X ∘ₗ LinearMap.adjoint ιE.toLinearMap

private theorem singularValues_coordinateLift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (X : H →ₗ[𝕜] H) :
    (coordinateLift ιE ιF X).singularValues = X.singularValues := by
  unfold coordinateLift
  calc
    (ιF.toLinearMap ∘ₗ X ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues =
        (X ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues :=
      singularValues_linearIsometry_comp ιF _
    _ = X.singularValues :=
      singularValues_comp_adjoint_linearIsometry ιE X

/-- Pull a rectangular UI norm back to square operators on a common coordinate
space.  Ambient extensions of the coordinate unitaries prove full square
unitary invariance. -/
private noncomputable def coordinateSquareNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F) :
    UnitarilyInvariantNorm 𝕜 H where
  toFun X := N (coordinateLift ιE ιF X)
  add_le' X Y := by
    have hmap : coordinateLift ιE ιF (X + Y) =
        coordinateLift ιE ιF X + coordinateLift ιE ιF Y := by
      ext x
      simp [coordinateLift, LinearMap.comp_apply]
    rw [hmap]
    exact N.add_le _ _
  smul' a X := by
    have hmap : coordinateLift ιE ιF (a • X) =
        a • coordinateLift ιE ιF X := by
      ext x
      simp [coordinateLift, LinearMap.comp_apply]
    rw [hmap]
    exact N.smul_eq a _
  invariant' U V X := by
    obtain ⟨UF, hUF⟩ := exists_ambient_unitary_intertwining ιF U
    obtain ⟨WE, hWE⟩ := exists_ambient_unitary_intertwining ιE V.symm
    have hadj : LinearMap.adjoint ιE.toLinearMap ∘ₗ WE.symm.toLinearMap =
        V.toLinearMap ∘ₗ LinearMap.adjoint ιE.toLinearMap := by
      have h := congrArg LinearMap.adjoint hWE
      simpa only [LinearMap.adjoint_comp,
        WE.adjoint_toLinearMap_eq_symm,
        (V.symm).adjoint_toLinearMap_eq_symm,
        LinearIsometryEquiv.symm_symm] using h
    have hlift : coordinateLift ιE ιF
          (U.toLinearMap ∘ₗ X ∘ₗ V.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF X ∘ₗ
          WE.symm.toLinearMap := by
      ext z
      simp only [coordinateLift, LinearMap.comp_apply]
      calc
        ιF (U (X (V (LinearMap.adjoint ιE.toLinearMap z)))) =
            UF (ιF (X (V (LinearMap.adjoint ιE.toLinearMap z)))) :=
          (LinearMap.congr_fun hUF _).symm
        _ = UF (ιF (X (LinearMap.adjoint ιE.toLinearMap (WE.symm z)))) := by
          have hz := LinearMap.congr_fun hadj z
          simp only [LinearMap.comp_apply,
            LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hz
          exact congrArg (fun q => UF (ιF (X q))) hz.symm
    rw [hlift]
    exact N.invariant UF WE.symm _

/-- The initial coordinate embedding determined by the first `d` vectors of
the standard orthonormal basis. -/
private noncomputable def initialCoordinateIsometry
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K]
    {d : ℕ} (hd : d ≤ finrank 𝕜 K) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] K :=
  familyIsometry ((stdOrthonormalBasis 𝕜 K).orthonormal.comp
    (fun i => Fin.castLE hd i) (Fin.castLE_injective hd))

/-- The square diagonal operator carrying the nonzero rectangular singular
coordinates. -/
private noncomputable def singularValueDiagonal (d : ℕ)
    (A : E →ₗ[𝕜] F) :
    EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
    (fun i => A.singularValues (i : ℕ))

private theorem singularValues_singularValueDiagonal
    {d : ℕ} (A : E →ₗ[𝕜] F) (hrank : finrank 𝕜 A.range ≤ d) :
    (singularValueDiagonal d A).singularValues = A.singularValues := by
  have hanti : Antitone (fun i : Fin d => A.singularValues (i : ℕ)) :=
    fun i j hij => A.singularValues_antitone (Fin.le_def.mp hij)
  have hnonneg : ∀ i : Fin d, 0 ≤ A.singularValues (i : ℕ) :=
    fun i => A.singularValues_nonneg _
  apply Finsupp.ext
  intro i
  rcases lt_or_ge i d with hi | hi
  · simpa [singularValueDiagonal] using
      singularValues_diagOp (𝕜 := 𝕜) finrank_euclideanSpace_fin
        (EuclideanSpace.basisFun (Fin d) 𝕜) hanti hnonneg ⟨i, hi⟩
  · have hcoord : finrank 𝕜 (EuclideanSpace 𝕜 (Fin d)) ≤ i := by
      simpa only [finrank_euclideanSpace_fin] using hi
    rw [(singularValueDiagonal d A).singularValues_of_finrank_le hcoord,
      A.singularValues_eq_zero_iff_le_finrank_range.mpr (hrank.trans hi)]

private theorem apply_eq_coordinateSquareNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (A : E →ₗ[𝕜] F) (X : H →ₗ[𝕜] H)
    (hσ : X.singularValues = A.singularValues) :
    N A = coordinateSquareNorm N ιE ιF X := by
  have hliftσ : (coordinateLift ιE ιF X).singularValues = A.singularValues :=
    (singularValues_coordinateLift ιE ιF X).trans hσ
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hliftσ.symm
  change N A = N (coordinateLift ιE ιF X)
  rw [hfac]
  exact N.invariant U V _


/-- A real-linear two-sided unitary action on rectangular maps. -/
private noncomputable def twoSidedActionLinear
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[ℝ] (E →ₗ[𝕜] F) where
  toFun A := U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap
  map_add' A B := by
    ext x
    simp [LinearMap.comp_apply]
  map_smul' r A := by
    ext x
    change U (((r : 𝕜) • A) (V x)) = ((r : 𝕜) •
      (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)) x
    simp [LinearMap.comp_apply]

/-- The real convex hull of a two-sided unitary orbit is invariant under any
further two-sided unitary action. -/
private theorem twoSidedAction_mem_convexHull
    {E₀ F₀ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    {A C : E₀ →ₗ[𝕜] F₀}
    (hA : A ∈ convexHull ℝ (twoSidedUnitaryOrbit C))
    (U : F₀ ≃ₗᵢ[𝕜] F₀) (V : E₀ ≃ₗᵢ[𝕜] E₀) :
    U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap ∈
      convexHull ℝ (twoSidedUnitaryOrbit C) := by
  let L := twoSidedActionLinear (𝕜 := 𝕜) U V
  have hmem : L A ∈ L '' convexHull ℝ (twoSidedUnitaryOrbit C) :=
    ⟨A, hA, rfl⟩
  rw [L.image_convexHull] at hmem
  apply convexHull_mono (𝕜 := ℝ) ?_ hmem
  rintro Y ⟨Y0, ⟨U0, V0, rfl⟩, rfl⟩
  refine ⟨U0.trans U, V.trans V0, ?_⟩
  ext x
  rfl

/-- Abstract T-transform descent with values in a convex set invariant under
coordinate transpositions and one-coordinate sign changes.

This is the membership-valued analogue of
`UnitarilyInvariantNorm.gauge_le_gauge_of_prefix_sums_le`.  It is formulated
once here so the rectangular orbit theorem can use the same finite descent
without invoking separation theorems or an external majorization library. -/
private theorem mem_convex_of_prefix_sums_le
    {n : ℕ} {K : Set (Fin n → ℝ)} (hK : Convex ℝ K)
    (hswap : ∀ y ∈ K, ∀ j l : Fin n, y ∘ Equiv.swap j l ∈ K)
    (hneg : ∀ y ∈ K, ∀ j : Fin n,
      Function.update y j (-(y j)) ∈ K)
    {z y : Fin n → ℝ} (hzanti : Antitone z)
    (hz0 : ∀ i, 0 ≤ z i) (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), z i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), y i)
    (hyK : y ∈ K) : z ∈ K := by
  classical
  have update_mem : ∀ (q : Fin n → ℝ), q ∈ K → ∀ (j : Fin n) (t : ℝ),
      |t| ≤ q j → Function.update q j t ∈ K := by
    intro q hq j t ht
    have hqj : 0 ≤ q j := le_trans (abs_nonneg t) ht
    rcases hqj.eq_or_lt with hzero | hpos
    · have ht0 : t = 0 := by
        have : |t| ≤ 0 := by simpa [hzero] using ht
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg t))
      have hupd : Function.update q j t = q := by
        funext i
        rcases eq_or_ne i j with rfl | hij
        · rw [Function.update_self, ht0, ← hzero]
        · rw [Function.update_of_ne hij]
      simpa [hupd] using hq
    · let c1 : ℝ := (q j + t) / (2 * q j)
      let c2 : ℝ := (q j - t) / (2 * q j)
      obtain ⟨ht1, ht2⟩ := abs_le.mp ht
      have hden : 0 < 2 * q j := by linarith
      have hc1 : 0 ≤ c1 := div_nonneg (by linarith) hden.le
      have hc2 : 0 ≤ c2 := div_nonneg (by linarith) hden.le
      have hsum : c1 + c2 = 1 := by
        dsimp [c1, c2]
        field_simp
        ring
      have hdecomp : Function.update q j t =
          c1 • q + c2 • Function.update q j (-(q j)) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases eq_or_ne i j with rfl | hij
        · rw [Function.update_self, Function.update_self]
          dsimp [c1, c2]
          field_simp
          ring
        · rw [Function.update_of_ne hij, Function.update_of_ne hij,
            ← add_mul, hsum, one_mul]
      rw [hdecomp]
      exact hK hq (hneg q hq j) hc1 hc2 hsum
  have mono_mem : ∀ d (q : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      q ∈ K → (∀ i, z i ≤ q i) → z ∈ K := by
    intro d
    induction d with
    | zero =>
        intro q hcard hq _
        have hemp : (Finset.univ.filter fun i => z i ≠ q i) = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
        have hzq : z = q := funext fun i => by
          by_contra hne
          have hi : i ∈ Finset.univ.filter fun i => z i ≠ q i :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hemp] at hi
          simp at hi
        simpa [hzq] using hq
    | succ d ih =>
        intro q hcard hq hzq
        by_cases heq : z = q
        · simpa [heq] using hq
        · have hne : (Finset.univ.filter fun i => z i ≠ q i).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            apply heq
            funext i
            by_contra hneq
            have hi : i ∈ Finset.univ.filter fun i => z i ≠ q i :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
            rw [hemp] at hi
            simp at hi
          obtain ⟨j, hj⟩ := hne
          let q' := Function.update q j (z j)
          have hq'K : q' ∈ K := by
            apply update_mem q hq j (z j)
            rw [abs_of_nonneg (hz0 j)]
            exact hzq j
          have hzq' : ∀ i, z i ≤ q' i := by
            intro i
            rcases eq_or_ne i j with rfl | hij
            · simp [q']
            · simp [q', hij, hzq i]
          have hsub : (Finset.univ.filter fun i => z i ≠ q' i) ⊆
              (Finset.univ.filter fun i => z i ≠ q i).erase j := by
            intro i hi
            obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
            have hij : i ≠ j := by
              rintro rfl
              exact hine (by simp [q'])
            refine Finset.mem_erase.mpr ⟨hij,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
            simpa [q', hij] using hine
          have hcard' : (Finset.univ.filter fun i => z i ≠ q' i).card ≤ d := by
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_erase_of_mem hj
            omega
          exact ih q' hcard' hq'K hzq'
  have H : ∀ d (q : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      (∀ i, 0 ≤ q i) →
      (∀ m : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), z i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), q i) →
      q ∈ K → z ∈ K := by
    intro d
    induction d with
    | zero =>
        intro q hcard _ _ hq
        exact mono_mem 0 q hcard hq (fun i => by
          have := hpre ((i : ℕ) + 1)
          -- The zero-disagreement case already gives equality directly.
          have hemp : (Finset.univ.filter fun k => z k ≠ q k) = ∅ :=
            Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
          by_contra hnot
          have hi : i ∈ Finset.univ.filter fun k => z k ≠ q k :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_gt (lt_of_not_ge hnot)⟩
          rw [hemp] at hi
          simp at hi)
    | succ d ih =>
        intro q hcard hq0 hqpre hqK
        by_cases hall : ∀ i, z i ≤ q i
        · exact mono_mem (d + 1) q hcard hqK hall
        push Not at hall
        have hSne : (Finset.univ.filter fun i : Fin n => q i < z i).Nonempty :=
          hall.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        let l := (Finset.univ.filter fun i : Fin n => q i < z i).min' hSne
        have hlS : q l < z l :=
          (Finset.mem_filter.mp
            ((Finset.univ.filter fun i : Fin n => q i < z i).min'_mem hSne)).2
        have hlmin : ∀ i, i < l → z i ≤ q i := by
          intro i hil
          by_contra hzy
          push Not at hzy
          exact absurd
            (Finset.min'_le _ i (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hzy⟩)) (not_le.mpr hil)
        have hexj : ∃ j, j < l ∧ z j < q j := by
          by_contra h
          push Not at h
          have heq : ∀ i, i < l → z i = q i := fun i hi =>
            le_antisymm (hlmin i hi) (h i hi)
          have hp := hqpre ((l : ℕ) + 1)
          have hset : (Finset.univ.filter fun i : Fin n =>
              (i : ℕ) < (l : ℕ) + 1) =
              insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert]
            constructor
            · intro hi
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
              · exact Or.inl (Fin.ext heq')
              · exact Or.inr hlt
            · rintro (rfl | hi)
              · omega
              · omega
          have hlnot : l ∉ Finset.univ.filter
              (fun i : Fin n => (i : ℕ) < (l : ℕ)) := by simp
          rw [hset, Finset.sum_insert hlnot, Finset.sum_insert hlnot] at hp
          have hsum_eq :
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (l : ℕ)), z i =
                ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (l : ℕ)), q i := by
            refine Finset.sum_congr rfl fun i hi => heq i ?_
            exact Fin.lt_def.mpr (Finset.mem_filter.mp hi).2
          rw [hsum_eq] at hp
          linarith
        obtain ⟨j, hjl, hzj⟩ := hexj
        have hjl_ne : j ≠ l := ne_of_lt hjl
        let delta : ℝ := min (q j - z j) (z l - q l)
        have hdeltaPos : 0 < delta := lt_min (by linarith) (by linarith)
        have hdelta1 : delta ≤ q j - z j := min_le_left _ _
        have hdelta2 : delta ≤ z l - q l := min_le_right _ _
        have hdeltaLt : delta < q j - q l :=
          lt_of_le_of_lt hdelta1 (by linarith [hzanti hjl.le])
        have hqjl : 0 < q j - q l := by linarith
        let c : ℝ := delta / (q j - q l)
        have hcpos : 0 < c := div_pos hdeltaPos hqjl
        have hclt : c < 1 := (div_lt_one hqjl).mpr hdeltaLt
        have hcmul : c * (q j - q l) = delta :=
          div_mul_cancel₀ delta (ne_of_gt hqjl)
        let q' : Fin n → ℝ :=
          Function.update (Function.update q j (q j - delta)) l (q l + delta)
        have hq'j : q' j = q j - delta := by
          simp [q', Function.update_of_ne hjl_ne]
        have hq'l : q' l = q l + delta := by simp [q']
        have hq'i : ∀ i, i ≠ j → i ≠ l → q' i = q i := by
          intro i hij hil
          simp [q', hij, hil]
        have hcomb : q' = (1 - c) • q + c • (q ∘ Equiv.swap j l) := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Function.comp_apply]
          rcases eq_or_ne i j with rfl | hij
          · rw [hq'j, Equiv.swap_apply_left]
            linear_combination hcmul
          rcases eq_or_ne i l with rfl | hil
          · rw [hq'l, Equiv.swap_apply_right]
            linear_combination -hcmul
          · rw [hq'i i hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
            ring
        have hq'0 : ∀ i, 0 ≤ q' i := by
          intro i
          rcases eq_or_ne i j with heq | hij
          · rw [heq, hq'j]
            linarith [hz0 j]
          rcases eq_or_ne i l with heq | hil
          · rw [heq, hq'l]
            linarith [hq0 l]
          · rw [hq'i i hij hil]
            exact hq0 i
        have hq'pre : ∀ m : ℕ,
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), z i ≤
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), q' i := by
          intro m
          rcases le_or_gt m (j : ℕ) with hmj | hmj
          · have hcong : ∀ i ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m), q' i = q i := by
              intro i hi
              have hivm := (Finset.mem_filter.mp hi).2
              have hij : i ≠ j := fun h => by subst h; omega
              have hil : i ≠ l := fun h => by subst h; omega
              exact hq'i i hij hil
            rw [Finset.sum_congr rfl hcong]
            exact hqpre m
          rcases le_or_gt m (l : ℕ) with hml | hml
          · have hcong : ∀ i ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m),
                q' i = Function.update q j (q j - delta) i := by
              intro i hi
              have hivm := (Finset.mem_filter.mp hi).2
              have hil : i ≠ l := fun h => by subst h; omega
              simp [q', hil]
            have hjmem : j ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmj⟩
            rw [Finset.sum_congr rfl hcong,
              Finset.sum_update_of_mem hjmem]
            have hqsplit : ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), q i =
                q j + ∑ i ∈ (Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m)) \ {j}, q i := by
              rw [← Finset.erase_eq]
              exact (Finset.add_sum_erase _ q hjmem).symm
            have hterm : q j - z j ≤
                ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), (q i - z i) := by
              refine Finset.single_le_sum (f := fun i => q i - z i) ?_ hjmem
              intro i hi
              have hivm := (Finset.mem_filter.mp hi).2
              have hil : i < l := Fin.lt_def.mpr (by omega)
              linarith [hlmin i hil]
            rw [Finset.sum_sub_distrib] at hterm
            linarith [hqpre m, hdelta1]
          · have hjmem : j ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            have hlmem : l ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hml⟩
            have hjmem' : j ∈ (Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m)) \ {l} :=
              Finset.mem_sdiff.mpr ⟨hjmem, by simp [hjl_ne]⟩
            have heqsum : ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), q' i =
                ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), q i := by
              have h1 : ∑ i ∈ Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m), q' i =
                  (q l + delta) + ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l},
                    Function.update q j (q j - delta) i := by
                unfold q'
                exact Finset.sum_update_of_mem hlmem _ _
              have h2 : ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l},
                    Function.update q j (q j - delta) i =
                  (q j - delta) + ∑ i ∈ ((Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}) \ {j}, q i :=
                Finset.sum_update_of_mem hjmem' _ _
              have h3 : ∑ i ∈ Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m), q i =
                  q l + ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}, q i := by
                rw [← Finset.erase_eq]
                exact (Finset.add_sum_erase _ q hlmem).symm
              have h4 : ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}, q i =
                  q j + ∑ i ∈ ((Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}) \ {j}, q i := by
                rw [← Finset.erase_eq, ← Finset.erase_eq]
                exact (Finset.add_sum_erase _ q (by rwa [Finset.erase_eq])).symm
              rw [h1, h2, h3, h4]
              ring
            rw [heqsum]
            exact hqpre m
        have hsub : (Finset.univ.filter fun i => z i ≠ q' i) ⊆
            Finset.univ.filter fun i => z i ≠ q i := by
          intro i hi
          obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
          have hij : i ≠ j := by
            rintro rfl
            exact absurd heq hzj.ne
          have hil : i ≠ l := by
            rintro rfl
            exact absurd heq hlS.ne'
          exact hine (by rw [hq'i i hij hil]; exact heq)
        have hwitness : ∃ w ∈ Finset.univ.filter (fun i => z i ≠ q i),
            w ∉ Finset.univ.filter (fun i => z i ≠ q' i) := by
          rcases min_choice (q j - z j) (z l - q l) with hmin | hmin
          · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
            have hj' : q' j = z j := by
              rw [hq'j]
              dsimp [delta]
              rw [hmin]
              ring
            simp [hj']
          · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
            have hl' : q' l = z l := by
              rw [hq'l]
              dsimp [delta]
              rw [hmin]
              ring
            simp [hl']
        have hcard' : (Finset.univ.filter fun i => z i ≠ q' i).card ≤ d := by
          have hlt := Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset hsub).mpr hwitness)
          omega
        have hq'K : q' ∈ K := by
          rw [hcomb]
          exact hK hqK (hswap q hqK j l) (by linarith) hcpos.le (by linarith)
        exact ih q' hcard' hq'0 hq'pre hq'K
  exact H _ y le_rfl hy0 hpre hyK

/-- Lift a square coordinate operator to a rectangular map after arbitrary
left and right coordinate unitaries, extending those unitaries to the ambient
spaces. -/
private theorem coordinateLift_unitary_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (U V : H ≃ₗᵢ[𝕜] H) (X : H →ₗ[𝕜] H) :
    ∃ (UF : F ≃ₗᵢ[𝕜] F) (VE : E ≃ₗᵢ[𝕜] E),
      coordinateLift ιE ιF
          (U.toLinearMap ∘ₗ X ∘ₗ V.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF X ∘ₗ VE.toLinearMap := by
  obtain ⟨UF, hUF⟩ := exists_ambient_unitary_intertwining ιF U
  obtain ⟨WE, hWE⟩ := exists_ambient_unitary_intertwining ιE V.symm
  have hadj : LinearMap.adjoint ιE.toLinearMap ∘ₗ WE.symm.toLinearMap =
      V.toLinearMap ∘ₗ LinearMap.adjoint ιE.toLinearMap := by
    have h := congrArg LinearMap.adjoint hWE
    simpa only [LinearMap.adjoint_comp, WE.adjoint_toLinearMap_eq_symm,
      (V.symm).adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.symm_symm] using h
  refine ⟨UF, WE.symm, ?_⟩
  ext z
  simp only [coordinateLift, LinearMap.comp_apply]
  calc
    ιF (U (X (V (LinearMap.adjoint ιE.toLinearMap z)))) =
        UF (ιF (X (V (LinearMap.adjoint ιE.toLinearMap z)))) :=
      (LinearMap.congr_fun hUF _).symm
    _ = UF (ιF (X (LinearMap.adjoint ιE.toLinearMap (WE.symm z)))) := by
      have hz := LinearMap.congr_fun hadj z
      simp only [LinearMap.comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hz
      exact congrArg (fun q => UF (ιF (X q))) hz.symm

/-- Real-linear map from a singular-value coordinate vector to its rectangular
diagonal lift. -/
private noncomputable def coordinateDiagonalLift
    {d : ℕ}
    (ιE : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E)
    (ιF : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] F) :
    (Fin d → ℝ) →ₗ[ℝ] (E →ₗ[𝕜] F) where
  toFun x := coordinateLift ιE ιF
    (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)
  map_add' x y := by
    ext z
    simp [coordinateLift, diagOp_add, LinearMap.comp_apply]
  map_smul' r x := by
    ext z
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) (r • x)) z =
      ((r : 𝕜) • coordinateLift ιE ιF
        (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)) z
    rw [diagOp_real_smul]
    simp only [coordinateLift, LinearMap.comp_apply, LinearMap.smul_apply]
    exact ιF.toLinearMap.map_smul (r : 𝕜)
      ((diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)
        (LinearMap.adjoint ιE.toLinearMap z))

/-- Weak singular-value majorization is exactly the finite-dimensional
convex-hull order generated by the two-sided unitary orbit.

The proof applies the abstract T-transform descent to the preimage of the orbit
convex hull under a rectangular diagonal lift.  Coordinate swaps and sign
changes become two-sided unitary actions, while equal singular-value data is
transported by the rectangular SVD factorization already proved above. -/
theorem mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
    {A B : E →ₗ[𝕜] F}
    (h : ∀ k, rectangularKyFanSum k A ≤ rectangularKyFanSum k B) :
    A ∈ convexHull ℝ (twoSidedUnitaryOrbit B) := by
  classical
  let d : ℕ := min (finrank 𝕜 E) (finrank 𝕜 F)
  have hdE : d ≤ finrank 𝕜 E := by
    dsimp [d]
    exact min_le_left _ _
  have hdF : d ≤ finrank 𝕜 F := by
    dsimp [d]
    exact min_le_right _ _
  let ιE := initialCoordinateIsometry (𝕜 := 𝕜) (K := E) hdE
  let ιF := initialCoordinateIsometry (𝕜 := 𝕜) (K := F) hdF
  let L := coordinateDiagonalLift (𝕜 := 𝕜) ιE ιF
  let z : Fin d → ℝ := fun i => A.singularValues (i : ℕ)
  let y : Fin d → ℝ := fun i => B.singularValues (i : ℕ)
  let K : Set (Fin d → ℝ) :=
    L ⁻¹' convexHull ℝ (twoSidedUnitaryOrbit B)
  have hKconv : Convex ℝ K :=
    (convex_convexHull ℝ (twoSidedUnitaryOrbit B)).linear_preimage L
  have hswap : ∀ q ∈ K, ∀ j l : Fin d,
      q ∘ Equiv.swap j l ∈ K := by
    intro q hq j l
    let P : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜]
        EuclideanSpace 𝕜 (Fin d) :=
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.swap j l)
    have hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (q ∘ Equiv.swap j l) =
        P.symm.toLinearMap ∘ₗ
          diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ
            P.toLinearMap := by
      let b := EuclideanSpace.basisFun (Fin d) 𝕜
      refine b.toBasis.ext fun i => ?_
      simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
      rw [diagOp_apply_basis]
      have hPi : P (b i) = b (Equiv.swap j l i) := by
        simp [P, b]
      change ((q (Equiv.swap j l i) : ℝ) : 𝕜) • b i =
        P.symm (diagOp b q (P (b i)))
      rw [hPi, diagOp_apply_basis, map_smul]
      have hPsymm : P.symm (b (Equiv.swap j l i)) = b i := by
        rw [← hPi, LinearIsometryEquiv.symm_apply_apply]
      rw [hPsymm]
    obtain ⟨UF, VE, hfac⟩ := coordinateLift_unitary_factorization
      ιE ιF P.symm P
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q)
    change L (q ∘ Equiv.swap j l) ∈
      convexHull ℝ (twoSidedUnitaryOrbit B)
    change L q ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hq
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
        (q ∘ Equiv.swap j l)) ∈ _
    rw [hdiag, hfac]
    exact twoSidedAction_mem_convexHull hq UF VE
  have hneg : ∀ q ∈ K, ∀ j : Fin d,
      Function.update q j (-(q j)) ∈ K := by
    intro q hq j
    let R := ((𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ).reflection
    have hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (Function.update q j (-(q j))) =
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap := by
      refine (EuclideanSpace.basisFun (Fin d) 𝕜).toBasis.ext fun i => ?_
      simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
      rcases eq_or_ne i j with rfl | hij
      · rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
          map_neg, diagOp_apply_basis, diagOp_apply_basis,
          Function.update_self, RCLike.ofReal_neg, neg_smul]
      · have hmem : (EuclideanSpace.basisFun (Fin d) 𝕜) i ∈
            (𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
            ((EuclideanSpace.basisFun (Fin d) 𝕜).orthonormal.2 (Ne.symm hij))
        rw [Submodule.reflection_mem_subspace_eq_self hmem,
          diagOp_apply_basis, diagOp_apply_basis, Function.update_of_ne hij]
    obtain ⟨UF, VE, hfac0⟩ := coordinateLift_unitary_factorization
      ιE ιF (LinearIsometryEquiv.refl 𝕜 _) R
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q)
    have hid : (LinearIsometryEquiv.refl 𝕜
          (EuclideanSpace 𝕜 (Fin d))).toLinearMap ∘ₗ
          diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap =
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap := by
      ext x
      rfl
    rw [hid] at hfac0
    have hfac : coordinateLift ιE ιF
          (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF
          (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q) ∘ₗ VE.toLinearMap :=
      hfac0
    change L (Function.update q j (-(q j))) ∈
      convexHull ℝ (twoSidedUnitaryOrbit B)
    change L q ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hq
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
        (Function.update q j (-(q j)))) ∈ _
    rw [hdiag, hfac]
    exact twoSidedAction_mem_convexHull hq UF VE
  have hrankA : finrank 𝕜 A.range ≤ d := by
    apply le_min
    · have hnull := A.finrank_range_add_finrank_ker
      omega
    · exact Submodule.finrank_le _
  have hrankB : finrank 𝕜 B.range ≤ d := by
    apply le_min
    · have hnull := B.finrank_range_add_finrank_ker
      omega
    · exact Submodule.finrank_le _
  have hLy : L y ∈ twoSidedUnitaryOrbit B := by
    have hsigma : (L y).singularValues = B.singularValues := by
      change (coordinateLift ιE ιF (singularValueDiagonal d B)).singularValues =
        B.singularValues
      rw [singularValues_coordinateLift,
        singularValues_singularValueDiagonal B hrankB]
    obtain ⟨U, V, hfac⟩ :=
      exists_unitary_factorization_of_singularValues_eq hsigma
    exact ⟨U, V, hfac⟩
  have hyK : y ∈ K := subset_convexHull ℝ _ hLy
  have hzanti : Antitone z := fun i j hij =>
    A.singularValues_antitone (Fin.le_def.mp hij)
  have hz0 : ∀ i, 0 ≤ z i := fun i => A.singularValues_nonneg _
  have hy0 : ∀ i, 0 ≤ y i := fun i => B.singularValues_nonneg _
  have hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m), z i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m), y i := by
    intro m
    rcases le_or_gt m d with hm | hm
    · rw [sum_filter_lt_eq_sum_fin hm (fun k => A.singularValues k),
        sum_filter_lt_eq_sum_fin hm (fun k => B.singularValues k)]
      exact h m
    · have huniv : (Finset.univ.filter
          fun i : Fin d => (i : ℕ) < m) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
      rw [huniv]
      exact h d
  have hzK : z ∈ K :=
    mem_convex_of_prefix_sums_le hKconv hswap hneg hzanti hz0 hy0 hpre hyK
  have hsigmaA : A.singularValues = (L z).singularValues := by
    symm
    change (coordinateLift ιE ιF (singularValueDiagonal d A)).singularValues =
      A.singularValues
    rw [singularValues_coordinateLift,
      singularValues_singularValueDiagonal A hrankA]
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hsigmaA
  change L z ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hzK
  rw [hfac]
  exact twoSidedAction_mem_convexHull hzK U V


/-- Fan dominance in rectangular form.

Lean proof route for a weaker agent:

1. Transfer `N` to its finite symmetric gauge on singular values and apply the Ky Fan dominance theorem already developed in `KyFan.lean`.
2. Translate `rectangularKyFanSum` to the square zero-extension convention.
3. Apply the existing square Fan-dominance theorem and simplify `ofSquareFamily`.
-/
theorem apply_le_of_kyFanSum_le {A B : E →ₗ[𝕜] F}
    (h : ∀ k, rectangularKyFanSum k A ≤ rectangularKyFanSum k B) : N A ≤ N B := by
  let d : ℕ := min (finrank 𝕜 E) (finrank 𝕜 F)
  have hdE : d ≤ finrank 𝕜 E := by
    dsimp [d]
    exact min_le_left _ _
  have hdF : d ≤ finrank 𝕜 F := by
    dsimp [d]
    exact min_le_right _ _
  let ιE := initialCoordinateIsometry (𝕜 := 𝕜) (K := E) hdE
  let ιF := initialCoordinateIsometry (𝕜 := 𝕜) (K := F) hdF
  let XA := singularValueDiagonal d A
  let XB := singularValueDiagonal d B
  have hrankA : finrank 𝕜 A.range ≤ d := by
    have hdom : finrank 𝕜 A.range ≤ finrank 𝕜 E := by
      have hranknull := A.finrank_range_add_finrank_ker
      omega
    have hcod : finrank 𝕜 A.range ≤ finrank 𝕜 F := Submodule.finrank_le _
    dsimp [d]
    exact le_min hdom hcod
  have hrankB : finrank 𝕜 B.range ≤ d := by
    have hdom : finrank 𝕜 B.range ≤ finrank 𝕜 E := by
      have hranknull := B.finrank_range_add_finrank_ker
      omega
    have hcod : finrank 𝕜 B.range ≤ finrank 𝕜 F := Submodule.finrank_le _
    dsimp [d]
    exact le_min hdom hcod
  have hσA : XA.singularValues = A.singularValues := by
    simpa only [XA] using singularValues_singularValueDiagonal A hrankA
  have hσB : XB.singularValues = B.singularValues := by
    simpa only [XB] using singularValues_singularValueDiagonal B hrankB
  have hNA : N A = coordinateSquareNorm N ιE ιF XA :=
    apply_eq_coordinateSquareNorm N ιE ιF A XA hσA
  have hNB : N B = coordinateSquareNorm N ιE ιF XB :=
    apply_eq_coordinateSquareNorm N ιE ιF B XB hσB
  rw [hNA, hNB]
  apply UnitarilyInvariantNorm.apply_le_of_kyFanSum_le
  intro k
  rw [kyFanSum_eq_sum_fin, kyFanSum_eq_sum_fin, hσA, hσB]
  exact h k

/-- Pointwise singular-value dominance implies norm dominance.

Lean proof route for a weaker agent:

1. Sum the pointwise inequalities to obtain all Ky Fan prefix inequalities, then apply `apply_le_of_kyFanSum_le`.
2. Sum the pointwise inequalities over each finite prefix using `Finset.sum_le_sum`.
3. Invoke `apply_le_of_kyFanSum_le` with the resulting prefix inequalities.
-/
theorem apply_le_of_singularValues_le {A B : E →ₗ[𝕜] F}
    (h : ∀ i, A.singularValues i ≤ B.singularValues i) : N A ≤ N B := by
  apply N.apply_le_of_kyFanSum_le
  intro k
  unfold rectangularKyFanSum
  exact Finset.sum_le_sum fun i _ => h (i : ℕ)

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

/--
Lean proof route for a weaker agent:

1. Unfold `adjointTransport`; the theorem is the defining equation of the transported rectangular UI norm.
2. Prove it by `rfl` after the constructor is implemented, or by the constructor simp lemma.
-/
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

Lean proof route for a weaker agent:

1. Choose orthonormal bases of `E` and `F`; the zero extension is the block matrix with `A` in one off-diagonal block, so its Gram operator is `A⋆A` plus a zero block.
2. Compare sorted eigenvalues with zero padding.
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

/-- Every square unitarily invariant norm has a compatible rectangular
extension, unique after fixing its symmetric gauge family across dimensions. -/
noncomputable def ofSquareFamily
    (Ns : ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [FiniteDimensional 𝕜 H], UnitarilyInvariantNorm 𝕜 H) :
    RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

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
private theorem singularValues_smul_rect (a : 𝕜) (A : E →ₗ[𝕜] F) (i : ℕ) :
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

private theorem rectangularKyFanSum_eq_zeroExtension
    (k : ℕ) (A : E →ₗ[𝕜] F) :
    rectangularKyFanSum k A = kyFanSum k (zeroExtension A) := by
  rw [kyFanSum_eq_sum_fin]
  unfold rectangularKyFanSum
  rw [singularValues_zeroExtension]

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

/-- Schatten `p`-norm for `1 ≤ p`. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularUnitarilyInvariantNorm 𝕜 E F := by
  sorry

/-- The rectangular Frobenius norm is the square root of the sum of squared
column norms in any orthonormal basis of the domain.

Lean proof route for a weaker agent:

1. Unfold the rectangular Frobenius norm through zero extension or its singular values and reuse Parseval/the existing square Frobenius basis formula.
2. Rewrite the zero extension on the canonical L² direct-sum basis and eliminate the codomain-only basis vectors.
3. Use `Real.sqrt_eq_iff_sq_eq` only after proving nonnegativity of the finite sum.
-/
theorem frobenius_apply (A : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
    frobenius A = Real.sqrt (∑ i, ‖A (b i)‖ ^ 2) := by
  show Real.sqrt (∑ i, ‖A (stdOrthonormalBasis 𝕜 E i)‖ ^ 2) = _
  rw [← sum_sq_singularValues A rfl (stdOrthonormalBasis 𝕜 E),
    ← sum_sq_singularValues A rfl b]

/-- The Ky Fan norm evaluates to the prefix sum of singular values.

Lean proof route for a weaker agent:

1. This should be definitional once `kyFan` is constructed from `rectangularKyFanSum`
2. otherwise reduce through the zero-extension square norm.
-/
theorem kyFan_apply (k : ℕ) (A : E →ₗ[𝕜] F) :
    kyFan k A = rectangularKyFanSum k A :=
  rfl

/-- A finite two-sided unitary-orbit certificate bounds every rectangular
Ky Fan prefix by the same certificate mass.

Proof strategy:

1. instantiate `apply_le_of_finiteUnitaryOrbitCertificate` with `kyFan k`;
2. use the definitional evaluation of `kyFan` as `rectangularKyFanSum`;
3. leave the certificate construction entirely outside the Ky Fan layer.

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

/--
Lean proof route for a weaker agent:

1. Unfold `UnitarilyInvariantNorm.toRectangular` and the zero-extension bridge.
2. The proof should be definitional once the square-to-rectangular constructor is implemented.
-/
@[simp] theorem toRectangular_apply
    (N : UnitarilyInvariantNorm 𝕜 E) (A : E →ₗ[𝕜] E) :
    N.toRectangular A = N A :=
  rfl

end UnitarilyInvariantNorm
end ForMathlib
