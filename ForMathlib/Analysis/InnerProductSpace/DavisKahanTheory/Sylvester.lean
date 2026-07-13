/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.Residual
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.ReciprocalMultiplier
import ForMathlib.Analysis.InnerProductSpace.SylvesterBound
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.Foundation.Sylvester

/-!
# Sylvester equations under spectral separation

This file scaffolds the rectangular, every-unitarily-invariant-norm Sylvester
machinery implicit in the Davis--Kahan proofs.

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 6.
* Davis--Kahan (1970), Section 5, "On the equation `AX-XB=C`".
* The ordered/coercive special case already proved in
  `ForMathlib/Analysis/InnerProductSpace/SylvesterBound.lean`.
* `prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`,
  Theorem `Kiexp` and Remark `nad`, for the arbitrary-disjoint-spectrum
  Fourier representation, sharp constant, scaling audit, and attribution.

The interval/exterior theorem has sharp constant one.  The final section
scaffolds the separate `π/2`-constant extension for arbitrary disjoint spectral
sets, isolates its one remaining simultaneous Ky Fan multiplier theorem, and
proves the bounded-mass orbit barycenter, exact finite certificate, and arbitrary
unitarily invariant norm lifts from it.  It must not be used silently in the
classic constant-one API.
-/


/-! ## Remaining construction plan

The Sylvester map and its finite inverse are explicit.  The sharp
interval/exterior estimate is proved below for every rectangular unitarily
invariant norm by a dimension-free polar-absorption argument.  The remaining
analytic extension in this file is the independent `pi/2` theorem for arbitrary
disjoint spectral sets.  Its complete dependency scaffold now isolates the
finite simultaneous reciprocal-orbit interpolation theorem as the sole
harmonic-analysis root; coordinate expansion, Ky Fan control, real
orbit-convexity, exact finite certificates, arbitrary unitarily invariant
norms, and residual/perturbation layers are proved consequences.
-/


/-! ## Weak-agent execution plan: finite Sylvester inversion and sharp bounds

### A. Repair the total solution definition without adding hypotheses

`solveSylvester A B C` is intentionally total, while invertibility is only
known under a gap.  Define it by a decidable branch on bijectivity:

* if `h : Function.Bijective (sylvesterOperator A B)`, use
  `(LinearEquiv.ofBijective _ h).symm C`;
* otherwise return `0`.

Add a private lemma saying the definition reduces to that inverse under a
supplied bijectivity proof.  In `sylvesterOperator_solveSylvester`, derive
injectivity from the gap, obtain surjectivity with
`LinearMap.injective_iff_surjective`, enter the positive branch, and use
`LinearEquiv.apply_symm_apply`.  This is cleaner than choosing eigenbases in
the definition and confines coordinates to the injectivity proof.

### B. Direct injectivity proof

Use eigenbases `eA` and `eB` for the symmetric maps.  For `Y` in the kernel,
apply the equation to `eB j` and take inner product with `eA i`.  After rewriting
both eigenvector equations, obtain

`(α i - β j) * ⟪eA i, Y (eB j)⟫ = 0`.

Turn `SpectraSeparated ... δ` and `0 < δ` into `α i - β j ≠ 0`; then every
matrix coefficient vanishes.  Prove `Y (eB j) = 0` by the orthonormal-basis
extensionality theorem and finally prove `Y = 0` by `LinearMap.ext` plus basis
induction/expansion.  Introduce named helpers for “eigenvalue belongs to the
restricted spectrum” and “separation implies denominator nonzero” so the main
proof is not dominated by set-membership coercions.

### C. Ordered form bounds

Completed through the rectangular abstract absorption theorem in
`SylvesterBound.lean`.  Its raw assumptions are subadditivity, absolute
homogeneity, and the two operator-ideal inequalities, so it applies directly
to every rectangular UI norm after finite maps are converted to continuous
maps.

### D. Interval/exterior gap

Completed by a stronger route than the originally planned block splitting.
Shift to the midpoint, replace the exterior operator by its absolute value,
and absorb the polar unitary into the unknown.  The new dimension-free
rectangular polar-absorption theorem then gives the sharp constant-one bound
for every UI norm at once.  The Ky Fan prefix-sum theorem is a direct
specialization rather than the root proof.

### E. Arbitrary disjoint spectra

The full dependency scaffold is now present and remains independent of the
constant-one absorption theorem:

1. `sylvesterReciprocalKernel` records the reciprocal eigenvalue-difference
   symbol in the canonical eigenbases;
2. `sylvester_eigenvalue_sub_ne_zero` discharges every denominator from
   positive spectral separation;
3. `sylvester_eigenbasis_coefficient_equation` identifies the coordinate
   Sylvester equation `(αᵢ-βⱼ)Xᵢⱼ=Cᵢⱼ`;
4. `hasReciprocalOrbitInterpolation_pi_div_two` is the single remaining
   harmonic-analysis root: construct one finite family of coefficients and
   left/right unitary factors that realizes the reciprocal action on every
   coordinate matrix unit simultaneously with mass at most `π / 2`;
5. `kyFan_reciprocalMultiplier_le` follows by coordinate expansion and the
   generic finite-orbit certificate bound;
6. `sylvester_barycentricOrbitRepresentation_of_spectralDistance` follows from
   that prefix estimate by rectangular orbit-convexity, uniformly over `ℝ` and
   `ℂ`;
7. the exact finite certificate, public Ky Fan alias, arbitrary-UI-norm theorem,
   and residual/perturbation `sin Θ` wrappers are proved downstream.

The remaining proof should therefore concentrate only on the common finite
reciprocal-orbit interpolation and its sharp `π / 2` mass bound.  Do not
re-open coordinate expansion, real convex-hull descent, finite-certificate
extraction, transport, or Fan-dominance layers, and do not derive this theorem
from the constant-one interval/exterior route.

### F. Coercion discipline

Perform algebra in `LinearMap` until the final norm estimate.  When invoking
`SylvesterBound`, create named continuous maps and prove the equation with
`ContinuousLinearMap.ext`; do not repeatedly unfold `toContinuousLinearMap`.
After any composition rewrite, normalize with `LinearMap.comp_apply` or
`ContinuousLinearMap.comp_apply` before using eigenvector equations.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Sylvester operator `X ↦ A X - X B`. -/
noncomputable def sylvesterOperator (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) where
  toFun X := A ∘ₗ X - X ∘ₗ B
  map_add' X Y := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      map_add]
    module
  map_smul' c X := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      map_smul, smul_sub, RingHom.id_apply]

/-- Ordered spectral separation for the Sylvester equation. -/
def OrderedSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (δ : ℝ) : Prop :=
  OrderedGap B ⊤ A ⊤ δ ∨ OrderedGap A ⊤ B ⊤ δ

/-- Interval/exterior separation with the spectrum of `B` in `[a,b]` and the
spectrum of `A` outside `(a-δ,b+δ)`. -/
def IntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  SpectrumIn B ⊤ (Set.Icc a b) ∧
    SpectrumIn A ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- The Sylvester operator is injective under positive spectral separation.

The proof is coordinate-free at the API boundary but uses the canonical
self-adjoint eigenbases internally.  Testing `A X - X B = 0` against an
`A`-eigenvector after evaluating at a `B`-eigenvector gives
`(α - β) * ⟪X eβ, eα⟫ = 0`; separation makes the scalar factor nonzero, and
two basis-extensionality steps force `X = 0`.
-/
theorem sylvesterOperator_injective {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ) :
    Function.Injective (sylvesterOperator A B) := by
  intro X Y hXY
  have hker : sylvesterOperator A B (X - Y) = 0 := by
    rw [map_sub, hXY, sub_self]
  apply sub_eq_zero.mp
  apply (hB.eigenvectorBasis rfl).toBasis.ext
  intro j
  apply InnerProductSpace.ext_inner_right_basis (hA.eigenvectorBasis rfl).toBasis
  intro i
  let α : ℝ := hA.eigenvalues rfl i
  let β : ℝ := hB.eigenvalues rfl j
  have hα : α ∈ restrictedSpectrum A ⊤ :=
    ⟨hA.eigenvectorBasis rfl i, Submodule.mem_top,
      (hA.eigenvectorBasis rfl).orthonormal.ne_zero i,
      by
        dsimp [α]
        exact hA.apply_eigenvectorBasis rfl i⟩
  have hβ : β ∈ restrictedSpectrum B ⊤ :=
    ⟨hB.eigenvectorBasis rfl j, Submodule.mem_top,
      (hB.eigenvectorBasis rfl).orthonormal.ne_zero j,
      by
        dsimp [β]
        exact hB.apply_eigenvectorBasis rfl j⟩
  have hαβ : α ≠ β := by
    have habs : 0 < |α - β| := lt_of_lt_of_le hδ (hgap α β hα hβ)
    exact sub_ne_zero.mp (abs_pos.mp habs)
  have hαβ𝕜 : (α : 𝕜) ≠ (β : 𝕜) := fun h =>
    hαβ (RCLike.ofReal_injective h)
  have hpoint := LinearMap.congr_fun hker (hB.eigenvectorBasis rfl j)
  change A ((X - Y) (hB.eigenvectorBasis rfl j)) -
      (X - Y) (B (hB.eigenvectorBasis rfl j)) = 0 at hpoint
  have heq : A ((X - Y) (hB.eigenvectorBasis rfl j)) =
      (X - Y) (B (hB.eigenvectorBasis rfl j)) :=
    sub_eq_zero.mp hpoint
  have hinner :
      ⟪(X - Y) (hB.eigenvectorBasis rfl j),
          A (hA.eigenvectorBasis rfl i)⟫_𝕜 =
        ⟪(X - Y) (B (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    calc
      _ = ⟪A ((X - Y) (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 :=
        (hA ((X - Y) (hB.eigenvectorBasis rfl j))
          (hA.eigenvectorBasis rfl i)).symm
      _ = _ := congrArg (fun z : F => ⟪z, hA.eigenvectorBasis rfl i⟫_𝕜) heq
  have hscalar :
      (α : 𝕜) * ⟪(X - Y) (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 =
        (β : 𝕜) * ⟪(X - Y) (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    simpa only [α, β, hA.apply_eigenvectorBasis rfl i,
      hB.apply_eigenvectorBasis rfl j, map_smul, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal] using hinner
  have hmul :
      ((α : 𝕜) - (β : 𝕜)) *
          ⟪(X - Y) (hB.eigenvectorBasis rfl j),
            hA.eigenvectorBasis rfl i⟫_𝕜 = 0 := by
    rw [sub_mul, hscalar, sub_self]
  have hcoeff := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hαβ𝕜)
  simpa using hcoeff

/-- Unique solution of the finite-dimensional Sylvester equation.

The definition is total: when the Sylvester operator is bijective it uses the
inverse linear equivalence, and otherwise it returns zero.  All computation
lemmas enter the bijective branch explicitly. -/
noncomputable def solveSylvester (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (C : E →ₗ[𝕜] F) : E →ₗ[𝕜] F := by
  classical
  exact if h : Function.Bijective (sylvesterOperator A B) then
    (LinearEquiv.ofBijective (sylvesterOperator A B) h).symm C
  else
    0

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
private theorem solveSylvester_eq_of_bijective
    (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E) (C : E →ₗ[𝕜] F)
    (h : Function.Bijective (sylvesterOperator A B)) :
    solveSylvester A B C =
      (LinearEquiv.ofBijective (sylvesterOperator A B) h).symm C := by
  classical
  simp only [solveSylvester, dif_pos h]

/-- The chosen solution satisfies the Sylvester equation under separation.

Injectivity above implies surjectivity because the Sylvester operator is an
endomorphism of the finite-dimensional map space.  The result is therefore
the `apply_symm_apply` identity of the linear equivalence built from that
bijection; no second coordinate calculation is needed.
-/
theorem sylvesterOperator_solveSylvester {A : F →ₗ[𝕜] F}
    {B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (C : E →ₗ[𝕜] F) :
    A ∘ₗ solveSylvester A B C - solveSylvester A B C ∘ₗ B = C := by
  have hinj : Function.Injective (sylvesterOperator A B) :=
    sylvesterOperator_injective hA hB hδ hgap
  have hbij : Function.Bijective (sylvesterOperator A B) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  change sylvesterOperator A B (solveSylvester A B C) = C
  rw [solveSylvester_eq_of_bijective A B C hbij]
  exact (LinearEquiv.ofBijective (sylvesterOperator A B) hbij).apply_symm_apply C

private theorem eigenvalue_mem_restrictedSpectrum_top
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) :
    hT.eigenvalues rfl i ∈ restrictedSpectrum T ⊤ :=
  ⟨hT.eigenvectorBasis rfl i, Submodule.mem_top,
    (hT.eigenvectorBasis rfl).orthonormal.ne_zero i,
    hT.apply_eigenvectorBasis rfl i⟩

private theorem re_inner_le_of_eigenvalues_le
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {c : ℝ}
    (hc : ∀ i : Fin (Module.finrank 𝕜 E), hT.eigenvalues rfl i ≤ c)
    (x : E) : RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT rfl x]
  calc
    (∑ i : Fin (Module.finrank 𝕜 E),
        hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2)
        ≤ ∑ i : Fin (Module.finrank 𝕜 E),
            c * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)
    _ = c * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          simp_rw [OrthonormalBasis.repr_apply_apply]
          exact (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right x

private theorem le_re_inner_of_le_eigenvalues
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {c : ℝ}
    (hc : ∀ i : Fin (Module.finrank 𝕜 E), c ≤ hT.eigenvalues rfl i)
    (x : E) : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT rfl x]
  calc
    c * ‖x‖ ^ 2 = ∑ i : Fin (Module.finrank 𝕜 E),
        c * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          simp_rw [OrthonormalBasis.repr_apply_apply]
          exact (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right x |>.symm
    _ ≤ ∑ i : Fin (Module.finrank 𝕜 E),
        hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

private theorem opNorm_shift_le_of_spectrumIn_Icc
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {a b : ℝ} (hab : a ≤ b)
    (hsp : SpectrumIn T ⊤ (Set.Icc a b)) :
    ‖(T - (((a + b) / 2 : ℝ) : 𝕜) • LinearMap.id).toContinuousLinearMap‖ ≤
      (b - a) / 2 := by
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : E →ₗ[𝕜] E := T - (m : 𝕜) • LinearMap.id
  have hS : S.IsSymmetric := hT.sub fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have ha : ∀ x, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
    le_re_inner_of_le_eigenvalues hT fun i =>
      (hsp (eigenvalue_mem_restrictedSpectrum_top hT i)).1
  have hb : ∀ x, RCLike.re ⟪T x, x⟫_𝕜 ≤ b * ‖x‖ ^ 2 :=
    re_inner_le_of_eigenvalues_le hT fun i =>
      (hsp (eigenvalue_mem_restrictedSpectrum_top hT i)).2
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hform : ∀ x, |RCLike.re ⟪S x, x⟫_𝕜| ≤ r * ‖x‖ ^ 2 := by
    intro x
    have hval : RCLike.re ⟪S x, x⟫_𝕜 =
        RCLike.re ⟪T x, x⟫_𝕜 - m * ‖x‖ ^ 2 := by
      simp only [S, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hval, abs_le]
    constructor <;> simp only [m, r] <;> nlinarith [ha x, hb x]
  change ‖S.toContinuousLinearMap‖ ≤ r
  exact ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le
    (fun x y => hS x y) hr hform

private theorem norm_shift_lower_of_spectrumOutside
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hsp : SpectrumIn T ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    ∀ x : E, ((b - a) / 2 + δ) * ‖x‖ ≤
      ‖(T - (((a + b) / 2 : ℝ) : 𝕜) •
          (LinearMap.id : E →ₗ[𝕜] E)) x‖ := by
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : E →ₗ[𝕜] E := T - (m : 𝕜) • LinearMap.id
  have hS : S.IsSymmetric := hT.sub fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hk : 0 ≤ r + δ := by linarith
  have hsep : ∀ i : Fin (Module.finrank 𝕜 E),
      r + δ ≤ |hT.eigenvalues rfl i - m| := by
    intro i
    have hi := hsp (eigenvalue_mem_restrictedSpectrum_top hT i)
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, not_and_or, not_lt] at hi
    rcases hi with hi | hi
    · rw [abs_of_nonpos]
      · simp only [m, r]
        linarith
      · simp only [m]
        linarith
    · rw [abs_of_nonneg]
      · simp only [m, r]
        linarith
      · simp only [m]
        linarith
  intro x
  have hsq : (r + δ) ^ 2 * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2 := by
    rw [← (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right (S x),
      ← (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hinner :
        ⟪hT.eigenvectorBasis rfl i, S x⟫_𝕜 =
          (((hT.eigenvalues rfl i - m : ℝ) : 𝕜) *
            ⟪hT.eigenvectorBasis rfl i, x⟫_𝕜) := by
      rw [← hS (hT.eigenvectorBasis rfl i) x]
      simp only [S, LinearMap.sub_apply, hT.apply_eigenvectorBasis,
        LinearMap.smul_apply, LinearMap.id_apply, inner_sub_left,
        inner_smul_left, RCLike.conj_ofReal, map_sub, sub_mul]
    rw [hinner, norm_mul, RCLike.norm_ofReal, mul_pow]
    gcongr
    exact hsep i
  change (r + δ) * ‖x‖ ≤ ‖S x‖
  rw [← sq_le_sq₀ (mul_nonneg hk (norm_nonneg x)) (norm_nonneg (S x))]
  simpa [mul_pow] using hsq

/-- Sharp operator-norm interval/exterior Sylvester estimate.

The analytic step is the dimension-free polar-absorption theorem in
`SylvesterBound`.  Finite dimensionality is used only to turn the interval and
exterior eigenvalue hypotheses into a strip norm bound for the inner operator
and a coercive bound for the modulus of the outer operator. -/
theorem opNorm_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * ‖X.toContinuousLinearMap‖ ≤ ‖C.toContinuousLinearMap‖ := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    rw [hX0]
    simp
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    rw [hX0]
    simp
  letI : NeZero (Module.finrank 𝕜 E) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  letI : NeZero (Module.finrank 𝕜 F) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
  have hj₀ := hgap.1 (eigenvalue_mem_restrictedSpectrum_top hB j₀)
  have hab : a ≤ b := hj₀.1.trans hj₀.2
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : F →ₗ[𝕜] F := A - (m : 𝕜) • LinearMap.id
  let T : E →ₗ[𝕜] E := B - (m : 𝕜) • LinearMap.id
  let H : F →ₗ[𝕜] F := ForMathlib.abs S
  let U : F ≃ₗᵢ[𝕜] F := polarUnitary S
  let Z : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ X
  let Y : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ C
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ r := by
    simpa [T, m, r] using opNorm_shift_le_of_spectrumIn_Icc hB hab hgap.1
  have hSlower : ∀ y, (r + δ) * ‖y‖ ≤ ‖S y‖ := by
    simpa [S, m, r] using
      norm_shift_lower_of_spectrumOutside hA hab hδ hgap.2
  have hHsym : H.IsSymmetric := (ForMathlib.isPositive_abs S).isSymmetric
  have hHeig : ∀ i : Fin (Module.finrank 𝕜 F),
      r + δ ≤ hHsym.eigenvalues rfl i := by
    intro i
    have hi : (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖H (hHsym.eigenvectorBasis rfl i)‖ := by
      change (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖ForMathlib.abs S (hHsym.eigenvectorBasis rfl i)‖
      rw [ForMathlib.norm_abs_apply]
      exact hSlower (hHsym.eigenvectorBasis rfl i)
    have hnonneg := (ForMathlib.isPositive_abs S).nonneg_eigenvalues rfl i
    rw [hHsym.apply_eigenvectorBasis rfl i, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg hnonneg,
      (hHsym.eigenvectorBasis rfl).orthonormal.norm_eq_one, mul_one, mul_one] at hi
    exact hi
  have hHform : ∀ y, (r + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪H y, y⟫_𝕜 :=
    le_re_inner_of_le_eigenvalues hHsym hHeig
  have hShift : S ∘ₗ X - X ∘ₗ T = C := by
    ext x
    have hx := LinearMap.congr_fun hEq x
    simp only [S, T, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hx
    rw [← hx]
    module
  have hPolar : H ∘ₗ X - Z ∘ₗ T = Y := by
    ext x
    have hx := LinearMap.congr_fun hShift x
    have hx' : U.symm (S (X x)) - U.symm (X (T x)) = U.symm (C x) := by
      calc
        U.symm (S (X x)) - U.symm (X (T x)) =
            U.symm (S (X x) - X (T x)) := (map_sub U.symm _ _).symm
        _ = U.symm (C x) := congrArg U.symm hx
    have hSX : U.symm (S (X x)) = H (X x) := by
      have hp := LinearMap.congr_fun (polar_decomposition_unitary S) (X x)
      change S (X x) = U (H (X x)) at hp
      rw [hp, U.symm_apply_apply]
    change H (X x) - U.symm (X (T x)) = U.symm (C x)
    rwa [← hSX]
  have hZnorm : ‖Z.toContinuousLinearMap‖ = ‖X.toContinuousLinearMap‖ := by
    apply le_antisymm
    · refine Z.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖U.symm (X x)‖ ≤ ‖X.toContinuousLinearMap‖ * ‖x‖
      rw [U.symm.norm_map]
      exact X.toContinuousLinearMap.le_opNorm x
    · refine X.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖X x‖ ≤ ‖Z.toContinuousLinearMap‖ * ‖x‖
      rw [← U.symm.norm_map (X x)]
      exact Z.toContinuousLinearMap.le_opNorm x
  have hYnorm : ‖Y.toContinuousLinearMap‖ = ‖C.toContinuousLinearMap‖ := by
    apply le_antisymm
    · refine Y.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖U.symm (C x)‖ ≤ ‖C.toContinuousLinearMap‖ * ‖x‖
      rw [U.symm.norm_map]
      exact C.toContinuousLinearMap.le_opNorm x
    · refine C.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖C x‖ ≤ ‖Y.toContinuousLinearMap‖ * ‖x‖
      rw [← U.symm.norm_map (C x)]
      exact Y.toContinuousLinearMap.le_opNorm x
  have hPolar' : H.toContinuousLinearMap ∘L X.toContinuousLinearMap -
      Z.toContinuousLinearMap ∘L T.toContinuousLinearMap = Y.toContinuousLinearMap := by
    ext x
    simpa [ContinuousLinearMap.comp_apply] using LinearMap.congr_fun hPolar x
  have hbound := ContinuousLinearMap.gap_mul_opNorm_le_of_comp_sub_comp_eq
    (fun x y => hHsym x y) hr hδ hHform hTnorm
    hZnorm hPolar'
  rwa [hYnorm] at hbound

private theorem uiNorm_sylvester_le_of_form_bounds_aux
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  let A' : F →L[𝕜] F := A.toContinuousLinearMap
  let B' : E →L[𝕜] E := B.toContinuousLinearMap
  let X' : E →L[𝕜] F := X.toContinuousLinearMap
  let C' : E →L[𝕜] F := C.toContinuousLinearMap
  let N' : (E →L[𝕜] F) → ℝ := fun T => N T.toLinearMap
  have hA' : A'.IsSymmetric := fun x y => hA x y
  have hB' : B'.IsSymmetric := fun x y => hB x y
  have hadd : ∀ f g : E →L[𝕜] F, N' (f + g) ≤ N' f + N' g := by
    intro f g
    simp only [N', ContinuousLinearMap.toLinearMap_add]
    exact N.add_le _ _
  have hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] F), N' (a • f) = ‖a‖ * N' f := by
    intro a f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact N.smul_eq _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ T : E →L[𝕜] F,
      N' (D ∘L T) ≤ ‖D‖ * N' T := by
    intro D T
    change N (D.toLinearMap ∘ₗ T.toLinearMap) ≤ ‖D‖ * N T.toLinearMap
    have h := N.comp_le_opNorm_mul D.toLinearMap T.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
  have hidealR : ∀ T : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (T ∘L D) ≤ N' T * ‖D‖ := by
    intro T D
    change N (T.toLinearMap ∘ₗ D.toLinearMap) ≤ N T.toLinearMap * ‖D‖
    have h := N.comp_le_mul_opNorm T.toLinearMap D.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
  have hEq' : A' ∘L X' - X' ∘L B' = C' := by
    ext x
    simpa [A', B', X', C', ContinuousLinearMap.comp_apply] using
      LinearMap.congr_fun hEq x
  have hbound : N' X' ≤ N' C' / δ :=
    ContinuousLinearMap.le_div_of_comp_sub_comp_eq_rectangular
      hadd hsmul hidealL hidealR hA' hB' hδ hAform hBform hEq'
  have hbound' : N X ≤ N C / δ := by
    simpa [N', X', C'] using hbound
  rw [le_div_iff₀ hδ] at hbound'
  simpa [mul_comm] using hbound'


/-- Sharp constant-one ordered Sylvester estimate in every rectangular UI
norm.

The proof first extends the integral-free absorption argument from square to
rectangular operator seminorms.  In either ordered orientation, the largest
eigenvalue of the lower block supplies a cut `c`; eigenbasis expansion then
gives the global upper and lower quadratic-form bounds.  The reverse
orientation is reduced to the first by taking adjoints and transporting the
rectangular UI norm.
-/
theorem uiNorm_sylvester_le_of_orderedGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedSylvesterGap A B δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    have hC0 : C = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    simp [hX0, hC0, N.apply_zero]
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have hC0 : C = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [hX0, hC0, N.apply_zero]
  letI : NeZero (Module.finrank 𝕜 E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  letI : NeZero (Module.finrank 𝕜 F) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  rcases hgap with hBA | hAB
  · let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hB.eigenvalues rfl j₀
    have hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
      re_inner_le_of_eigenvalues_le hB (fun j =>
        hB.eigenvalues_antitone rfl (Fin.zero_le j))
    have hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
      le_re_inner_of_le_eigenvalues hA fun i =>
        hBA c (hA.eigenvalues rfl i)
          (eigenvalue_mem_restrictedSpectrum_top hB j₀)
          (eigenvalue_mem_restrictedSpectrum_top hA i)
    exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq
  · let i₀ : Fin (Module.finrank 𝕜 F) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hA.eigenvalues rfl i₀
    have hAform : ∀ y, RCLike.re ⟪A y, y⟫_𝕜 ≤ c * ‖y‖ ^ 2 :=
      re_inner_le_of_eigenvalues_le hA (fun i =>
        hA.eigenvalues_antitone rfl (Fin.zero_le i))
    have hBform : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜 :=
      le_re_inner_of_le_eigenvalues hB fun j =>
        hAB c (hB.eigenvalues rfl j)
          (eigenvalue_mem_restrictedSpectrum_top hA i₀)
          (eigenvalue_mem_restrictedSpectrum_top hB j)
    have hadj : X.adjoint ∘ₗ A - B ∘ₗ X.adjoint = C.adjoint := by
      simpa only [map_sub, LinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq] using
        congrArg (fun T : E →ₗ[𝕜] F => T.adjoint) hEq
    have hEqAdj : B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint := by
      calc
        B ∘ₗ X.adjoint - X.adjoint ∘ₗ A
            = -(X.adjoint ∘ₗ A - B ∘ₗ X.adjoint) := by abel
        _ = -C.adjoint := congrArg Neg.neg hadj
    have hbound := uiNorm_sylvester_le_of_form_bounds_aux
      (RectangularUnitarilyInvariantNorm.adjointTransport N)
      hB hA hδ hBform hAform hEqAdj
    have hXnorm :
        (RectangularUnitarilyInvariantNorm.adjointTransport N) X.adjoint = N X := by
      change N X.adjoint.adjoint = N X
      rw [LinearMap.adjoint_adjoint]
    have hCnorm :
        (RectangularUnitarilyInvariantNorm.adjointTransport N) (-C.adjoint) = N C := by
      change N ((-C.adjoint).adjoint) = N C
      rw [map_neg, LinearMap.adjoint_adjoint, N.apply_neg]
    rw [hXnorm, hCnorm] at hbound
    exact hbound

/-- Sharp constant-one interval/exterior Sylvester estimate in every
rectangular UI norm.

The proof follows the dimension-free polar-absorption route used for the
operator norm.  Shift the interval to its midpoint, replace the exterior
operator by its absolute value, and absorb the polar unitary into the unknown
and right-hand side.  The abstract rectangular seminorm theorem in
`SylvesterBound` applies because every rectangular UI norm is subadditive,
absolutely homogeneous, and satisfies both operator-ideal inequalities.
Unitary invariance identifies the rotated norms with the original ones.
-/
theorem uiNorm_sylvester_le_of_intervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    rw [hX0, N.apply_zero, mul_zero]
    exact N.nonneg C
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    rw [hX0, N.apply_zero, mul_zero]
    exact N.nonneg C
  letI : NeZero (Module.finrank 𝕜 E) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  letI : NeZero (Module.finrank 𝕜 F) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
  have hj₀ := hgap.1 (eigenvalue_mem_restrictedSpectrum_top hB j₀)
  have hab : a ≤ b := hj₀.1.trans hj₀.2
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : F →ₗ[𝕜] F := A - (m : 𝕜) • LinearMap.id
  let T : E →ₗ[𝕜] E := B - (m : 𝕜) • LinearMap.id
  let H : F →ₗ[𝕜] F := ForMathlib.abs S
  let U : F ≃ₗᵢ[𝕜] F := polarUnitary S
  let Z : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ X
  let Y : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ C
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ r := by
    simpa [T, m, r] using opNorm_shift_le_of_spectrumIn_Icc hB hab hgap.1
  have hSlower : ∀ y, (r + δ) * ‖y‖ ≤ ‖S y‖ := by
    simpa [S, m, r] using
      norm_shift_lower_of_spectrumOutside hA hab hδ hgap.2
  have hHsym : H.IsSymmetric := (ForMathlib.isPositive_abs S).isSymmetric
  have hHeig : ∀ i : Fin (Module.finrank 𝕜 F),
      r + δ ≤ hHsym.eigenvalues rfl i := by
    intro i
    have hi : (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖H (hHsym.eigenvectorBasis rfl i)‖ := by
      change (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖ForMathlib.abs S (hHsym.eigenvectorBasis rfl i)‖
      rw [ForMathlib.norm_abs_apply]
      exact hSlower (hHsym.eigenvectorBasis rfl i)
    have hnonneg := (ForMathlib.isPositive_abs S).nonneg_eigenvalues rfl i
    rw [hHsym.apply_eigenvectorBasis rfl i, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg hnonneg,
      (hHsym.eigenvectorBasis rfl).orthonormal.norm_eq_one, mul_one, mul_one] at hi
    exact hi
  have hHform : ∀ y, (r + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪H y, y⟫_𝕜 :=
    le_re_inner_of_le_eigenvalues hHsym hHeig
  have hShift : S ∘ₗ X - X ∘ₗ T = C := by
    ext x
    have hx := LinearMap.congr_fun hEq x
    simp only [S, T, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hx
    rw [← hx]
    module
  have hPolar : H ∘ₗ X - Z ∘ₗ T = Y := by
    ext x
    have hx := LinearMap.congr_fun hShift x
    have hx' : U.symm (S (X x)) - U.symm (X (T x)) = U.symm (C x) := by
      calc
        U.symm (S (X x)) - U.symm (X (T x)) =
            U.symm (S (X x) - X (T x)) := (map_sub U.symm _ _).symm
        _ = U.symm (C x) := congrArg U.symm hx
    have hSX : U.symm (S (X x)) = H (X x) := by
      have hp := LinearMap.congr_fun (polar_decomposition_unitary S) (X x)
      change S (X x) = U (H (X x)) at hp
      rw [hp, U.symm_apply_apply]
    change H (X x) - U.symm (X (T x)) = U.symm (C x)
    rwa [← hSX]
  have hZnorm : N Z = N X := by
    change N (U.symm.toLinearMap ∘ₗ X) = N X
    have h := N.invariant U.symm (LinearIsometryEquiv.refl 𝕜 E) X
    have hcomp : U.symm.toLinearMap ∘ₗ X ∘ₗ
        (LinearIsometryEquiv.refl 𝕜 E).toLinearMap =
        U.symm.toLinearMap ∘ₗ X := by
      ext x
      rfl
    rwa [hcomp] at h
  have hYnorm : N Y = N C := by
    change N (U.symm.toLinearMap ∘ₗ C) = N C
    have h := N.invariant U.symm (LinearIsometryEquiv.refl 𝕜 E) C
    have hcomp : U.symm.toLinearMap ∘ₗ C ∘ₗ
        (LinearIsometryEquiv.refl 𝕜 E).toLinearMap =
        U.symm.toLinearMap ∘ₗ C := by
      ext x
      rfl
    rwa [hcomp] at h
  let H' : F →L[𝕜] F := H.toContinuousLinearMap
  let T' : E →L[𝕜] E := T.toContinuousLinearMap
  let X' : E →L[𝕜] F := X.toContinuousLinearMap
  let Z' : E →L[𝕜] F := Z.toContinuousLinearMap
  let Y' : E →L[𝕜] F := Y.toContinuousLinearMap
  let N' : (E →L[𝕜] F) → ℝ := fun Q => N Q.toLinearMap
  have hadd : ∀ f g : E →L[𝕜] F, N' (f + g) ≤ N' f + N' g := by
    intro f g
    simp only [N', ContinuousLinearMap.toLinearMap_add]
    exact N.add_le _ _
  have hsmul : ∀ (q : 𝕜) (f : E →L[𝕜] F), N' (q • f) = ‖q‖ * N' f := by
    intro q f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact N.smul_eq _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ Q : E →L[𝕜] F,
      N' (D ∘L Q) ≤ ‖D‖ * N' Q := by
    intro D Q
    change N (D.toLinearMap ∘ₗ Q.toLinearMap) ≤ ‖D‖ * N Q.toLinearMap
    have h := N.comp_le_opNorm_mul D.toLinearMap Q.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
    rwa [hD] at h
  have hidealR : ∀ Q : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (Q ∘L D) ≤ N' Q * ‖D‖ := by
    intro Q D
    change N (Q.toLinearMap ∘ₗ D.toLinearMap) ≤ N Q.toLinearMap * ‖D‖
    have h := N.comp_le_mul_opNorm Q.toLinearMap D.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
    rwa [hD] at h
  have hPolar' : H' ∘L X' - Z' ∘L T' = Y' := by
    ext x
    simpa [H', T', X', Z', Y', ContinuousLinearMap.comp_apply] using
      LinearMap.congr_fun hPolar x
  have hZX' : N' Z' = N' X' := by
    simpa [N', X', Z'] using hZnorm
  have hbound := ContinuousLinearMap.gap_mul_le_of_comp_sub_comp_eq_rectangular
    hadd hsmul hidealL hidealR (fun x y => hHsym x y) hr hδ hHform
    hTnorm hZX' hPolar'
  have hbound' : δ * N X ≤ N Y := by
    simpa [N', X', Y'] using hbound
  rwa [hYnorm] at hbound'

/-- Ky Fan specialization of the sharp interval/exterior Sylvester
estimate.  The hard work is already contained in
`uiNorm_sylvester_le_of_intervalGap`; evaluating the concrete Ky Fan norm gives
this singular-value prefix-sum form directly.
-/
theorem kyFan_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  have h := uiNorm_sylvester_le_of_intervalGap
    (RectangularUnitarilyInvariantNorm.kyFan k) hA hB hδ hgap hEq
  simpa only [RectangularUnitarilyInvariantNorm.kyFan_apply] using h

/-- Ordered positivity/coercivity form used by the existing integral-free
proof.

Lean proof route for a weaker agent:

1. Dispatch through the already proved `ForMathlib.SylvesterBound` theorem after converting its norm abstraction to the rectangular UI API.
2. This is the fastest direct finite route.
-/
theorem uiNorm_sylvester_le_of_form_bounds
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq

/-! ## Arbitrary disjoint spectra: the `π/2` scaffold

The Bhatia--Davis--McIntosh extension is deliberately factored at the weakest
analytic seam.  The finite spectral-coordinate algebra is explicit below, the
single remaining hard theorem is the simultaneous Ky Fan prefix estimate, and
rectangular Fan dominance then lifts that estimate to every UI norm.  Keeping
this seam at the Ky Fan level prevents the downstream residual and perturbation
APIs from depending on a particular Fourier, Schur-multiplier, or contour
implementation.
-/

/-- Reciprocal spectral multiplier in the canonical eigenbases of `A` and `B`.
The gap hypothesis is not built into the definition; it is supplied when the
kernel is used, so the object remains a simple coordinate function. -/
noncomputable def sylvesterReciprocalKernel
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    Fin (Module.finrank 𝕜 F) → Fin (Module.finrank 𝕜 E) → 𝕜 :=
  fun i j =>
    ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜))⁻¹

/-- Positive spectral separation makes every denominator of the reciprocal
kernel nonzero.  This is the scalar fact used both by the coordinate solution
formula and by the multiplier estimate. -/
theorem sylvester_eigenvalue_sub_ne_zero
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)) :
    (hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜) ≠ 0 := by
  let α : ℝ := hA.eigenvalues rfl i
  let β : ℝ := hB.eigenvalues rfl j
  have hα : α ∈ restrictedSpectrum A ⊤ :=
    eigenvalue_mem_restrictedSpectrum_top hA i
  have hβ : β ∈ restrictedSpectrum B ⊤ :=
    eigenvalue_mem_restrictedSpectrum_top hB j
  have habs : 0 < |α - β| := lt_of_lt_of_le hδ (hgap α β hα hβ)
  have hαβ : α ≠ β := sub_ne_zero.mp (abs_pos.mp habs)
  exact sub_ne_zero.mpr fun h => hαβ (RCLike.ofReal_injective h)

/-- Entrywise spectral-coordinate form of the Sylvester equation.  It exposes
exactly the scalar equation to which the reciprocal kernel is applied:
`(αᵢ-βⱼ) Xᵢⱼ = Cᵢⱼ`. -/
theorem sylvester_eigenbasis_coefficient_equation
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hEq : A ∘ₗ X - X ∘ₗ B = C)
    (i : Fin (Module.finrank 𝕜 F)) (j : Fin (Module.finrank 𝕜 E)) :
    ((hA.eigenvalues rfl i : 𝕜) - (hB.eigenvalues rfl j : 𝕜)) *
        ⟪X (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 =
      ⟪C (hB.eigenvectorBasis rfl j), hA.eigenvectorBasis rfl i⟫_𝕜 := by
  have hpoint := LinearMap.congr_fun hEq (hB.eigenvectorBasis rfl j)
  change A (X (hB.eigenvectorBasis rfl j)) -
      X (B (hB.eigenvectorBasis rfl j)) =
        C (hB.eigenvectorBasis rfl j) at hpoint
  have hinner :
      ⟪X (hB.eigenvectorBasis rfl j),
          A (hA.eigenvectorBasis rfl i)⟫_𝕜 -
        ⟪X (B (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 =
        ⟪C (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    calc
      _ = ⟪A (X (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 -
          ⟪X (B (hB.eigenvectorBasis rfl j)),
            hA.eigenvectorBasis rfl i⟫_𝕜 := by
        rw [← hA (X (hB.eigenvectorBasis rfl j))
          (hA.eigenvectorBasis rfl i)]
      _ = ⟪A (X (hB.eigenvectorBasis rfl j)) -
          X (B (hB.eigenvectorBasis rfl j)),
            hA.eigenvectorBasis rfl i⟫_𝕜 := by
        rw [inner_sub_left]
      _ = _ := congrArg
        (fun z : F => ⟪z, hA.eigenvectorBasis rfl i⟫_𝕜) hpoint
  simpa only [hA.apply_eigenvectorBasis rfl i,
    hB.apply_eigenvectorBasis rfl j, map_smul, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, sub_mul] using hinner

/-- Restrict scalars on the Sylvester map space from `𝕜` to `ℝ` so the
barycentric theorem can state real convex-hull membership.

Proof strategy:

1. compose the existing `𝕜` action with `algebraMap ℝ 𝕜`;
2. keep the instance file-local rather than exporting a second global module
   structure;
3. leave the real-to-`𝕜` coefficient conversion to an explicit definitional
   `change` in the downstream certificate extraction theorem, avoiding an
   unnecessary and fragile `IsScalarTower` instance. -/
local instance realModuleSylvesterMap : Module ℝ (E →ₗ[𝕜] F) :=
  Module.compHom (E →ₗ[𝕜] F) (algebraMap ℝ 𝕜)

/-- **Analytic Ky Fan root of the finite `π/2` front.**  Every singular-value
prefix of a separated self-adjoint Sylvester solution satisfies the
Bhatia--Davis--McIntosh estimate.

This is the weakest field-uniform analytic seam.  A Fourier or equivalent
reciprocal-multiplier proof should establish this theorem directly.  The
operator-valued barycenter, exact finite certificate, arbitrary unitarily
invariant norm, residual, and perturbation statements are formal consequences.

The preferred proof route is:

1. diagonalize `A` and `B` and use
   `sylvester_eigenbasis_coefficient_equation` to identify `X` with the
   reciprocal Schur multiplier applied to `C`;
2. prove the finite reciprocal-multiplier estimate with constant `π / 2` for
   each Ky Fan prefix;
3. keep the argument field-uniform at the singular-value level, so the real
   case needs no separate descent from a complex operator-valued integral.

This statement deliberately contains no convex-hull or finite-certificate
bookkeeping. -/
theorem kyFan_sylvester_le_of_spectralDistance_analytic
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (α := hA.eigenvalues rfl)
    (β := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    exact sylvester_eigenbasis_coefficient_equation hA hB hEq i j

/-- The scaled solution of a separated self-adjoint Sylvester equation is a
bounded-mass multiple of a point in the real convex hull of the two-sided
unitary orbit of the defect.

The analytic work is exactly the simultaneous Ky Fan estimate above.  The
rectangular orbit-convexity theorem then converts weak singular-value
majorization into real convex-hull membership uniformly over `ℝ` and `ℂ`.
This avoids placing Fourier integration, phase absorption, normalization, or a
separate real-field descent inside the barycentric theorem.

We choose the maximal allowed mass `p = π / 2` and normalize
`Y = p⁻¹ • (δ • X)`.  Positive homogeneity and the analytic Ky Fan estimate
show every prefix of `Y` is bounded by the corresponding prefix of `C`;
rectangular Fan orbit-convexity gives `Y ∈ conv(orbit(C))`, and the defining
scalar identity recovers `δ • X = p • Y`. -/
theorem sylvester_barycentricOrbitRepresentation_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ Real.pi / 2 ∧
      ∃ Y : E →ₗ[𝕜] F,
        Y ∈ convexHull ℝ
          (RectangularUnitarilyInvariantNorm.twoSidedUnitaryOrbit C) ∧
        (((δ : 𝕜)) • X) = ((m : 𝕜)) • Y := by
  let p : ℝ := Real.pi / 2
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hp0 : 0 ≤ p := le_of_lt hp
  have hpinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  let Y : E →ₗ[𝕜] F := (((p⁻¹ : ℝ) : 𝕜)) • (((δ : 𝕜)) • X)
  refine ⟨p, hp0, le_rfl, Y, ?_, ?_⟩
  · apply
      RectangularUnitarilyInvariantNorm.mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
    intro k
    have hcore :=
      kyFan_sylvester_le_of_spectralDistance_analytic
        hA hB hδ hgap hEq k
    change δ *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      p * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C at hcore
    calc
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k Y =
          p⁻¹ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
            (((δ : 𝕜)) • X) := by
        simpa only [Y] using
          RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k (((δ : 𝕜)) • X) hpinv0
      _ = p⁻¹ *
          (δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X) := by
        rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k X (le_of_lt hδ)]
      _ ≤ p⁻¹ *
          (p * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C) :=
        mul_le_mul_of_nonneg_left hcore hpinv0
      _ = RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
        field_simp [ne_of_gt hp]
  · dsimp [Y]
    rw [smul_smul, ← RCLike.ofReal_mul]
    field_simp [ne_of_gt hp]
    simp
/-- A separated self-adjoint Sylvester equation admits a finite two-sided
unitary-orbit certificate of mass at most `π / 2` for the scaled solution
`δ • X` relative to the defect `C`.

Proof strategy:

1. obtain the bounded-mass convex-hull representation from
   `sylvester_barycentricOrbitRepresentation_of_spectralDistance`;
2. pass it to
   `RectangularUnitarilyInvariantNorm.hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull`;
3. let that generic theorem extract the exact finite convex combination,
   choose unitary factors, compute the coefficient mass, and reindex by
   `Fin n`.

Consequently this theorem contains no Fourier, integration, compactness, or
Carathéodory bookkeeping.  The remaining harmonic analysis is isolated in
`hasReciprocalOrbitInterpolation_pi_div_two`; the reciprocal Ky Fan theorem
and this barycentric theorem are now finite-algebra and orbit-convexity
consequences. -/
theorem sylvester_hasFiniteUnitaryOrbitCertificate_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    RectangularUnitarilyInvariantNorm.HasFiniteUnitaryOrbitCertificate
      (Real.pi / 2) (((δ : 𝕜)) • X) C := by
  rcases sylvester_barycentricOrbitRepresentation_of_spectralDistance
      hA hB hδ hgap hEq with ⟨m, hm, hmass, Y, hY, hXY⟩
  exact
    RectangularUnitarilyInvariantNorm.hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
      hm hmass hY hXY

/-- Every Ky Fan prefix satisfies the arbitrary-disjoint-spectrum Sylvester
bound.  This public theorem is the stable API alias for the analytic root;
the barycentric and finite-certificate layers are downstream consequences,
not proof dependencies. -/
theorem kyFan_sylvester_le_of_spectralDistance
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
  kyFan_sylvester_le_of_spectralDistance_analytic
    hA hB hδ hgap hEq k

/-- General disjoint-spectrum extension with the Bhatia--Davis--McIntosh
constant `π/2`, lifted from the finite orbit certificate through Ky Fan
prefixes and rectangular Fan dominance.

Proof strategy:

1. compare the positively scaled maps `δ • X` and `(π / 2) • C`;
2. use the already proved Ky Fan theorem for every prefix;
3. apply rectangular Fan dominance;
4. rewrite absolute homogeneity only after the prefix comparison is complete.
-/
theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : 𝕜)) • X) ≤ N (((p : 𝕜)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    rw [RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k X hδ0,
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k C hp0]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : 𝕜)) • X) := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_pos hδ]
    _ ≤ N (((p : 𝕜)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-! ### Unconditional field-specific endpoints

The explicit Haagerup--Zsidó kernel closes the analytic root over `ℂ`
directly and over `ℝ` through the doubled orthogonal descent.  The theorems
below repeat the sharp arbitrary-separated-spectrum statements at the two
concrete scalar fields with no open obligation.  The generic `RCLike`
versions above remain routed through the finite orbit-interpolation seam,
which is still an open obligation. -/

/-- Unconditional complex Ky Fan Sylvester estimate. -/
theorem kyFan_sylvester_le_of_spectralDistance_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    {A : FC →ₗ[ℂ] FC} {B : EC →ₗ[ℂ] EC} {X C : EC →ₗ[ℂ] FC}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_complex
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (α := hA.eigenvalues rfl)
    (β := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    exact sylvester_eigenbasis_coefficient_equation hA hB hEq i j

/-- Unconditional real Ky Fan Sylvester estimate. -/
theorem kyFan_sylvester_le_of_spectralDistance_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    {A : FR →ₗ[ℝ] FR} {B : ER →ₗ[ℝ] ER} {X C : ER →ₗ[ℝ] FR}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      (Real.pi / 2) *
        RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  apply kyFan_reciprocalMultiplier_le_real
    (eF := hA.eigenvectorBasis rfl)
    (eE := hB.eigenvectorBasis rfl)
    (alpha := hA.eigenvalues rfl)
    (beta := hB.eigenvalues rfl)
    (X := X) (C := C) hδ
  · intro i j
    exact hgap
      (hA.eigenvalues rfl i) (hB.eigenvalues rfl j)
      (eigenvalue_mem_restrictedSpectrum_top hA i)
      (eigenvalue_mem_restrictedSpectrum_top hB j)
  · intro i j
    have h := sylvester_eigenbasis_coefficient_equation hA hB hEq i j
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h

/-- Unconditional complex arbitrary-UI-norm Sylvester estimate. -/
theorem uiNorm_sylvester_le_of_spectralDistance_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    (N : RectangularUnitarilyInvariantNorm ℂ EC FC)
    {A : FC →ₗ[ℂ] FC} {B : EC →ₗ[ℂ] EC} {X C : EC →ₗ[ℂ] FC}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (((δ : ℂ)) • X) ≤ N (((p : ℂ)) • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    have hX : RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          (((δ : ℂ)) • X) =
        δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X :=
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k X hδ0
    have hC : RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          (((p : ℂ)) • C) =
        p * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C :=
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul k C hp0
    rw [hX, hC]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance_complex hA hB hδ hgap hEq k
  calc
    δ * N X = N (((δ : ℂ)) • X) := by
      rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ N (((p : ℂ)) • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

/-- Unconditional real arbitrary-UI-norm Sylvester estimate. -/
theorem uiNorm_sylvester_le_of_spectralDistance_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    (N : RectangularUnitarilyInvariantNorm ℝ ER FR)
    {A : FR →ₗ[ℝ] FR} {B : ER →ₗ[ℝ] ER} {X C : ER →ₗ[ℝ] FR}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C := by
  let p : ℝ := Real.pi / 2
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hscaled : N (δ • X) ≤ N (p • C) := by
    apply N.apply_le_of_kyFanSum_le
    intro k
    have hX := RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
      (𝕜 := ℝ) k X hδ0
    have hC := RectangularUnitarilyInvariantNorm.rectangularKyFanSum_real_smul
      (𝕜 := ℝ) k C hp0
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hX hC
    rw [hX, hC]
    simpa [p] using
      kyFan_sylvester_le_of_spectralDistance_real hA hB hδ hgap hEq k
  calc
    δ * N X = N (δ • X) := by
      rw [N.smul_eq, Real.norm_eq_abs, abs_of_pos hδ]
    _ ≤ N (p • C) := hscaled
    _ = p * N C := by
      rw [N.smul_eq, Real.norm_eq_abs, abs_of_nonneg hp0]
    _ = (Real.pi / 2) * N C := by rfl

end DavisKahanTheory

namespace DavisKahanExt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Finite-dimensional rectangular unitarily invariant Sylvester estimate.

For self-adjoint `A` and `B` with spectra separated by `d > 0`, every
rectangular unitarily invariant seminorm satisfies
`d * N X ≤ (π / 2) * N C` whenever `A X - X B = C`.

Proof strategy:

1. forget continuity and transport self-adjointness, spectral separation, and
   the Sylvester equation to the finite linear-map API;
2. apply `DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance`, whose proof
   runs through the finite reciprocal-multiplier Ky Fan estimate and
   rectangular Fan dominance;
3. unfold the named linear maps to recover the compatibility signature.

All reciprocal-multiplier analysis, including the sharp `π / 2` constant,
is isolated in
`DavisKahanTheory.hasReciprocalOrbitInterpolation_pi_div_two`.  Coordinate
expansion, singular-value control, the orbit barycenter, and this
continuous-linear-map bridge contain no further analytic argument. -/
theorem ideal_sylvester_le
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (N : DavisKahanTheory.RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : F →ₗ[𝕜] F := A.toLinearMap
  let B' : E →ₗ[𝕜] E := B.toLinearMap
  let X' : E →ₗ[𝕜] F := X.toLinearMap
  let C' : E →ₗ[𝕜] F := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : DavisKahanTheory.SpectraSeparated A' ⊤ B' ⊤ d := by
    intro a b ha hb
    rcases ha with ⟨x, -, ⟨hx0, hxeig⟩⟩
    rcases hb with ⟨y, -, ⟨hy0, hyeig⟩⟩
    exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
      b ⟨y, Submodule.mem_top, hy0, hyeig⟩
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' := by
    ext x
    have hpoint := congrArg (fun T : E →L[𝕜] F => T x) hEq
    simpa [A', B', X', C', sylvesterOperator,
      ContinuousLinearMap.comp_apply] using hpoint
  simpa [X', C'] using
    DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance
      N hA' hB' hd hsep' hEq'

/-- **Unconditional complex sharp Sylvester estimate.**  Identical to
`ideal_sylvester_le` at `𝕜 = ℂ`, but proved through the explicit
Haagerup--Zsidó kernel with no open obligation. -/
theorem ideal_sylvester_le_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    (N : DavisKahanTheory.RectangularUnitarilyInvariantNorm ℂ EC FC)
    {A : FC →L[ℂ] FC} {B : EC →L[ℂ] EC} {X C : EC →L[ℂ] FC}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : FC →ₗ[ℂ] FC := A.toLinearMap
  let B' : EC →ₗ[ℂ] EC := B.toLinearMap
  let X' : EC →ₗ[ℂ] FC := X.toLinearMap
  let C' : EC →ₗ[ℂ] FC := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : DavisKahanTheory.SpectraSeparated A' ⊤ B' ⊤ d := by
    intro a b ha hb
    rcases ha with ⟨x, -, ⟨hx0, hxeig⟩⟩
    rcases hb with ⟨y, -, ⟨hy0, hyeig⟩⟩
    exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
      b ⟨y, Submodule.mem_top, hy0, hyeig⟩
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' := by
    ext x
    have hpoint := congrArg (fun T : EC →L[ℂ] FC => T x) hEq
    simpa [A', B', X', C', sylvesterOperator,
      ContinuousLinearMap.comp_apply] using hpoint
  simpa [X', C'] using
    DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance_complex
      N hA' hB' hd hsep' hEq'

/-- **Unconditional real sharp Sylvester estimate.**  Identical to
`ideal_sylvester_le` at `𝕜 = ℝ`, proved through the doubled orthogonal
descent from the explicit Haagerup--Zsidó kernel. -/
theorem ideal_sylvester_le_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    (N : DavisKahanTheory.RectangularUnitarilyInvariantNorm ℝ ER FR)
    {A : FR →L[ℝ] FR} {B : ER →L[ℝ] ER} {X C : ER →L[ℝ] FR}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : FR →ₗ[ℝ] FR := A.toLinearMap
  let B' : ER →ₗ[ℝ] ER := B.toLinearMap
  let X' : ER →ₗ[ℝ] FR := X.toLinearMap
  let C' : ER →ₗ[ℝ] FR := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : DavisKahanTheory.SpectraSeparated A' ⊤ B' ⊤ d := by
    intro a b ha hb
    rcases ha with ⟨x, -, ⟨hx0, hxeig⟩⟩
    rcases hb with ⟨y, -, ⟨hy0, hyeig⟩⟩
    exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
      b ⟨y, Submodule.mem_top, hy0, hyeig⟩
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' := by
    ext x
    have hpoint := congrArg (fun T : ER →L[ℝ] FR => T x) hEq
    simpa [A', B', X', C', sylvesterOperator,
      ContinuousLinearMap.comp_apply] using hpoint
  simpa [X', C'] using
    DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance_real
      N hA' hB' hd hsep' hEq'

end DavisKahanExt
end ForMathlib
