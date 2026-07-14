/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.Core.All
import ForMathlib.Analysis.InnerProductSpace.SylvesterBound

/-!
# Finite-dimensional Sylvester equations

The Sylvester operator, spectral-separation predicates, injectivity, and the
canonical finite-dimensional solution.
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

/-- Interval/exterior separation in either orientation.  The first branch has
the spectrum of `B` in `[a,b]` and that of `A` outside the enlarged interval;
the second branch reverses those roles. -/
def UnorderedIntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  IntervalSylvesterGap A B a b δ ∨ IntervalSylvesterGap B A a b δ

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

theorem eigenvalue_mem_restrictedSpectrum_top
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) :
    hT.eigenvalues rfl i ∈ restrictedSpectrum T ⊤ :=
  ⟨hT.eigenvectorBasis rfl i, Submodule.mem_top,
    (hT.eigenvectorBasis rfl).orthonormal.ne_zero i,
    hT.apply_eigenvectorBasis rfl i⟩

theorem re_inner_le_of_eigenvalues_le
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

theorem le_re_inner_of_le_eigenvalues
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

theorem opNorm_shift_le_of_spectrumIn_Icc
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

theorem norm_shift_lower_of_spectrumOutside
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


end DavisKahanTheory
end ForMathlib
