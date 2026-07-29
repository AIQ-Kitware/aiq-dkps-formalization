/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.Real.SpectralBridge
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Complexification of real Hilbert spaces

This file supplies the concrete complexification foundation needed to reuse the
complex operator-angle and spectral calculus for real Hilbert spaces.

For a real Hilbert space `E`, its complexification is the L2 product `E × E`.
The pair `(x, y)` represents `x + i y`, with complex scalar multiplication

`(a + i b) • (x + i y) = (a x - b y) + i (b x + a y)`.

The complex inner product is

`⟪(x,y),(u,v)⟫ = (⟪x,u⟫ + ⟪y,v⟫) + i (⟪x,v⟫ - ⟪y,u⟫)`.

The construction includes:

* the canonical isometric real-linear embedding `ofReal`;
* complex conjugation as a real-linear isometric involution;
* complexification of bounded real-linear operators;
* preservation of zero, identity, addition, subtraction, scalar multiplication,
  and composition;
* exact preservation of operator norm;
* reflection of equality and transport of symmetry.

No unbounded-operator, spectral-cutoff, or Ky Fan file depends on this module.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Foundation

open scoped InnerProductSpace ComplexConjugate

noncomputable section

/-- The complexification of a real normed space, represented by its real and
imaginary coordinates with the L2 product norm. -/
def RealComplexification (E : Type*) := WithLp 2 (E × E)

namespace RealComplexification

variable {E F G : Type*}

instance instAddCommGroup [AddCommGroup E] :
    AddCommGroup (RealComplexification E) :=
  inferInstanceAs (AddCommGroup (WithLp 2 (E × E)))

instance instNormedAddCommGroup [NormedAddCommGroup E] :
    NormedAddCommGroup (RealComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance instCompleteSpace [NormedAddCommGroup E] [CompleteSpace E] :
    CompleteSpace (RealComplexification E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

instance instSMulReal [SMul ℝ E] : SMul ℝ (RealComplexification E) :=
  inferInstanceAs (SMul ℝ (WithLp 2 (E × E)))

instance instModuleReal [AddCommGroup E] [Module ℝ E] :
    Module ℝ (RealComplexification E) :=
  inferInstanceAs (Module ℝ (WithLp 2 (E × E)))

instance instNormedSpaceReal [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (RealComplexification E) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (E × E)))

/-- Construct a complexified vector from its real and imaginary coordinates. -/
def mk (x y : E) : RealComplexification E :=
  WithLp.toLp 2 (x, y)

/-- The real coordinate of a complexified vector. -/
def re (z : RealComplexification E) : E :=
  (WithLp.ofLp z).1

/-- The imaginary coordinate of a complexified vector. -/
def im (z : RealComplexification E) : E :=
  (WithLp.ofLp z).2

@[simp] theorem re_mk (x y : E) : re (mk x y) = x := rfl
@[simp] theorem im_mk (x y : E) : im (mk x y) = y := rfl
@[simp] theorem mk_re_im (z : RealComplexification E) : mk (re z) (im z) = z := by
  exact WithLp.toLp_ofLp 2 z

@[ext]
theorem ext {z w : RealComplexification E} (hre : re z = re w) (him : im z = im w) : z = w := by
  apply WithLp.ofLp_injective
  exact Prod.ext hre him

@[simp] theorem re_zero [AddCommGroup E] : re (0 : RealComplexification E) = 0 := rfl
@[simp] theorem im_zero [AddCommGroup E] : im (0 : RealComplexification E) = 0 := rfl
@[simp] theorem re_add [AddCommGroup E] (z w : RealComplexification E) :
    re (z + w) = re z + re w := rfl
@[simp] theorem im_add [AddCommGroup E] (z w : RealComplexification E) :
    im (z + w) = im z + im w := rfl
@[simp] theorem re_neg [AddCommGroup E] (z : RealComplexification E) :
    re (-z) = -re z := rfl
@[simp] theorem im_neg [AddCommGroup E] (z : RealComplexification E) :
    im (-z) = -im z := rfl
@[simp] theorem re_sub [AddCommGroup E] (z w : RealComplexification E) :
    re (z - w) = re z - re w := rfl
@[simp] theorem im_sub [AddCommGroup E] (z w : RealComplexification E) :
    im (z - w) = im z - im w := rfl
@[simp] theorem re_real_smul [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (z : RealComplexification E) : re (r • z) = r • re z := rfl
@[simp] theorem im_real_smul [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (z : RealComplexification E) : im (r • z) = r • im z := rfl

/-- Complex scalar multiplication on the real L2 product. -/
instance instSMulComplex [AddCommGroup E] [Module ℝ E] :
    SMul ℂ (RealComplexification E) where
  smul c z := mk (c.re • re z - c.im • im z) (c.im • re z + c.re • im z)

@[simp] theorem re_complex_smul [AddCommGroup E] [Module ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    re (c • z) = c.re • re z - c.im • im z := rfl

@[simp] theorem im_complex_smul [AddCommGroup E] [Module ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    im (c • z) = c.im • re z + c.re • im z := rfl

instance instModuleComplex [AddCommGroup E] [Module ℝ E] :
    Module ℂ (RealComplexification E) :=
  Module.ofMinimalAxioms
    (fun c z w => by
      apply RealComplexification.ext <;>
        simp [smul_add, sub_eq_add_neg] <;> abel)
    (fun c d z => by apply RealComplexification.ext <;> simp [add_smul, sub_eq_add_neg] <;> module)
    (fun c d z => by
      apply RealComplexification.ext <;>
        simp [sub_eq_add_neg, Complex.mul_re, Complex.mul_im] <;> module)
    (fun z => by apply RealComplexification.ext <;> simp)

instance instIsScalarTower [AddCommGroup E] [Module ℝ E] :
    IsScalarTower ℝ ℂ (RealComplexification E) where
  smul_assoc r c z := by
    apply RealComplexification.ext
    · simp only [re_complex_smul, re_real_smul, Complex.smul_re, Complex.smul_im,
        smul_sub, smul_smul, smul_eq_mul]
    · simp only [im_complex_smul, im_real_smul, Complex.smul_re, Complex.smul_im,
        smul_add, smul_smul, smul_eq_mul]

/-- The squared L2 norm is the sum of the squared coordinate norms. -/
theorem norm_sq [NormedAddCommGroup E] (z : RealComplexification E) :
    ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 z

/-- Complex scalar multiplication scales the L2 norm exactly. -/
theorem norm_complex_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    ‖c • z‖ = ‖c‖ * ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [norm_sq (c • z), mul_pow, norm_sq z]
  simp only [re_complex_smul, im_complex_smul]
  rw [norm_sub_sq (𝕜 := ℝ), norm_add_sq (𝕜 := ℝ)]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
    real_inner_smul_right, Complex.sq_norm, Complex.normSq_apply]
  have hsq (a b : ℝ) : (|a| * b) ^ 2 = a ^ 2 * b ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [hsq c.re ‖re z‖, hsq c.im ‖im z‖,
    hsq c.im ‖re z‖, hsq c.re ‖im z‖]
  ring

instance instNormedSpaceComplex [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    NormedSpace ℂ (RealComplexification E) :=
  { (instModuleComplex (E := E)) with
    norm_smul_le := fun c z => (norm_complex_smul c z).le }

/-- The canonical complex inner product on a real Hilbert-space complexification. -/
instance instInnerProductSpaceComplex [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    InnerProductSpace ℂ (RealComplexification E) where
  inner z w :=
    ⟨⟪re z, re w⟫_ℝ + ⟪im z, im w⟫_ℝ,
      ⟪re z, im w⟫_ℝ - ⟪im z, re w⟫_ℝ⟩
  norm_sq_eq_re_inner z := by
    rw [norm_sq]
    simp []
  conj_inner_symm z w := by
    apply Complex.ext <;> simp [real_inner_comm]
  add_left z w u := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring_nf
  smul_left z w c := by
    apply Complex.ext <;>
      simp [inner_add_left, inner_sub_left, real_inner_smul_left,
        Complex.mul_re, Complex.mul_im] <;> ring

@[simp]
theorem inner_apply [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : RealComplexification E) :
    ⟪z, w⟫_ℂ =
      ⟨⟪re z, re w⟫_ℝ + ⟪im z, im w⟫_ℝ,
        ⟪re z, im w⟫_ℝ - ⟪im z, re w⟫_ℝ⟩ :=
  rfl

/-- The canonical embedding of a real Hilbert space into its complexification. -/
def ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →ₗᵢ[ℝ] RealComplexification E where
  toFun x := mk x 0
  map_add' x y := by apply RealComplexification.ext <;> simp
  map_smul' r x := by apply RealComplexification.ext <;> simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq]
    simp

@[simp] theorem re_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    re (ofReal x) = x := rfl
@[simp] theorem im_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    im (ofReal x) = 0 := rfl
@[simp] theorem inner_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    ⟪ofReal x, ofReal y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) := by
  apply Complex.ext <;> simp

/-- Multiplication by `i` sends the real copy to the imaginary copy. -/
@[simp] theorem I_smul_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    Complex.I • ofReal x = mk 0 x := by
  apply RealComplexification.ext <;> simp

/-- Complex conjugation on the complexification. -/
def conjugation [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    RealComplexification E →ₗᵢ[ℝ] RealComplexification E where
  toFun z := mk (re z) (-im z)
  map_add' z w := by
    apply RealComplexification.ext <;> simp <;> abel
  map_smul' r z := by apply RealComplexification.ext <;> simp
  norm_map' z := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq, norm_sq]
    simp

@[simp] theorem re_conj [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : re (conjugation z) = re z := rfl
@[simp] theorem im_conj [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : im (conjugation z) = -im z := rfl
@[simp] theorem conjugation_involutive [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : conjugation (conjugation z) = z := by
  apply RealComplexification.ext <;> simp
@[simp] theorem conjugation_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    conjugation (ofReal x) = ofReal x := by
  apply RealComplexification.ext <;> simp
@[simp] theorem conjugation_complex_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    conjugation (c • z) = conj c • conjugation z := by
  apply RealComplexification.ext <;> simp [Complex.conj_re, Complex.conj_im] <;> module

/-- Coordinatewise extension of a bounded real-linear operator. -/
def complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : RealComplexification E →L[ℂ] RealComplexification F := by
  let L : RealComplexification E →ₗ[ℂ] RealComplexification F :=
    { toFun := fun z => mk (T (re z)) (T (im z))
      map_add' := fun z w => by apply RealComplexification.ext <;> simp
      map_smul' := fun c z => by apply RealComplexification.ext <;> simp }
  exact L.mkContinuous ‖T‖ (fun z => by
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [norm_sq, mul_pow, norm_sq]
    have hre : ‖T (re z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖re z‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (T.le_opNorm _)
    have him : ‖T (im z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖im z‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (T.le_opNorm _)
    change ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2 ≤
      ‖T‖ ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2)
    nlinarith)

@[simp] theorem re_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (z : RealComplexification E) :
    re (complexify T z) = T (re z) := rfl

@[simp] theorem im_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (z : RealComplexification E) :
    im (complexify T z) = T (im z) := rfl

@[simp] theorem complexify_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (x : E) :
    complexify T (ofReal x) = ofReal (T x) := by
  apply RealComplexification.ext <;> simp

@[simp] theorem complexify_zero [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    complexify (0 : E →L[ℝ] F) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

@[simp] theorem complexify_id [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    complexify (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℂ (RealComplexification E) := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

@[simp] theorem complexify_add [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S T : E →L[ℝ] F) : complexify (S + T) = complexify S + complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

@[simp] theorem complexify_neg [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : complexify (-T) = -complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

@[simp] theorem complexify_sub [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S T : E →L[ℝ] F) : complexify (S - T) = complexify S - complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

@[simp] theorem complexify_real_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (r : ℝ) (T : E →L[ℝ] F) :
    complexify (r • T) = (r : ℂ) • complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext
  · change r • T (re z) =
      (r : ℂ).re • T (re z) - (r : ℂ).im • T (im z)
    simp
  · change r • T (im z) =
      (r : ℂ).im • T (re z) + (r : ℂ).re • T (im z)
    simp

@[simp] theorem complexify_comp [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (S : F →L[ℝ] G) (T : E →L[ℝ] F) :
    complexify (S ∘L T) = complexify S ∘L complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- Complexification preserves operator norm exactly. -/
theorem norm_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : ‖complexify T‖ = ‖T‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [norm_sq, mul_pow, norm_sq]
      have hre : ‖T (re z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖re z‖ ^ 2 := by
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (T.le_opNorm _)
      have him : ‖T (im z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖im z‖ ^ 2 := by
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (T.le_opNorm _)
      change ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2 ≤
        ‖T‖ ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2)
      nlinarith
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    simpa using (complexify T).le_opNorm (ofReal x)

/-- Complexification reflects equality of bounded real operators. -/
theorem complexify_injective [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Function.Injective (complexify : (E →L[ℝ] F) → RealComplexification E →L[ℂ] RealComplexification F) := by
  intro S T h
  apply ContinuousLinearMap.ext
  intro x
  have hx : complexify S (ofReal x) = complexify T (ofReal x) := by rw [h]
  simpa using congrArg re hx

/-- Symmetry of a real operator is equivalent to symmetry of its complexification. -/
theorem complexify_isSymmetric_iff [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    ((complexify T : RealComplexification E →L[ℂ] RealComplexification E) :
      RealComplexification E →ₗ[ℂ] RealComplexification E).IsSymmetric ↔
      (T : E →ₗ[ℝ] E).IsSymmetric := by
  constructor
  · intro h x y
    have hxy := h (ofReal x) (ofReal y)
    simpa [inner_apply] using congrArg Complex.re hxy
  · intro h z w
    apply Complex.ext
    · simp [inner_apply, h]
    · simp [inner_apply, h]

/-- Self-adjointness is preserved and reflected by complexification. -/
theorem complexify_isSelfAdjoint_iff [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) :
    IsSelfAdjoint (complexify T) ↔ IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    complexify_isSymmetric_iff]

end RealComplexification

end

end Foundation
end Experimental
end DavisKahan
end TauCeti