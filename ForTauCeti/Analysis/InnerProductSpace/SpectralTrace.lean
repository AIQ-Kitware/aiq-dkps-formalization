/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.SchurHorn
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
public import TauCeti.Analysis.InnerProductSpace.NormalOperator
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Convex.Deriv
public import TauCeti.Analysis.Convex.StrictConvexSpace
public import TauCeti.Analysis.Normed.Module.Trace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Normed.Operator.Mul
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import Mathlib.Algebra.Star.StarProjection

/-!
# Supporting inequalities and first variations of normal spectral traces

A scalar supporting inequality transfers to normal operators by averaging in
two orthonormal eigenbases. The averaging coefficients are the accepted Schur
weights, whose row and column sums are one. This is the finite-dimensional
Klein inequality, with a scalar function on the complex plane rather than only
on the real line.

The eigenbasis form keeps the algebra independent of differentiation. The
continuous-functional-calculus form then supplies the supporting operator
canonically. Applying the inequality in both directions and using continuity
of that supporting operator gives first variations of normal spectral costs,
including displacement powers with zero displacement singular values.
Empty eigenbases are permitted, so no positive-dimension hypothesis is needed.

## Provenance

The scalar-to-trace argument is classical doubly stochastic averaging. The
Schur weights and finite-spectrum functional calculus are consumed from the
accepted Tau Ceti dependency. This module adds the complex normal-operator
supporting inequality; it makes no claim of mathematical novelty.
-/

public section

noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace TauCeti

section NormPower

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The tangent inequality for a power of the Hilbert norm, valid also at
the zero vector. Restricting the accepted convex norm power to the affine
line from `x` to `y` reduces the assertion to the one-variable secant bound. -/
theorem norm_rpow_support (p : ℝ) (hp : 1 < p) (x y : F) :
    ‖x‖ ^ p + p * ‖x‖ ^ (p - 2) * ⟪x, y - x⟫_ℝ ≤ ‖y‖ ^ p := by
  have hconv : ConvexOn ℝ Set.univ fun t : ℝ => ‖AffineMap.lineMap x y t‖ ^ p := by
    simpa only [Set.preimage_univ, Function.comp_def] using!
      (convexOn_norm_rpow (E := F) hp.le).comp_affineMap (AffineMap.lineMap x y)
  have hd : HasDerivAt (fun t : ℝ => ‖AffineMap.lineMap x y t‖ ^ p)
      (p * ‖x‖ ^ (p - 2) * ⟪x, y - x⟫_ℝ) 0 := by
    have hdline : HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ) :=
      AffineMap.hasDerivAt_lineMap
    have hnorm : HasFDerivAt (fun z : F => ‖z‖ ^ p)
        ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) (AffineMap.lineMap x y (0 : ℝ)) := by
      simpa only [AffineMap.lineMap_apply_zero] using hasFDerivAt_norm_rpow x hp
    have h := hnorm.comp_hasDerivAt (0 : ℝ) hdline
    simpa only [AffineMap.lineMap_apply_zero, smul_apply,
      innerSL_apply_apply, smul_eq_mul, Function.comp_def] using! h
  have h := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one hd
  simp only [slope_def_field, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at h
  linarith

/-- The gradient of a Hilbert norm power is continuous, including at zero
when `1 < p < 2`. Transport the accepted continuous Fréchet derivative through
the Riesz isometry, avoiding a separate limit for its singular coefficient. -/
theorem continuous_norm_rpow_gradient [CompleteSpace F] (p : ℝ) (hp : 1 < p) :
    Continuous (fun x : F => (p * ‖x‖ ^ (p - 2)) • x) := by
  have hrepr (x : F) : InnerProductSpace.toDual ℝ F ((p * ‖x‖ ^ (p - 2)) • x) =
      fderiv ℝ (fun z : F => ‖z‖ ^ p) x := by
    rw [fderiv_norm_rpow x hp]
    ext y
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  have hc := (InnerProductSpace.toDual ℝ F).symm.continuous.comp
    ((contDiff_norm_rpow (E := F) hp).continuous_fderiv one_ne_zero)
  convert hc using 1
  ext x
  apply (InnerProductSpace.toDual ℝ F).injective
  rw [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply, hrepr]

end NormPower

/-- The complex scalar support for the displacement norm power. This uses
the real Hilbert-space tangent inequality and keeps the complex gradient in
the form consumed by the normal functional calculus. -/
theorem norm_sub_one_rpow_support (p : ℝ) (hp : 1 < p) (z w : ℂ) :
    ‖z - 1‖ ^ p +
        (conj (((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) * (w - z)).re ≤
      ‖w - 1‖ ^ p := by
  have h := norm_rpow_support p hp (z - 1) (w - 1)
  rw [show (w - 1) - (z - 1) = w - z by ring, real_inner_eq_re_inner ℂ,
    RCLike.inner_apply'] at h
  have hre (r : ℝ) (u : ℂ) : RCLike.re ((r : ℂ) * u) = r * RCLike.re u := by
    change ((r : ℂ) * u).re = r * u.re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change ‖z - 1‖ ^ p +
    RCLike.re (conj (((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) * (w - z)) ≤ _
  simpa only [map_mul, Complex.conj_ofReal, mul_assoc, hre] using h

/-- The scalar supporting field of the displacement power is continuous
for every exponent greater than one, including at the identity. -/
theorem continuous_norm_sub_one_rpow_gradient (p : ℝ) (hp : 1 < p) :
    Continuous (fun z : ℂ => ((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) := by
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, RCLike.real_smul_eq_coe_mul] using!
    (continuous_norm_rpow_gradient (F := ℂ) p hp).comp
      (continuous_id.sub continuous_const)

section LinearSupport

open Filter Asymptotics
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous family of linear supports determines the derivative along
a differentiable curve. The values need only be supported along the curve;
the feasible set need not contain a neighborhood in the ambient Banach space.
This distinction permits applications to normal and unitary operator curves. -/
theorem hasDerivAt_of_linear_support
    (a : ℝ → F) (L : ℝ → F →L[ℝ] ℝ) (f : ℝ → ℝ) (x : ℝ) (a' : F)
    (ha : HasDerivAt a a' x) (hL : ContinuousAt L x)
    (hsupport : ∀ᶠ t in 𝓝 x,
      L x (a t - a x) ≤ f t - f x ∧ f t - f x ≤ L t (a t - a x)) :
    HasDerivAt f (L x a') x := by
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp ha.isBigO_sub
  have hrem : (fun t => f t - f x - L x (a t - a x)) =o[𝓝 x] fun t => t - x := by
    apply IsLittleO.of_bound
    intro ε hε
    have hclose : ∀ᶠ t in 𝓝 x, ‖L t - L x‖ < ε / C := by
      have hc : Tendsto (fun t => ‖L t - L x‖) (𝓝 x) (𝓝 0) := by
        simpa only [Pi.sub_apply, sub_self, norm_zero] using
          (hL.sub (continuousAt_const (y := L x))).norm.tendsto
      exact hc.eventually (gt_mem_nhds (div_pos hε hC))
    filter_upwards [hsupport, hbound, hclose] with t ht hb hc
    have hr0 : 0 ≤ f t - f x - L x (a t - a x) := sub_nonneg.mpr ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    calc
      _ ≤ (L t - L x) (a t - a x) := by
        change f t - f x - L x (a t - a x) ≤
          L t (a t - a x) - L x (a t - a x)
        exact sub_le_sub_right ht.2 _
      _ ≤ ‖(L t - L x) (a t - a x)‖ := le_abs_self _
      _ ≤ ‖L t - L x‖ * ‖a t - a x‖ := (L t - L x).le_opNorm _
      _ ≤ (ε / C) * (C * ‖t - x‖) :=
        mul_le_mul hc.le hb (norm_nonneg _) (div_nonneg hε.le hC.le)
      _ = ε * ‖t - x‖ := by field_simp
  have hlin := (L x).hasFDerivAt.comp_hasDerivAt x ha
  apply HasDerivAt.of_isLittleO
  convert hrem.add hlin.isLittleO using 1
  ext t
  simp only [map_sub, smul_eq_mul, Function.comp_def]
  ring

end LinearSupport

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι] [Fintype κ]

/-- In an orthonormal eigenbasis, the diagonal of an operator in any unit
vector is the Schur-weighted average of its eigenvalues. The complex-valued
identity retains the imaginary part needed for normal spectral costs. -/
theorem inner_apply_eq_sum_schurWeight_mul
    (v : OrthonormalBasis ι ℂ E) (e : OrthonormalBasis κ ℂ E)
    (T : E →ₗ[ℂ] E) (mu : ι → ℂ) (hmu : ∀ i, T (v i) = mu i • v i) (k : κ) :
    ⟪e k, T (e k)⟫_ℂ = ∑ i, (v.schurWeight e i k : ℂ) * mu i := by
  have himage : T (e k) = ∑ i, (v.repr (e k) i * mu i) • v i := by
    calc
      T (e k) = T (∑ i, v.repr (e k) i • v i) := by rw [v.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, hmu, smul_smul]
  rw [himage, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmul : v.repr (e k) i * ⟪e k, v i⟫_ℂ = (v.schurWeight e i k : ℂ) := by
    rw [v.repr_apply_apply, ← inner_conj_symm (e k) (v i), Complex.mul_conj,
      Complex.normSq_eq_norm_sq, OrthonormalBasis.schurWeight_apply]
  rw [inner_smul_right]
  calc
    (v.repr (e k) i * mu i) * ⟪e k, v i⟫_ℂ =
        (v.repr (e k) i * ⟪e k, v i⟫_ℂ) * mu i := by ring
    _ = _ := by rw [hmul]

variable [FiniteDimensional ℂ E]

/-- **Klein's supporting inequality for normal spectral sums.** A scalar
support at each eigenvalue of `S` transfers to the trace pairing with its
diagonal supporting operator `G`. The proof multiplies each scalar inequality
by a Schur weight and sums; it does not require differentiable eigenvectors. -/
theorem spectral_sum_support
    (v : OrthonormalBasis ι ℂ E) (e : OrthonormalBasis κ ℂ E)
    (S T G : E →ₗ[ℂ] E) (mu : ι → ℂ) (nu : κ → ℂ)
    (hS : ∀ i, S (v i) = mu i • v i)
    (hT : ∀ j, T (e j) = nu j • e j)
    (f : ℂ → ℝ) (g : ℂ → ℂ)
    (hG : ∀ i, G (v i) = g (mu i) • v i)
    (hsupport : ∀ i j, f (mu i) + (conj (g (mu i)) * (nu j - mu i)).re ≤ f (nu j)) :
    (∑ i, f (mu i)) +
        (LinearMap.trace ℂ E (G.adjoint * (T - S))).re ≤ ∑ j, f (nu j) := by
  classical
  have htrace : (LinearMap.trace ℂ E (G.adjoint * (T - S))).re =
      ∑ i, ∑ j, e.schurWeight v j i *
        (conj (g (mu i)) * (nu j - mu i)).re := by
    rw [LinearMap.trace_eq_sum_inner _ v, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hdiag := inner_apply_eq_sum_schurWeight_mul e v T nu hT i
    have hweight : ∑ j, (e.schurWeight v j i : ℂ) = 1 := by
      rw [← Complex.ofReal_sum, e.sum_schurWeight_col v, Complex.ofReal_one]
    have hv : ⟪v i, v i⟫_ℂ = 1 := v.inner_eq_one i
    simp only [Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.adjoint_inner_right, hG, inner_smul_left, inner_sub_right,
      hS, inner_smul_right, hv, mul_one]
    rw [hdiag]
    calc
      (conj (g (mu i)) * (∑ j, (e.schurWeight v j i : ℂ) * nu j) -
          mu i * conj (g (mu i))).re =
          (conj (g (mu i)) * ((∑ j, (e.schurWeight v j i : ℂ) * nu j) - mu i)).re := by
        congr 1
        ring
      _ =
          (∑ j, (e.schurWeight v j i : ℂ) *
            (conj (g (mu i)) * (nu j - mu i))).re := by
        congr 1
        calc
          _ = conj (g (mu i)) *
              (∑ j, (e.schurWeight v j i : ℂ) * (nu j - mu i)) := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweight, one_mul]
          _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = _ := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [htrace, ← Finset.sum_add_distrib]
  have hbound : ∀ i,
      f (mu i) + ∑ j, e.schurWeight v j i *
          (conj (g (mu i)) * (nu j - mu i)).re ≤
        ∑ j, e.schurWeight v j i * f (nu j) := by
    intro i
    calc
      _ = ∑ j, e.schurWeight v j i *
          (f (mu i) + (conj (g (mu i)) * (nu j - mu i)).re) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
          e.sum_schurWeight_col v, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hsupport i j) (e.schurWeight_nonneg v j i)
  calc
    _ ≤ ∑ i, ∑ j, e.schurWeight v j i * f (nu j) :=
      Finset.sum_le_sum fun i _ => hbound i
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, e.sum_schurWeight_row v, one_mul]

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- The finite complex trace is faithful on positive squares. The accepted
Frobenius trace identity turns the hypothesis into a sum of squared column
norms, each of which must vanish. -/
theorem eq_zero_of_re_trace_adjoint_mul_self_eq_zero
    (A : E →L[ℂ] E)
    (h : (LinearMap.trace ℂ E (A.adjoint * A).toLinearMap).re = 0) : A = 0 := by
  classical
  let b := stdOrthonormalBasis ℂ E
  have htrace : (LinearMap.trace ℂ E (A.adjoint * A).toLinearMap).re =
      ∑ i, ‖A (b i)‖ ^ 2 := by
    rw [_root_.ContinuousLinearMap.toLinearMap_mul,
      ← _root_.ContinuousLinearMap.adjoint_toLinearMap, Module.End.mul_eq_comp,
      A.toLinearMap.trace_adjoint_comp_self_eq_sum_norm_apply_sq b]
    exact RCLike.ofReal_re (K := ℂ) _
  rw [htrace] at h
  have hA : A.toLinearMap = 0 := by
    apply b.toBasis.ext
    intro i
    change A (b i) = 0
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A (b j)‖)).mp h i
        (Finset.mem_univ i))
  ext x
  change A.toLinearMap x = 0
  rw [hA]
  rfl

/-- Orthogonality in the trace pairing to every Hermitian element of a
projection's commutant forces its diagonal compression to vanish. Testing
against `P G P` reduces the assertion to faithfulness of the trace square. -/
theorem projection_compression_eq_zero_of_trace_pairing_eq_zero
    (G P : E →L[ℂ] E) (hG : IsSelfAdjoint G) (hP : IsStarProjection P)
    (hzero : ∀ H : E →L[ℂ] E, IsSelfAdjoint H → Commute H P →
      (LinearMap.trace ℂ E (G * H).toLinearMap).re = 0) : P * G * P = 0 := by
  let H := P * G * P
  have hHs : IsSelfAdjoint H := hG.conjugate_self hP.isSelfAdjoint
  have hPP : P * P = P := hP.isIdempotentElem
  have hHP : H * P = H := by
    dsimp [H]
    rw [mul_assoc (P * G) P P, hPP]
  have hPH : P * H = H := by
    dsimp [H]
    calc
      P * (P * G * P) = (P * P) * G * P := by simp only [mul_assoc]
      _ = _ := by rw [hPP]
  have hcomm : Commute H P := hHP.trans hPH.symm
  apply eq_zero_of_re_trace_adjoint_mul_self_eq_zero H
  have htrace : LinearMap.trace ℂ E (H.adjoint * H).toLinearMap =
      LinearMap.trace ℂ E (G * H).toLinearMap := by
    calc
      _ = LinearMap.trace ℂ E (H * H).toLinearMap := by
        rw [← _root_.ContinuousLinearMap.star_eq_adjoint, hHs.star_eq]
      _ = LinearMap.trace ℂ E (P * (G * H)).toLinearMap := by
        have heq : H * H = P * (G * H) := by
          change (P * G * P) * H = P * (G * H)
          rw [mul_assoc, mul_assoc, hPH]
        rw [heq]
      _ = LinearMap.trace ℂ E ((G * H) * P).toLinearMap := by
        simp only [_root_.ContinuousLinearMap.toLinearMap_mul]
        exact LinearMap.trace_mul_comm ℂ P.toLinearMap (G.toLinearMap * H.toLinearMap)
      _ = LinearMap.trace ℂ E (G * H).toLinearMap := by
        rw [mul_assoc, hHP]
  rw [htrace]
  exact hzero H hHs hcomm

/-- Forgetting continuity preserves normality of a finite-dimensional
operator. This representation bridge uses the accepted adjoint comparison. -/
theorem isStarNormal_toLinearMap (A : E →L[ℂ] E) [IsStarNormal A] :
    IsStarNormal A.toLinearMap := by
  constructor
  change A.toLinearMap.adjoint * A.toLinearMap = A.toLinearMap * A.toLinearMap.adjoint
  rw [_root_.ContinuousLinearMap.adjoint_toLinearMap,
    ← _root_.ContinuousLinearMap.toLinearMap_mul,
    ← _root_.ContinuousLinearMap.toLinearMap_mul]
  exact congrArg _root_.ContinuousLinearMap.toLinearMap
    (show A.adjoint * A = A * A.adjoint from star_comm_self' A)

/-- The complex continuous functional calculus acts on a normal operator's
eigenvectors by applying its symbol to the eigenvalue. Finite spectrum permits
an arbitrary symbol, including one whose global continuity is not available. -/
theorem cfc_apply_of_apply_eq_smul_of_isStarNormal
    (f : ℂ → ℂ) {T : E →L[ℂ] E} [IsStarNormal T] {x : E} {mu : ℂ}
    (hx : T x = mu • x) : cfc f T x = f mu • x := by
  have halg (z : ℂ) : algebraMap ℂ (E →L[ℂ] E) z • x = z • x := by
    rw [_root_.ContinuousLinearMap.smul_def, _root_.ContinuousLinearMap.algebraMap_apply]
  rw [← _root_.ContinuousLinearMap.smul_def, ← halg] at hx ⊢
  exact cfc_smul_of_smul_eq_algebraMap_smul f (T.finite_spectrum ℂ) hx

/-- The real trace of the functional calculus of a real-valued symbol is its
sum over any orthonormal eigenbasis, with multiplicity. -/
theorem re_trace_cfc_eq_sum
    (f : ℂ → ℝ) (T : E →L[ℂ] E) [IsStarNormal T]
    (v : OrthonormalBasis ι ℂ E) (mu : ι → ℂ)
    (hmu : ∀ i, T (v i) = mu i • v i) :
    (LinearMap.trace ℂ E (cfc (fun z => (f z : ℂ)) T).toLinearMap).re =
      ∑ i, f (mu i) := by
  rw [LinearMap.trace_eq_sum_inner _ v, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (⟪v i, cfc (fun z => (f z : ℂ)) T (v i)⟫_ℂ).re = _
  rw [cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hmu i), inner_smul_right,
    v.inner_eq_one, mul_one, Complex.ofReal_re]

/-- A scalar supporting inequality transfers to traces of the continuous
functional calculus. The supplied eigenbases may have different finite index
types. Its gradient is the canonical functional-calculus operator `cfc g S`. -/
theorem re_trace_cfc_support_of_eigenbases
    (f : ℂ → ℝ) (g : ℂ → ℂ)
    (S T : E →L[ℂ] E) [IsStarNormal S] [IsStarNormal T]
    (v : OrthonormalBasis ι ℂ E) (e : OrthonormalBasis κ ℂ E)
    (mu : ι → ℂ) (nu : κ → ℂ)
    (hS : ∀ i, S (v i) = mu i • v i)
    (hT : ∀ j, T (e j) = nu j • e j)
    (hsupport : ∀ i j, f (mu i) + (conj (g (mu i)) * (nu j - mu i)).re ≤ f (nu j)) :
    (LinearMap.trace ℂ E (cfc (fun z => (f z : ℂ)) S).toLinearMap).re +
        (LinearMap.trace ℂ E ((cfc g S).adjoint * (T - S)).toLinearMap).re ≤
      (LinearMap.trace ℂ E (cfc (fun z => (f z : ℂ)) T).toLinearMap).re := by
  rw [re_trace_cfc_eq_sum f S v mu hS, re_trace_cfc_eq_sum f T e nu hT]
  have hG (i : ι) : (cfc g S).toLinearMap (v i) = g (mu i) • v i :=
    cfc_apply_of_apply_eq_smul_of_isStarNormal g (hS i)
  convert spectral_sum_support v e S.toLinearMap T.toLinearMap
    (cfc g S).toLinearMap mu nu hS hT f g hG hsupport using 1
  rw [_root_.ContinuousLinearMap.toLinearMap_mul,
    _root_.ContinuousLinearMap.toLinearMap_sub,
    _root_.ContinuousLinearMap.adjoint_toLinearMap]

/-- **Klein's inequality for complex normal operators**, expressed without
chosen eigenbases. The scalar supporting inequality is needed only for the
two spectra. This is the form used along curves of unitary operators. -/
theorem re_trace_cfc_support
    (f : ℂ → ℝ) (g : ℂ → ℂ)
    (S T : E →L[ℂ] E) [IsStarNormal S] [IsStarNormal T]
    (hsupport : ∀ z ∈ spectrum ℂ S, ∀ w ∈ spectrum ℂ T,
      f z + (conj (g z) * (w - z)).re ≤ f w) :
    (LinearMap.trace ℂ E (cfc (fun z => (f z : ℂ)) S).toLinearMap).re +
        (LinearMap.trace ℂ E ((cfc g S).adjoint * (T - S)).toLinearMap).re ≤
      (LinearMap.trace ℂ E (cfc (fun z => (f z : ℂ)) T).toLinearMap).re := by
  let := isStarNormal_toLinearMap S
  let := isStarNormal_toLinearMap T
  obtain ⟨v, mu, hS⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal S.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  obtain ⟨e, nu, hT⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal T.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  apply re_trace_cfc_support_of_eigenbases f g S T v e mu nu hS hT
  intro i j
  apply hsupport
  · rw [_root_.ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨by simpa only [Module.End.mem_eigenspace_iff] using hS i,
          v.orthonormal.ne_zero i⟩).mem_spectrum
  · rw [_root_.ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨by simpa only [Module.End.mem_eigenspace_iff] using hT j,
          e.orthonormal.ne_zero j⟩).mem_spectrum

/-- **First variation of a supported normal spectral trace.** A continuous
scalar supporting field on a common compact spectral set gives the derivative
along any differentiable curve of normal operators. The proof uses Klein's
inequality in both directions and continuity of the accepted functional
calculus. Eigenvalues may collide, and the symbol need not be twice smooth. -/
theorem hasDerivAt_re_trace_cfc
    (f : ℂ → ℝ) (g : ℂ → ℂ) (s : Set ℂ) (hs : IsCompact s)
    (hg : ContinuousOn g s)
    (hsupport : ∀ z ∈ s, ∀ w ∈ s, f z + (conj (g z) * (w - z)).re ≤ f w)
    (a : ℝ → E →L[ℂ] E) (x : ℝ) (a' : E →L[ℂ] E)
    (ha : HasDerivAt a a' x) (hnormal : ∀ t, IsStarNormal (a t))
    (hspectrum : ∀ t, spectrum ℂ (a t) ⊆ s) :
    HasDerivAt
      (fun t => (LinearMap.trace ℂ E (cfc (fun z => (f z : ℂ)) (a t)).toLinearMap).re)
      (LinearMap.trace ℂ E ((cfc g (a x)).adjoint * a').toLinearMap).re x := by
  let tr : (E →L[ℂ] E) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((traceCLM ℂ E).restrictScalars ℝ)
  let L : ℝ → (E →L[ℂ] E) →L[ℝ] ℝ := fun t =>
    tr.comp (_root_.ContinuousLinearMap.mul ℝ (E →L[ℂ] E) (star (cfc g (a t))))
  have hL_apply (t : ℝ) (B : E →L[ℂ] E) :
      L t B = (LinearMap.trace ℂ E ((cfc g (a t)).adjoint * B).toLinearMap).re := by
    simp only [L, tr, _root_.ContinuousLinearMap.comp_apply,
      _root_.ContinuousLinearMap.mul_apply', Complex.reCLM_apply,
      _root_.ContinuousLinearMap.star_eq_adjoint]
    exact congrArg Complex.re (traceCLM_apply _)
  have hG : ContinuousAt (fun t => cfc g (a t)) x := by
    rw [← continuousWithinAt_univ]
    exact (continuousOn_cfc (E →L[ℂ] E) hs g hg (a x)
      ⟨hnormal x, hspectrum x⟩).comp ha.continuousAt.continuousWithinAt
        (fun t _ => ⟨hnormal t, hspectrum t⟩)
  have hL : ContinuousAt L x :=
    continuousAt_const.clm_comp
      ((_root_.ContinuousLinearMap.mul ℝ (E →L[ℂ] E)).continuous.continuousAt.comp hG.star)
  rw [← hL_apply]
  apply hasDerivAt_of_linear_support a L _ x a' ha hL
  apply Filter.Eventually.of_forall
  intro t
  let := hnormal x
  let := hnormal t
  have hlo := re_trace_cfc_support f g (a x) (a t)
    (fun z hz w hw => hsupport z (hspectrum x hz) w (hspectrum t hw))
  have hhi := re_trace_cfc_support f g (a t) (a x)
    (fun z hz w hw => hsupport z (hspectrum t hz) w (hspectrum x hw))
  rw [← hL_apply] at hlo hhi
  rw [show a x - a t = -(a t - a x) by abel, map_neg] at hhi
  exact ⟨by linarith, by linarith⟩

/-- The displacement power has a first variation along normal curves for
every exponent above one. This includes `1 < p < 2` and eigenvalue `1`, where
the displacement vanishes and a second derivative may fail to exist. -/
theorem hasDerivAt_re_trace_cfc_norm_sub_one_rpow
    (p : ℝ) (hp : 1 < p) (s : Set ℂ) (hs : IsCompact s)
    (a : ℝ → E →L[ℂ] E) (x : ℝ) (a' : E →L[ℂ] E)
    (ha : HasDerivAt a a' x) (hnormal : ∀ t, IsStarNormal (a t))
    (hspectrum : ∀ t, spectrum ℂ (a t) ⊆ s) :
    HasDerivAt
      (fun t => (LinearMap.trace ℂ E
        (cfc (fun z => ((‖z - 1‖ ^ p : ℝ) : ℂ)) (a t)).toLinearMap).re)
      (LinearMap.trace ℂ E
        ((cfc (fun z => ((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1))
          (a x)).adjoint * a').toLinearMap).re x :=
  hasDerivAt_re_trace_cfc (fun z => ‖z - 1‖ ^ p)
    (fun z => ((p * ‖z - 1‖ ^ (p - 2) : ℝ) : ℂ) * (z - 1)) s hs
    (continuous_norm_sub_one_rpow_gradient p hp).continuousOn
    (fun z _ w _ => norm_sub_one_rpow_support p hp z w)
    a x a' ha hnormal hspectrum

end ContinuousLinearMap

end TauCeti
