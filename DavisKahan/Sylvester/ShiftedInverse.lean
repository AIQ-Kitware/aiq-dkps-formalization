/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Unbounded.Core

/-!
# Shifted-inverse bounds for closed operators

The one- and two-sided shifted-inverse predicates, the form-bound estimate for a
shifted closed operator, and the resulting operator-norm bounds on the solution
of a closed Sylvester equation in both interval/exterior orientations.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta


open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Bounded left inverse of the shifted operator `A - c` with norm at most
`s⁻¹`: the one-sided resolvent surrogate for "the spectrum of the
self-adjoint `A` avoids `(c - s, c + s)`". -/
def LeftShiftedInverseBound
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (c s : ℝ) : Prop :=
  ∃ J : E →L[𝕜] E,
    (∀ x : A.domain,
      J (A.toLinearMap x - ((c : ℝ) : 𝕜) • (x : E)) = (x : E)) ∧
    ‖J‖ ≤ s⁻¹

/-- Bounded two-sided inverse of the shifted operator `A - c` with norm at
most `s⁻¹`, including the domain transport of the right-inverse leg. -/
def TwoSidedShiftedInverseBound
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (c s : ℝ) : Prop :=
  ∃ J : E →L[𝕜] E, ∃ hdom : ∀ z : E, J z ∈ A.domain,
    (∀ x : A.domain,
      J (A.toLinearMap x - ((c : ℝ) : 𝕜) • (x : E)) = (x : E)) ∧
    (∀ z : E, A.toLinearMap ⟨J z, hdom z⟩ - ((c : ℝ) : 𝕜) • J z = z) ∧
    ‖J‖ ≤ s⁻¹

theorem TwoSidedShiftedInverseBound.leftShiftedInverseBound
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)} {c s : ℝ}
    (h : TwoSidedShiftedInverseBound A c s) :
    LeftShiftedInverseBound A c s := by
  obtain ⟨J, _hdom, hleft, _hright, hnorm⟩ := h
  exact ⟨J, hleft, hnorm⟩

/-! ## Numerical radius controls the norm of a symmetric block -/

/-- A symmetric closed operator whose quadratic form lies in `[β, α]` on its
domain satisfies `‖B y - c y‖ ≤ r ‖y‖` there, where `c = (α+β)/2` is the
center and `r = (α-β)/2` the radius.  Polarization gives the sesquilinear
bound and density of the domain converts it into the norm bound. -/
theorem _root_.ForMathlib.DavisKahanExt.ClosedOperator.norm_shift_apply_le_of_form_bounds
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    (hsym : B.IsSymmetric)
    {β α : ℝ} (hβα : β ≤ α)
    (hlow : SemiboundedBelow B β) (hhigh : SemiboundedAbove B α)
    (u : B.domain) :
    ‖B.toLinearMap u - (((α + β) / 2 : ℝ) : 𝕜) • (u : F)‖ ≤
      (α - β) / 2 * ‖(u : F)‖ := by
  set c : ℝ := (α + β) / 2 with hc
  set r : ℝ := (α - β) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  set S : B.domain → F :=
    fun w => B.toLinearMap w - ((c : ℝ) : 𝕜) • (w : F) with hS
  -- symmetry of the shifted operator
  have hSsym : ∀ v w : B.domain, ⟪S v, (w : F)⟫_𝕜 = ⟪(v : F), S w⟫_𝕜 := by
    intro v w
    simp only [hS, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
    rw [hsym v w]
  -- the quadratic form of the shift lies in `[-r, r]`
  have hform : ∀ w : B.domain,
      |RCLike.re ⟪S w, (w : F)⟫_𝕜| ≤ r * ‖(w : F)‖ ^ 2 := by
    intro w
    have hval : ⟪S w, (w : F)⟫_𝕜 =
        ⟪B.toLinearMap w, (w : F)⟫_𝕜 -
          ((c : ℝ) : 𝕜) * ⟪(w : F), (w : F)⟫_𝕜 := by
      simp only [hS, inner_sub_left, inner_smul_left, RCLike.conj_ofReal]
    have hre : RCLike.re ⟪S w, (w : F)⟫_𝕜 =
        RCLike.re ⟪B.toLinearMap w, (w : F)⟫_𝕜 - c * ‖(w : F)‖ ^ 2 := by
      rw [hval, map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have h1 := hlow w
    have h2 := hhigh w
    rw [hre, abs_le]
    constructor
    · rw [hc, hr] at *
      nlinarith [sq_nonneg ‖(w : F)‖]
    · rw [hc, hr] at *
      nlinarith [sq_nonneg ‖(w : F)‖]
  -- polarization: unnormalized sesquilinear bound
  have hpolar : ∀ v w : B.domain,
      RCLike.re ⟪S v, (w : F)⟫_𝕜 ≤ (r / 2) * (‖(v : F)‖ ^ 2 + ‖(w : F)‖ ^ 2) := by
    intro v w
    have hSadd : S (v + w) = S v + S w := by
      simp only [hS, map_add, Submodule.coe_add, smul_add]
      abel
    have hSsub : S (v - w) = S v - S w := by
      simp only [hS, map_sub, Submodule.coe_sub, smul_sub]
      abel
    have hswap : RCLike.re ⟪S w, (v : F)⟫_𝕜 = RCLike.re ⟪S v, (w : F)⟫_𝕜 := by
      rw [hSsym w v, ← inner_conj_symm]
      exact RCLike.conj_re _
    have hexp : RCLike.re ⟪S (v + w), ((v + w : B.domain) : F)⟫_𝕜 -
        RCLike.re ⟪S (v - w), ((v - w : B.domain) : F)⟫_𝕜 =
        4 * RCLike.re ⟪S v, (w : F)⟫_𝕜 := by
      rw [hSadd, hSsub]
      simp only [Submodule.coe_add, Submodule.coe_sub, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, map_add, map_sub]
      rw [hswap]
      ring
    have hb1 := (abs_le.mp (hform (v + w))).2
    have hb2 := (abs_le.mp (hform (v - w))).1
    have hpar := parallelogram_law_with_norm 𝕜 ((v : F)) ((w : F))
    have hcoeadd : ‖((v + w : B.domain) : F)‖ = ‖(v : F) + (w : F)‖ := by
      rw [Submodule.coe_add]
    have hcoesub : ‖((v - w : B.domain) : F)‖ = ‖(v : F) - (w : F)‖ := by
      rw [Submodule.coe_sub]
    rw [hcoeadd] at hb1
    rw [hcoesub] at hb2
    nlinarith [hexp]
  -- scaling: the sharp sesquilinear bound
  have hscaled : ∀ v w : B.domain,
      RCLike.re ⟪S v, (w : F)⟫_𝕜 ≤ r * ‖(v : F)‖ * ‖(w : F)‖ := by
    intro v w
    rcases eq_or_ne ((v : F)) 0 with hv0 | hv0
    · have hveq : v = 0 := Subtype.ext hv0
      have hSv : S v = 0 := by
        rw [hveq]
        simp [hS]
      rw [hSv]
      simp [hv0]
    rcases eq_or_ne ((w : F)) 0 with hw0 | hw0
    · simp [hw0]
    have hnv : 0 < ‖(v : F)‖ := norm_pos_iff.mpr hv0
    have hnw : 0 < ‖(w : F)‖ := norm_pos_iff.mpr hw0
    set a : ℝ := ‖(v : F)‖⁻¹ with ha
    set b : ℝ := ‖(w : F)‖⁻¹ with hb
    have ha0 : 0 < a := by rw [ha]; exact inv_pos.mpr hnv
    have hb0 : 0 < b := by rw [hb]; exact inv_pos.mpr hnw
    set v' : B.domain := ((a : ℝ) : 𝕜) • v with hv'
    set w' : B.domain := ((b : ℝ) : 𝕜) • w with hw'
    have hSv' : S v' = ((a : ℝ) : 𝕜) • S v := by
      simp only [hS, hv', map_smul, Submodule.coe_smul, smul_sub]
      rw [smul_comm]
    have hnv' : ‖(v' : F)‖ = 1 := by
      rw [hv', Submodule.coe_smul, norm_smul, RCLike.norm_ofReal,
        abs_of_pos ha0, ha]
      exact inv_mul_cancel₀ hnv.ne'
    have hnw' : ‖(w' : F)‖ = 1 := by
      rw [hw', Submodule.coe_smul, norm_smul, RCLike.norm_ofReal,
        abs_of_pos hb0, hb]
      exact inv_mul_cancel₀ hnw.ne'
    have hval : RCLike.re ⟪S v', (w' : F)⟫_𝕜 =
        a * (b * RCLike.re ⟪S v, (w : F)⟫_𝕜) := by
      rw [hSv', hw', Submodule.coe_smul, inner_smul_left, inner_smul_right,
        RCLike.conj_ofReal, ← mul_assoc, ← RCLike.ofReal_mul,
        RCLike.re_ofReal_mul]
      ring
    have hstep := hpolar v' w'
    rw [hval, hnv', hnw'] at hstep
    have hone : (r / 2) * ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = r := by ring
    rw [hone] at hstep
    have hab : a * b > 0 := mul_pos ha0 hb0
    have hfinal : RCLike.re ⟪S v, (w : F)⟫_𝕜 ≤ r / (a * b) := by
      rw [le_div_iff₀ hab]
      calc RCLike.re ⟪S v, (w : F)⟫_𝕜 * (a * b)
          = a * (b * RCLike.re ⟪S v, (w : F)⟫_𝕜) := by ring
        _ ≤ r := hstep
    calc RCLike.re ⟪S v, (w : F)⟫_𝕜 ≤ r / (a * b) := hfinal
      _ = r * ‖(v : F)‖ * ‖(w : F)‖ := by
          rw [ha, hb]
          field_simp
  -- density upgrade to arbitrary right entries, then apply at `S u`
  have hall : ∀ z : F, RCLike.re ⟪S u, z⟫_𝕜 ≤ r * ‖(u : F)‖ * ‖z‖ := by
    have hclosed : IsClosed {z : F |
        RCLike.re ⟪S u, z⟫_𝕜 ≤ r * ‖(u : F)‖ * ‖z‖} := by
      refine isClosed_le ?_ ?_
      · exact RCLike.continuous_re.comp (continuous_const.inner continuous_id)
      · exact continuous_const.mul continuous_norm
    have hsubset : (B.domain : Set F) ⊆ {z : F |
        RCLike.re ⟪S u, z⟫_𝕜 ≤ r * ‖(u : F)‖ * ‖z‖} := by
      intro z hz
      exact hscaled u ⟨z, hz⟩
    intro z
    have hz : z ∈ closure (B.domain : Set F) := by
      rw [B.dense_domain.closure_eq]
      trivial
    exact closure_minimal hsubset hclosed hz
  have hkey := hall (S u)
  rw [inner_self_eq_norm_sq] at hkey
  rcases eq_or_lt_of_le (norm_nonneg (S u)) with h0 | h0
  · rw [← h0]
    exact mul_nonneg hr0 (norm_nonneg _)
  · nlinarith

/-! ## Constant-one interval/exterior closed Sylvester estimates -/

/-- Constant-one estimate for `A X - X B = C` with the interval block `B`
(quadratic form in `[β, α]`) and the exterior block `A` (bounded shifted left
inverse at distance `δ` beyond the interval). -/
theorem norm_closedSylvester_le_of_intervalExterior
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    (hBsym : B.IsSymmetric)
    {X C : F →L[𝕜] E} {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow B β) (hBhigh : SemiboundedAbove B α)
    (hAres : LeftShiftedInverseBound A ((α + β) / 2) ((α - β) / 2 + δ))
    (hEq : HasClosedSylvesterEquation A B X C) :
    δ * ‖X‖ ≤ ‖C‖ := by
  obtain ⟨J, hJleft, hJnorm⟩ := hAres
  set c : ℝ := (α + β) / 2 with hc
  set r : ℝ := (α - β) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrd : (0 : ℝ) < r + δ := by linarith
  -- pointwise absorption identity on the dense domain
  have hkey : ∀ y : B.domain, X (y : F) =
      J (C (y : F) + X (B.toLinearMap y - ((c : ℝ) : 𝕜) • (y : F))) := by
    intro y
    have heq := hEq.equation y
    have hJ := hJleft ⟨X (y : F), hEq.mapsTo y⟩
    have hexpand : A.toLinearMap ⟨X (y : F), hEq.mapsTo y⟩ -
        ((c : ℝ) : 𝕜) • X (y : F) =
        C (y : F) + X (B.toLinearMap y - ((c : ℝ) : 𝕜) • (y : F)) := by
      rw [map_sub, map_smul]
      have : A.toLinearMap ⟨X (y : F), hEq.mapsTo y⟩ =
          C (y : F) + X (B.toLinearMap y) := by
        rw [← heq]; abel
      rw [this]
      abel
    rw [hexpand] at hJ
    exact hJ.symm
  -- pointwise norm bound on the dense domain
  have hbound : ∀ y : B.domain, ‖X (y : F)‖ ≤
      (r + δ)⁻¹ * (‖C‖ + ‖X‖ * r) * ‖(y : F)‖ := by
    intro y
    have hshift := ForMathlib.DavisKahanExt.ClosedOperator.norm_shift_apply_le_of_form_bounds
      hBsym hβα hBlow hBhigh y
    calc ‖X (y : F)‖
        = ‖J (C (y : F) + X (B.toLinearMap y - ((c : ℝ) : 𝕜) • (y : F)))‖ := by
          rw [← hkey y]
      _ ≤ ‖J‖ * ‖C (y : F) + X (B.toLinearMap y - ((c : ℝ) : 𝕜) • (y : F))‖ :=
          J.le_opNorm _
      _ ≤ ‖J‖ * (‖C‖ * ‖(y : F)‖ + ‖X‖ * (r * ‖(y : F)‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg J)
          refine (norm_add_le _ _).trans (add_le_add (C.le_opNorm _) ?_)
          refine (X.le_opNorm _).trans ?_
          exact mul_le_mul_of_nonneg_left hshift (norm_nonneg X)
      _ ≤ (r + δ)⁻¹ * (‖C‖ * ‖(y : F)‖ + ‖X‖ * (r * ‖(y : F)‖)) := by
          refine mul_le_mul_of_nonneg_right hJnorm ?_
          exact add_nonneg
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg _)))
      _ = (r + δ)⁻¹ * (‖C‖ + ‖X‖ * r) * ‖(y : F)‖ := by ring
  -- density upgrade and operator-norm bound
  have hallz : ∀ z : F, ‖X z‖ ≤ (r + δ)⁻¹ * (‖C‖ + ‖X‖ * r) * ‖z‖ := by
    have hclosed : IsClosed {z : F |
        ‖X z‖ ≤ (r + δ)⁻¹ * (‖C‖ + ‖X‖ * r) * ‖z‖} := by
      refine isClosed_le (X.continuous.norm) ?_
      exact continuous_const.mul continuous_norm
    have hsubset : (B.domain : Set F) ⊆ {z : F |
        ‖X z‖ ≤ (r + δ)⁻¹ * (‖C‖ + ‖X‖ * r) * ‖z‖} := by
      intro z hz
      exact hbound ⟨z, hz⟩
    intro z
    have hz : z ∈ closure (B.domain : Set F) := by
      rw [B.dense_domain.closure_eq]
      trivial
    exact closure_minimal hsubset hclosed hz
  have hXnorm : ‖X‖ ≤ (r + δ)⁻¹ * (‖C‖ + ‖X‖ * r) :=
    ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (inv_nonneg.mpr hrd.le)
        (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hr0)))
      hallz
  have hmul := mul_le_mul_of_nonneg_left hXnorm hrd.le
  rw [← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul] at hmul
  nlinarith [norm_nonneg X]

/-- Constant-one estimate for `A X - X B = C` in the swapped orientation:
interval block `A` (quadratic form in `[β, α]`) and exterior block `B`
(bounded shifted two-sided inverse at distance `δ` beyond the interval). -/
theorem norm_closedSylvester_le_of_exteriorInterval
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    (hAsym : A.IsSymmetric)
    {X C : F →L[𝕜] E} {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hAlow : SemiboundedBelow A β) (hAhigh : SemiboundedAbove A α)
    (hBres : TwoSidedShiftedInverseBound B ((α + β) / 2) ((α - β) / 2 + δ))
    (hEq : HasClosedSylvesterEquation A B X C) :
    δ * ‖X‖ ≤ ‖C‖ := by
  obtain ⟨J, hJdom, _hJleft, hJright, hJnorm⟩ := hBres
  set c : ℝ := (α + β) / 2 with hc
  set r : ℝ := (α - β) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrd : (0 : ℝ) < r + δ := by linarith
  -- pointwise absorption identity, now on all of `F`
  have hkey : ∀ z : F, X z =
      (A.toLinearMap ⟨X (J z), hEq.mapsTo ⟨J z, hJdom z⟩⟩ -
        ((c : ℝ) : 𝕜) • X (J z)) - C (J z) := by
    intro z
    have heq := hEq.equation ⟨J z, hJdom z⟩
    have hres := hJright z
    -- `B (J z) = z + c • J z`
    have hBJ : B.toLinearMap ⟨J z, hJdom z⟩ = z + ((c : ℝ) : 𝕜) • J z :=
      sub_eq_iff_eq_add.mp hres
    have hXB : X (B.toLinearMap ⟨J z, hJdom z⟩) =
        X z + ((c : ℝ) : 𝕜) • X (J z) := by
      rw [hBJ, map_add, map_smul]
    have := heq
    rw [hXB] at this
    -- this : A (X (J z)) - (X z + c • X (J z)) = C (J z)
    calc X z = A.toLinearMap ⟨X (J z), hEq.mapsTo ⟨J z, hJdom z⟩⟩ -
          (X z + ((c : ℝ) : 𝕜) • X (J z)) - C (J z) + X z := by
          rw [this]; abel
      _ = (A.toLinearMap ⟨X (J z), hEq.mapsTo ⟨J z, hJdom z⟩⟩ -
          ((c : ℝ) : 𝕜) • X (J z)) - C (J z) := by abel
  have hbound : ∀ z : F, ‖X z‖ ≤ (r + δ)⁻¹ * (‖X‖ * r + ‖C‖) * ‖z‖ := by
    intro z
    have hshift := ForMathlib.DavisKahanExt.ClosedOperator.norm_shift_apply_le_of_form_bounds
      hAsym hβα hAlow hAhigh ⟨X (J z), hEq.mapsTo ⟨J z, hJdom z⟩⟩
    have hJz : ‖J z‖ ≤ (r + δ)⁻¹ * ‖z‖ := by
      refine (J.le_opNorm z).trans ?_
      exact mul_le_mul_of_nonneg_right hJnorm (norm_nonneg z)
    calc ‖X z‖
        = ‖(A.toLinearMap ⟨X (J z), hEq.mapsTo ⟨J z, hJdom z⟩⟩ -
            ((c : ℝ) : 𝕜) • X (J z)) - C (J z)‖ := by rw [← hkey z]
      _ ≤ ‖A.toLinearMap ⟨X (J z), hEq.mapsTo ⟨J z, hJdom z⟩⟩ -
            ((c : ℝ) : 𝕜) • X (J z)‖ + ‖C (J z)‖ := norm_sub_le _ _
      _ ≤ r * ‖X (J z)‖ + ‖C‖ * ‖J z‖ :=
          add_le_add hshift (C.le_opNorm _)
      _ ≤ r * (‖X‖ * ‖J z‖) + ‖C‖ * ‖J z‖ := by
          refine add_le_add ?_ le_rfl
          exact mul_le_mul_of_nonneg_left (X.le_opNorm _) hr0
      _ = (‖X‖ * r + ‖C‖) * ‖J z‖ := by ring
      _ ≤ (‖X‖ * r + ‖C‖) * ((r + δ)⁻¹ * ‖z‖) := by
          refine mul_le_mul_of_nonneg_left hJz ?_
          exact add_nonneg (mul_nonneg (norm_nonneg _) hr0) (norm_nonneg _)
      _ = (r + δ)⁻¹ * (‖X‖ * r + ‖C‖) * ‖z‖ := by ring
  have hXnorm : ‖X‖ ≤ (r + δ)⁻¹ * (‖X‖ * r + ‖C‖) :=
    ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (inv_nonneg.mpr hrd.le)
        (add_nonneg (mul_nonneg (norm_nonneg _) hr0) (norm_nonneg _)))
      hbound
  have hmul := mul_le_mul_of_nonneg_left hXnorm hrd.le
  rw [← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul] at hmul
  nlinarith [norm_nonneg X]

/-! ## The unbounded `sin Θ` theorem, operator norm -/

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
