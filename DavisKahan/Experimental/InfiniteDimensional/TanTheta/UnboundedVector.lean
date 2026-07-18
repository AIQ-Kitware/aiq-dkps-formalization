/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.TanTheta.Vector
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SpectralRestriction
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.BoundedFromSpectrum

/-!
# The unbounded Davis--Kahan tangent theorem, per-vector form

The bounded infinite-dimensional tangent theorem uses the ambient operator only
on the test subspace, the complementary exact subspace, and differences of
vectors from those two subspaces.  This module records that domain information
explicitly and repeats the geometric argument for a closed self-adjoint
operator.

The first theorem accepts a closed symmetric operator together with:

* inclusion of the test subspace in the operator domain;
* inclusion and invariance of the complementary exact subspace;
* a centered norm bound on that complementary exact subspace;
* coercivity of the compressed action on the test subspace;
* a columnwise residual bound on the test subspace.

The second theorem specializes the complementary exact subspace to the
canonical Spectra range of the bounded interval `Set.Icc alpha beta`.  Spectral
calculus supplies its full-domain inclusion, invariance, and sharp centered
norm bound.  The resulting exact target is the orthogonal complement of that
interval spectral range.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace TanTheta

open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory
open SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem norm_sq_starProjection_add_norm_sq_sub
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (x : H) :
    ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  have horth : ⟪K.starProjection x, x - K.starProjection x⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem x)
      (K.sub_starProjection_mem_orthogonal x)
  have hx : K.starProjection x + (x - K.starProjection x) = x := by
    abel
  calc
    ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2 =
        ‖K.starProjection x + (x - K.starProjection x)‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), horth, map_zero]
      ring
    _ = ‖x‖ ^ 2 := by rw [hx]

/-- A residual bound on a domain-contained test subspace transfers to the
opposite block of a symmetric closed operator.  Only the particular vector in
the orthogonal complement is required to lie in the operator domain. -/
theorem norm_starProjection_closedOperator_le_of_mem_orthogonal
    (A : DKClosedOperator (H := H)) (hA : A.IsSymmetric)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection]
    (hZdom : Z ≤ A.domain)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A.toLinearMap ⟨x, hZdom hx⟩ -
          Z.starProjection (A.toLinearMap ⟨x, hZdom hx⟩)‖ ≤ ρ * ‖x‖)
    {w : H} (hwdom : w ∈ A.domain) (hw : w ∈ Zᗮ) :
    ‖Z.starProjection (A.toLinearMap ⟨w, hwdom⟩)‖ ≤ ρ * ‖w‖ := by
  set z : H := Z.starProjection (A.toLinearMap ⟨w, hwdom⟩) with hz
  have hzZ : z ∈ Z := Z.starProjection_apply_mem _
  have hzdom : z ∈ A.domain := hZdom hzZ
  have hsq : ‖z‖ ^ 2 ≤ ρ * ‖w‖ * ‖z‖ := by
    have h0 : ⟪z, z⟫_ℂ = ⟪A.toLinearMap ⟨w, hwdom⟩, z⟫_ℂ := by
      conv_lhs => rw [hz]
      rw [Z.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hzZ]
    have h1 : ⟪A.toLinearMap ⟨w, hwdom⟩, z⟫_ℂ =
        ⟪w, A.toLinearMap ⟨z, hzdom⟩ -
          Z.starProjection (A.toLinearMap ⟨z, hzdom⟩)⟫_ℂ := by
      calc
        ⟪A.toLinearMap ⟨w, hwdom⟩, z⟫_ℂ =
            ⟪w, A.toLinearMap ⟨z, hzdom⟩⟫_ℂ :=
          hA ⟨w, hwdom⟩ ⟨z, hzdom⟩
        _ = ⟪w, A.toLinearMap ⟨z, hzdom⟩ -
            Z.starProjection (A.toLinearMap ⟨z, hzdom⟩)⟫_ℂ := by
          rw [inner_sub_right,
            Submodule.inner_left_of_mem_orthogonal
              (Z.starProjection_apply_mem (A.toLinearMap ⟨z, hzdom⟩)) hw,
            sub_zero]
    calc
      ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_ℂ := (inner_self_eq_norm_sq z).symm
      _ = RCLike.re ⟪w, A.toLinearMap ⟨z, hzdom⟩ -
          Z.starProjection (A.toLinearMap ⟨z, hzdom⟩)⟫_ℂ := by
        rw [h0, h1]
      _ ≤ ‖⟪w, A.toLinearMap ⟨z, hzdom⟩ -
          Z.starProjection (A.toLinearMap ⟨z, hzdom⟩)⟫_ℂ‖ :=
        RCLike.re_le_norm _
      _ ≤ ‖w‖ * ‖A.toLinearMap ⟨z, hzdom⟩ -
          Z.starProjection (A.toLinearMap ⟨z, hzdom⟩)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (ρ * ‖z‖) := by
        have hzres := hρ z hzZ
        gcongr
      _ = ρ * ‖w‖ * ‖z‖ := by ring
  rcases eq_or_ne ‖z‖ 0 with h0 | h0
  · rw [h0]
    positivity
  · have hzpos : 0 < ‖z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith [hsq, hzpos]

/-- The domain-aware, per-vector Davis--Kahan tangent theorem.

The exact target is `V`; its orthogonal complement is required to lie in the
operator domain and to satisfy the centered interval estimate.  The test
subspace `Z` also lies in the domain.  This is precisely the domain footprint
of the bounded proof, so the conclusion is unchanged:

`delta * ‖x - P_V x‖ <= rho * ‖P_V x‖` for every `x` in `Z`.
-/
theorem tanTheta_unbounded_vector_of_centered_bounds
    (A : DKClosedOperator (H := H)) (hA : A.IsSymmetric)
    {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hZdom : Z ≤ A.domain)
    (hVperpdom : Vᗮ ≤ A.domain)
    (hVperpinv : ∀ u : H, ∀ hu : u ∈ Vᗮ,
      A.toLinearMap ⟨u, hVperpdom hu⟩ ∈ Vᗮ)
    {center halfWidth δ ρ : ℝ}
    (hhalf : 0 ≤ halfWidth) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZcoercive : ∀ x : H, ∀ hx : x ∈ Z,
      (halfWidth + δ) * ‖x‖ ≤
        ‖Z.starProjection (A.toLinearMap ⟨x, hZdom hx⟩) -
          (center : ℂ) • x‖)
    (hVperpcentered : ∀ u : H, ∀ hu : u ∈ Vᗮ,
      ‖A.toLinearMap ⟨u, hVperpdom hu⟩ - (center : ℂ) • u‖ ≤
        halfWidth * ‖u‖)
    (hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A.toLinearMap ⟨x, hZdom hx⟩ -
          Z.starProjection (A.toLinearMap ⟨x, hZdom hx⟩)‖ ≤ ρ * ‖x‖) :
    ∀ x : H, ∀ hx : x ∈ Z,
      δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  set Wop : (↥Vᗮ) →L[ℂ] H := Z.starProjection ∘L Vᗮ.subtypeL with hWop
  set κ : ℝ := ‖Wop‖ with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    exact norm_nonneg Wop
  have hmax : ∀ v : H, ∀ hv : v ∈ Vᗮ,
      ‖Z.starProjection v‖ ≤ κ * ‖v‖ := by
    intro v hv
    exact Wop.le_opNorm ⟨v, hv⟩
  have hκ1 : κ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact Z.norm_starProjection_apply_le (v : H)
  have hchain : ∀ u₀ : H, ∀ hu₀V : u₀ ∈ Vᗮ, ‖u₀‖ ≤ 1 →
      (halfWidth + δ) * ‖Z.starProjection u₀‖ ≤
        κ * halfWidth + ρ * ‖u₀ - Z.starProjection u₀‖ := by
    intro u₀ hu₀V hu₀n
    have hpZ : Z.starProjection u₀ ∈ Z := Z.starProjection_apply_mem u₀
    have huDom : u₀ ∈ A.domain := hVperpdom hu₀V
    have hpDom : Z.starProjection u₀ ∈ A.domain := hZdom hpZ
    have hwDom : u₀ - Z.starProjection u₀ ∈ A.domain :=
      A.domain.sub_mem huDom hpDom
    have h1 := hZcoercive (Z.starProjection u₀) hpZ
    have hAu :
        A.toLinearMap ⟨u₀, huDom⟩ =
          A.toLinearMap ⟨Z.starProjection u₀, hpDom⟩ +
            A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩ := by
      have hsub : (⟨u₀, huDom⟩ : A.domain) =
          ⟨Z.starProjection u₀, hpDom⟩ +
            ⟨u₀ - Z.starProjection u₀, hwDom⟩ := by
        apply Subtype.ext
        simp
      rw [hsub, map_add]
    have hsplit :
        Z.starProjection
            (A.toLinearMap ⟨Z.starProjection u₀, hpDom⟩) -
            (center : ℂ) • Z.starProjection u₀ =
          Z.starProjection
              (A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀) -
            Z.starProjection
              (A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩) := by
      calc
        Z.starProjection
              (A.toLinearMap ⟨Z.starProjection u₀, hpDom⟩) -
            (center : ℂ) • Z.starProjection u₀ =
            Z.starProjection
                ((A.toLinearMap ⟨Z.starProjection u₀, hpDom⟩ +
                    A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩) -
                  (center : ℂ) •
                    (Z.starProjection u₀ +
                      (u₀ - Z.starProjection u₀))) -
              Z.starProjection
                (A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩) := by
          simp only [map_sub, map_add, map_smul]
          rw [Submodule.starProjection_eq_self_iff.mpr hpZ]
          abel
        _ = Z.starProjection
              (A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀) -
            Z.starProjection
              (A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩) := by
          rw [← hAu, show Z.starProjection u₀ +
            (u₀ - Z.starProjection u₀) = u₀ by abel]
    have hcenterMem :
        A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀ ∈ Vᗮ :=
      Submodule.sub_mem _ (hVperpinv u₀ hu₀V) (Vᗮ.smul_mem _ hu₀V)
    have h2 :
        ‖Z.starProjection
            (A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀)‖ ≤
          κ * halfWidth := by
      calc
        ‖Z.starProjection
            (A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀)‖ ≤
            κ * ‖A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀‖ :=
          hmax _ hcenterMem
        _ ≤ κ * (halfWidth * ‖u₀‖) := by
          have hstrip := hVperpcentered u₀ hu₀V
          gcongr
        _ ≤ κ * (halfWidth * 1) := by gcongr
        _ = κ * halfWidth := by ring
    have h3 :
        ‖Z.starProjection
            (A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩)‖ ≤
          ρ * ‖u₀ - Z.starProjection u₀‖ :=
      norm_starProjection_closedOperator_le_of_mem_orthogonal
        A hA hZdom hρ0 hρ hwDom
        (Z.sub_starProjection_mem_orthogonal u₀)
    calc
      (halfWidth + δ) * ‖Z.starProjection u₀‖ ≤
          ‖Z.starProjection
              (A.toLinearMap ⟨Z.starProjection u₀, hpDom⟩) -
            (center : ℂ) • Z.starProjection u₀‖ := h1
      _ = ‖Z.starProjection
              (A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀) -
            Z.starProjection
              (A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩)‖ := by
        rw [hsplit]
      _ ≤ ‖Z.starProjection
              (A.toLinearMap ⟨u₀, huDom⟩ - (center : ℂ) • u₀)‖ +
            ‖Z.starProjection
              (A.toLinearMap ⟨u₀ - Z.starProjection u₀, hwDom⟩)‖ :=
        norm_sub_le _ _
      _ ≤ κ * halfWidth + ρ * ‖u₀ - Z.starProjection u₀‖ :=
        add_le_add h2 h3
  have hκineq : δ * κ ≤ ρ * Real.sqrt (1 - κ ^ 2) := by
    rcases eq_or_lt_of_le hκ0 with hκz | hκpos
    · rw [← hκz, mul_zero]
      positivity
    · have hev : ∀ ε ∈ Set.Ioo (0 : ℝ) κ,
          δ * κ ≤ (halfWidth + δ) * ε +
            ρ * Real.sqrt (1 - (κ - ε) ^ 2) := by
        intro ε hε
        obtain ⟨x, hx1, hxlt⟩ :=
          Wop.exists_lt_apply_of_lt_opNorm (r := κ - ε)
            (by rw [hκdef] at hε ⊢; linarith [hε.1])
        have hu₀V : (x : H) ∈ Vᗮ := x.2
        have hu₀n : ‖(x : H)‖ ≤ 1 := le_of_lt hx1
        have halt : κ - ε < ‖Z.starProjection (x : H)‖ := hxlt
        have hεκ : (0 : ℝ) ≤ κ - ε := by linarith [hε.2]
        have hpy := norm_sq_starProjection_add_norm_sq_sub Z (x : H)
        have hb : ‖(x : H) - Z.starProjection (x : H)‖ ≤
            Real.sqrt (1 - (κ - ε) ^ 2) := by
          have hb2 : ‖(x : H) - Z.starProjection (x : H)‖ ^ 2 ≤
              1 - (κ - ε) ^ 2 := by
            have hn1 : ‖(x : H)‖ ^ 2 ≤ 1 :=
              pow_le_one₀ (norm_nonneg _) hu₀n
            have h2 : (κ - ε) ^ 2 ≤
                ‖Z.starProjection (x : H)‖ ^ 2 := by
              nlinarith [halt, hεκ]
            linarith
          calc
            ‖(x : H) - Z.starProjection (x : H)‖ =
                Real.sqrt (‖(x : H) - Z.starProjection (x : H)‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
            _ ≤ Real.sqrt (1 - (κ - ε) ^ 2) := Real.sqrt_le_sqrt hb2
        have hstep := hchain (x : H) hu₀V hu₀n
        have hbρ : ρ * ‖(x : H) - Z.starProjection (x : H)‖ ≤
            ρ * Real.sqrt (1 - (κ - ε) ^ 2) :=
          mul_le_mul_of_nonneg_left hb hρ0
        have hlhs : (halfWidth + δ) * (κ - ε) ≤
            (halfWidth + δ) * ‖Z.starProjection (x : H)‖ := by
          have hpos : (0 : ℝ) ≤ halfWidth + δ := by linarith
          nlinarith [halt]
        nlinarith [hstep, hbρ, hlhs]
      have hcont : ContinuousWithinAt
          (fun ε : ℝ => (halfWidth + δ) * ε +
            ρ * Real.sqrt (1 - (κ - ε) ^ 2))
          (Set.Ioo 0 κ) 0 := by
        apply Continuous.continuousWithinAt
        exact (continuous_const.mul continuous_id).add
          (continuous_const.mul (Real.continuous_sqrt.comp
            (continuous_const.sub
              ((continuous_const.sub continuous_id).pow 2))))
      haveI hne : (nhdsWithin (0 : ℝ) (Set.Ioo 0 κ)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hκpos.ne]
        exact ⟨le_refl 0, hκpos.le⟩
      have hlim := ge_of_tendsto hcont
        (by filter_upwards [self_mem_nhdsWithin] with ε hε using hev ε hε)
      simpa using hlim
  have hkey : ∀ u : H, ∀ hu : u ∈ Vᗮ,
      δ * ‖Z.starProjection u‖ ≤ ρ * ‖u - Z.starProjection u‖ := by
    intro u huV
    have hPu : ‖Z.starProjection u‖ ≤ κ * ‖u‖ := hmax u huV
    have hpyu : ‖Z.starProjection u‖ ^ 2 +
        ‖u - Z.starProjection u‖ ^ 2 = ‖u‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub Z u
    have h1κ2 : (0 : ℝ) ≤ 1 - κ ^ 2 := by nlinarith [hκ1, hκ0]
    have hsq : (δ * ‖Z.starProjection u‖) ^ 2 ≤
        (ρ * ‖u - Z.starProjection u‖) ^ 2 := by
      have hδκsq : (δ * κ) ^ 2 ≤ ρ ^ 2 * (1 - κ ^ 2) := by
        calc
          (δ * κ) ^ 2 ≤ (ρ * Real.sqrt (1 - κ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hδ.le hκ0) hκineq 2
          _ = ρ ^ 2 * Real.sqrt (1 - κ ^ 2) ^ 2 := by ring
          _ = ρ ^ 2 * (1 - κ ^ 2) := by rw [Real.sq_sqrt h1κ2]
      have hPu2 : ‖Z.starProjection u‖ ^ 2 ≤ κ ^ 2 * ‖u‖ ^ 2 := by
        nlinarith [hPu, norm_nonneg (Z.starProjection u), norm_nonneg u, hκ0]
      calc
        (δ * ‖Z.starProjection u‖) ^ 2 =
            δ ^ 2 * ‖Z.starProjection u‖ ^ 2 := by ring
        _ ≤ δ ^ 2 * (κ ^ 2 * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hPu2 (sq_nonneg δ)
        _ = (δ * κ) ^ 2 * ‖u‖ ^ 2 := by ring
        _ ≤ ρ ^ 2 * (1 - κ ^ 2) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδκsq (sq_nonneg _)
        _ = ρ ^ 2 * ‖u‖ ^ 2 - ρ ^ 2 * (κ ^ 2 * ‖u‖ ^ 2) := by ring
        _ ≤ ρ ^ 2 * ‖u‖ ^ 2 - ρ ^ 2 * ‖Z.starProjection u‖ ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_left hPu2 (sq_nonneg ρ)
          linarith
        _ = ρ ^ 2 * (‖u‖ ^ 2 - ‖Z.starProjection u‖ ^ 2) := by ring
        _ = ρ ^ 2 * ‖u - Z.starProjection u‖ ^ 2 := by
          rw [show ‖u - Z.starProjection u‖ ^ 2 =
            ‖u‖ ^ 2 - ‖Z.starProjection u‖ ^ 2 by linarith [hpyu]]
        _ = (ρ * ‖u - Z.starProjection u‖) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
      Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at hsqrt
  intro x hxZ
  have huV : x - V.starProjection x ∈ Vᗮ :=
    V.sub_starProjection_mem_orthogonal x
  rcases eq_or_ne (x - V.starProjection x) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    positivity
  · have hCS : ‖x - V.starProjection x‖ ^ 2 ≤
        ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ := by
      have e1 : ⟪x - V.starProjection x, x - V.starProjection x⟫_ℂ =
          ⟪x, x - V.starProjection x⟫_ℂ := by
        conv_lhs => rw [inner_sub_left]
        rw [Submodule.inner_right_of_mem_orthogonal
          (V.starProjection_apply_mem x) huV, sub_zero]
      have e2 : ⟪x, x - V.starProjection x⟫_ℂ =
          ⟪x, Z.starProjection (x - V.starProjection x)⟫_ℂ := by
        rw [← Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hxZ]
      calc
        ‖x - V.starProjection x‖ ^ 2 =
            RCLike.re ⟪x - V.starProjection x,
              x - V.starProjection x⟫_ℂ :=
          (inner_self_eq_norm_sq _).symm
        _ = RCLike.re ⟪x,
            Z.starProjection (x - V.starProjection x)⟫_ℂ := by
          rw [e1, e2]
        _ ≤ ‖⟪x, Z.starProjection (x - V.starProjection x)⟫_ℂ‖ :=
          RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ :=
          norm_inner_le_norm _ _
    have hk := hkey _ huV
    have hpyZu : ‖Z.starProjection (x - V.starProjection x)‖ ^ 2 +
          ‖(x - V.starProjection x) -
              Z.starProjection (x - V.starProjection x)‖ ^ 2 =
        ‖x - V.starProjection x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub Z _
    have hpyVx : ‖V.starProjection x‖ ^ 2 +
        ‖x - V.starProjection x‖ ^ 2 = ‖x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub V x
    have hq : (0 : ℝ) < ‖x - V.starProjection x‖ := norm_pos_iff.mpr h0
    set q : ℝ := ‖x - V.starProjection x‖ with hqdef
    set pz : ℝ := ‖Z.starProjection (x - V.starProjection x)‖ with hpzdef
    set pw : ℝ := ‖(x - V.starProjection x) -
      Z.starProjection (x - V.starProjection x)‖ with hpwdef
    set pv : ℝ := ‖V.starProjection x‖ with hpvdef
    have hfin : (δ * q) ^ 2 ≤ (ρ * pv) ^ 2 := by
      have hAineq : (δ * pz) ^ 2 ≤ (ρ * pw) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg _)) hk 2
      have hBineq : (q ^ 2) ^ 2 ≤ (‖x‖ * pz) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hCS 2
      have hCineq : δ ^ 2 * (q ^ 2) ^ 2 ≤
          ρ ^ 2 * pv ^ 2 * (q ^ 2) := by
        calc
          δ ^ 2 * (q ^ 2) ^ 2 ≤ δ ^ 2 * (‖x‖ * pz) ^ 2 :=
            mul_le_mul_of_nonneg_left hBineq (sq_nonneg δ)
          _ = ‖x‖ ^ 2 * (δ * pz) ^ 2 := by ring
          _ ≤ ‖x‖ ^ 2 * (ρ * pw) ^ 2 :=
            mul_le_mul_of_nonneg_left hAineq (sq_nonneg _)
          _ = ρ ^ 2 * ‖x‖ ^ 2 * pw ^ 2 := by ring
          _ = ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 -
              ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by
            rw [show pw ^ 2 = q ^ 2 - pz ^ 2 by linarith [hpyZu]]
            ring
          _ ≤ ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 -
              ρ ^ 2 * (q ^ 2) ^ 2 := by
            have h5 : ρ ^ 2 * (q ^ 2) ^ 2 ≤
                ρ ^ 2 * (‖x‖ * pz) ^ 2 :=
              mul_le_mul_of_nonneg_left hBineq (sq_nonneg ρ)
            have h6 : ρ ^ 2 * (‖x‖ * pz) ^ 2 =
                ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by ring
            linarith
          _ = ρ ^ 2 * (‖x‖ ^ 2 - q ^ 2) * q ^ 2 := by ring
          _ = ρ ^ 2 * pv ^ 2 * q ^ 2 := by
            rw [show ‖x‖ ^ 2 - q ^ 2 = pv ^ 2 by linarith [hpyVx]]
      have hq2 : (0 : ℝ) < q ^ 2 := by positivity
      nlinarith [hCineq, hq2]
    have hsqrt := Real.sqrt_le_sqrt hfin
    rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
      Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at hsqrt

/-- Every vector in the canonical interval spectral range lies in the domain of
the unbounded self-adjoint operator. -/
theorem selfAdjointSpectralIcc_mem_domain
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {α β : ℝ} (hαβ : α ≤ β)
    {x : H}
    (hx : x ∈ selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc) :
    x ∈ A.domain := by
  let U := genToGroup hA
  have hgen : generator U = A.toLinearPMap := generator_genToGroup hA
  have hdom : (generator U).domain = A.domain :=
    congrArg LinearPMap.domain hgen
  have habs : ∀ s ∈ Set.Icc α β, |s| ≤ max |α| |β| := by
    intro s hs
    exact abs_le_max_of_mem_Icc hs
  have hfix : spectralProjection U (Set.Icc α β) measurableSet_Icc x = x := by
    change selfAdjointSpectralProjection A hA (Set.Icc α β)
      measurableSet_Icc x = x
    rw [selfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  have hxU : spectralProjection U (Set.Icc α β) measurableSet_Icc x ∈
      (generator U).domain :=
    spectralProjection_mem_generatorDomain U measurableSet_Icc habs x
  rw [hfix] at hxU
  exact (le_of_eq hdom) hxU

/-- The canonical interval spectral range satisfies the sharp centered norm
bound required by the unbounded tangent theorem. -/
theorem selfAdjointSpectralIcc_centered_norm_le
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {α β : ℝ} (hαβ : α ≤ β)
    {x : H}
    (hx : x ∈ selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc) :
    ‖A.toLinearMap
          ⟨x, selfAdjointSpectralIcc_mem_domain A hA hαβ hx⟩ -
        (((α + β) / 2 : ℝ) : ℂ) • x‖ ≤
      (β - α) / 2 * ‖x‖ := by
  let U := genToGroup hA
  have hgen : generator U = A.toLinearPMap := generator_genToGroup hA
  have habs : ∀ s ∈ Set.Icc α β, |s| ≤ max |α| |β| := by
    intro s hs
    exact abs_le_max_of_mem_Icc hs
  have hfix : spectralProjection U (Set.Icc α β) measurableSet_Icc x = x := by
    change selfAdjointSpectralProjection A hA (Set.Icc α β)
      measurableSet_Icc x = x
    rw [selfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  have hprojDom : spectralProjection U (Set.Icc α β) measurableSet_Icc x ∈
      (generator U).domain :=
    spectralProjection_mem_generatorDomain U measurableSet_Icc habs x
  have hxU : x ∈ (generator U).domain := by
    rw [hfix] at hprojDom
    exact hprojDom
  have hbound := generator_sub_smul_norm_le_Icc U α β ((α + β) / 2)
    (by linarith) (by linarith) x hprojDom
  have hsub :
      (⟨spectralProjection U (Set.Icc α β) measurableSet_Icc x, hprojDom⟩ :
        (generator U).domain) = ⟨x, hxU⟩ :=
    Subtype.ext hfix
  have hmax : max ((α + β) / 2 - α) (β - (α + β) / 2) =
      (β - α) / 2 := by
    rw [show (α + β) / 2 - α = (β - α) / 2 by ring,
      show β - (α + β) / 2 = (β - α) / 2 by ring, max_self]
  rw [hsub, hfix, hmax] at hbound
  have happly := (LinearPMap.ext_iff.mp hgen).2
  have htransport :
      generator U ⟨x, hxU⟩ =
        A.toLinearPMap
          ⟨x, selfAdjointSpectralIcc_mem_domain A hA hαβ hx⟩ :=
    happly
      (x := x)
      (hf := hxU)
      (hg := selfAdjointSpectralIcc_mem_domain A hA hαβ hx)
  have hsmul : ((((α + β) / 2 : ℝ) : ℂ) • x) =
      ((α + β) / 2 : ℝ) • x :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ x).symm
  calc
    ‖A.toLinearMap
          ⟨x, selfAdjointSpectralIcc_mem_domain A hA hαβ hx⟩ -
        (((α + β) / 2 : ℝ) : ℂ) • x‖ =
        ‖generator U ⟨x, hxU⟩ - (((α + β) / 2 : ℝ) : ℂ) • x‖ :=
      congrArg
        (fun y : H => ‖y - (((α + β) / 2 : ℝ) : ℂ) • x‖)
        htransport.symm
    _ = ‖generator U ⟨x, hxU⟩ - ((α + β) / 2 : ℝ) • x‖ := by
      rw [hsmul]
    _ ≤ (β - α) / 2 * ‖x‖ := hbound

/-- Canonical exact-subspace specialization of the unbounded tangent theorem.

The bounded interval spectral range `E_A([alpha,beta])H` is the complementary
exact component.  Its orthogonal complement is the exact target subspace.  The
only remaining hypotheses concern the test subspace: domain inclusion,
coercivity of its compressed action, and a columnwise residual bound.
-/
theorem tanTheta_unbounded_exactSpectralIcc
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection]
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZdom : Z ≤ A.domain)
    (hZcoercive : ∀ x : H, ∀ hx : x ∈ Z,
      ((β - α) / 2 + δ) * ‖x‖ ≤
        ‖Z.starProjection (A.toLinearMap ⟨x, hZdom hx⟩) -
          (((α + β) / 2 : ℝ) : ℂ) • x‖)
    (hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A.toLinearMap ⟨x, hZdom hx⟩ -
          Z.starProjection (A.toLinearMap ⟨x, hZdom hx⟩)‖ ≤ ρ * ‖x‖) :
    let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc
    ∀ x : H, ∀ hx : x ∈ Z,
      δ * ‖x - Wᗮ.starProjection x‖ ≤ ρ * ‖Wᗮ.starProjection x‖ := by
  let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
    measurableSet_Icc
  have hdouble : (Wᗮ)ᗮ = W := by
    rw [Submodule.orthogonal_orthogonal]
  have hVperpdom : (Wᗮ)ᗮ ≤ A.domain := by
    intro u hu
    have huW : u ∈ W := (le_of_eq hdouble) hu
    exact selfAdjointSpectralIcc_mem_domain A hA hαβ huW
  have hVperpinv : ∀ u : H, ∀ hu : u ∈ (Wᗮ)ᗮ,
      A.toLinearMap ⟨u, hVperpdom hu⟩ ∈ (Wᗮ)ᗮ := by
    intro u hu
    have huW : u ∈ W := (le_of_eq hdouble) hu
    have himage : A.toLinearMap ⟨u, hVperpdom hu⟩ ∈ W :=
      selfAdjoint_maps_spectralSubspace A hA measurableSet_Icc
        ⟨u, hVperpdom hu⟩ huW
    exact (le_of_eq hdouble.symm) himage
  have hcenter : ∀ u : H, ∀ hu : u ∈ (Wᗮ)ᗮ,
      ‖A.toLinearMap ⟨u, hVperpdom hu⟩ -
          (((α + β) / 2 : ℝ) : ℂ) • u‖ ≤
        (β - α) / 2 * ‖u‖ := by
    intro u hu
    have huW : u ∈ W := (le_of_eq hdouble) hu
    have h := selfAdjointSpectralIcc_centered_norm_le A hA hαβ huW
    have hdomEq :
        (⟨u, hVperpdom hu⟩ : A.domain) =
          ⟨u, selfAdjointSpectralIcc_mem_domain A hA hαβ huW⟩ :=
      Subtype.ext rfl
    rw [hdomEq]
    exact h
  exact tanTheta_unbounded_vector_of_centered_bounds
    (V := Wᗮ) (Z := Z) A hA.isSymmetric hZdom hVperpdom hVperpinv
      (halfWidth := (β - α) / 2)
      (center := (α + β) / 2)
      (δ := δ) (ρ := ρ)
      (by linarith) hδ hρ0 hZcoercive hcenter hρ

end TanTheta
end Experimental
end DavisKahan
end ForMathlib
