/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Order.Compact

/-!
# A scalar minimum principle from monotone logarithmic curvature

If `L(0)=0` and `L'=w H` with positive w and strictly increasing H, Rolle's
theorem excludes two positive roots of L. If the derivative of a continuous
cost has L's sign, nonnegative H(0) gives a strictly increasing cost, while
negative H(0) and a positive endpoint derivative give one interior global
minimizer. No endpoint limit of L or continuity of H is required.

These are classical calculus consequences, formalized here as reusable
ingredients for spectral-penalty phase selection. They are not claims of
historical novelty or unrestricted operator optimization.
-/

public section

namespace TauCeti.SingleCrossingMinimum

open Set

variable {F L H : ℝ → ℝ} {theta : ℝ}

/-- Two applications of Rolle's theorem exclude distinct positive roots
when the derivative has a positive weight and a strictly increasing factor. -/
theorem positive_roots_eq
    (hzero : L 0 = 0)
    (hderiv : ∀ x ∈ Ico 0 theta, ∃ w > 0, HasDerivAt L (w * H x) x)
    (hmono : StrictMonoOn H (Ico 0 theta))
    {a b : ℝ} (ha : a ∈ Ioo 0 theta) (hb : b ∈ Ioo 0 theta)
    (hLa : L a = 0) (hLb : L b = 0) : a = b := by
  have hcont (a b : ℝ) (ha : 0 ≤ a) (hb : b < theta) : ContinuousOn L (Icc a b) := by
    intro x hx
    obtain ⟨w, _, hw⟩ := hderiv x ⟨ha.trans hx.1, hx.2.trans_lt hb⟩
    exact hw.continuousAt.continuousWithinAt
  have hnot (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < theta)
      (hLa : L a = 0) (hLb : L b = 0) : False := by
    obtain ⟨x, hx, hxD⟩ := exists_deriv_eq_zero ha (hcont 0 a le_rfl (hab.trans hb))
      (hzero.trans hLa.symm)
    obtain ⟨y, hy, hyD⟩ := exists_deriv_eq_zero hab (hcont a b ha.le hb) (hLa.trans hLb.symm)
    have hxθ : x ∈ Ico 0 theta := ⟨hx.1.le, hx.2.trans (hab.trans hb)⟩
    have hyθ : y ∈ Ico 0 theta := ⟨(ha.trans hy.1).le, hy.2.trans hb⟩
    obtain ⟨wx, hwx, hDx⟩ := hderiv x hxθ
    obtain ⟨wy, hwy, hDy⟩ := hderiv y hyθ
    have hxH : H x = 0 := (mul_eq_zero.mp (hDx.deriv.symm.trans hxD)).resolve_left hwx.ne'
    have hyH : H y = 0 := (mul_eq_zero.mp (hDy.deriv.symm.trans hyD)).resolve_left hwy.ne'
    have hlt := hmono hxθ hyθ (hx.2.trans hy.1)
    rw [hxH, hyH] at hlt
    exact lt_irrefl 0 hlt
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (hnot a b ha.1 hab hb.2 hLa hLb)
  · exact hab
  · exact False.elim (hnot b a hb.1 hab ha.2 hLb hLa)

/-- A positive zero of the imbalance forces strictly negative initial
control. This turns a positive stationary-point certificate into the
supercritical case without assuming an optimizer exists there. -/
theorem initial_neg_of_positive_root
    (hzero : L 0 = 0)
    (hderiv : ∀ x ∈ Ico 0 theta, ∃ w > 0, HasDerivAt L (w * H x) x)
    (hmono : StrictMonoOn H (Ico 0 theta))
    {a : ℝ} (ha : a ∈ Ioo 0 theta) (hLa : L a = 0) : H 0 < 0 := by
  have hc : ContinuousOn L (Icc 0 a) := by
    intro x hx
    obtain ⟨w, _, hw⟩ := hderiv x ⟨hx.1, hx.2.trans_lt ha.2⟩
    exact hw.continuousAt.continuousWithinAt
  obtain ⟨x, hx, hxD⟩ := exists_deriv_eq_zero ha.1 hc (hzero.trans hLa.symm)
  have hxθ : x ∈ Ico 0 theta := ⟨hx.1.le, hx.2.trans ha.2⟩
  obtain ⟨w, hw, hD⟩ := hderiv x hxθ
  have hxH : H x = 0 := (mul_eq_zero.mp (hD.deriv.symm.trans hxD)).resolve_left hw.ne'
  have hlt := hmono ⟨le_rfl, ha.1.trans ha.2⟩ hxθ hx.1
  rwa [hxH] at hlt

/-- A nonnegative initial control gives a strictly increasing cost on the
whole compact interval, including the zero-control critical case. -/
theorem strictMonoOn_of_initial_nonneg
    (hF : ContinuousOn F (Icc 0 theta)) (hzero : L 0 = 0)
    (hderiv : ∀ x ∈ Ico 0 theta, ∃ w > 0, HasDerivAt L (w * H x) x)
    (hmono : StrictMonoOn H (Ico 0 theta))
    (hsign : ∀ x ∈ Ioo 0 theta, (0 < deriv F x ↔ 0 < L x))
    (hinit : 0 ≤ H 0) : StrictMonoOn F (Icc 0 theta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hF
  intro x hx
  rw [interior_Icc] at hx
  apply (hsign x hx).mpr
  have hLm : StrictMonoOn L (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro y hy
      obtain ⟨w, _, hw⟩ := hderiv y ⟨hy.1, hy.2.trans_lt hx.2⟩
      exact hw.continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      obtain ⟨w, hw, hD⟩ := hderiv y ⟨hy.1.le, hy.2.trans hx.2⟩
      rw [hD.deriv]
      exact mul_pos hw (hinit.trans_lt
        (hmono ⟨le_rfl, hx.1.trans hx.2⟩ ⟨hy.1.le, hy.2.trans hx.2⟩ hy.1))
  have hlt := hLm ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  rwa [hzero] at hlt

private theorem better_than_zero_of_initial_neg
    (hθ : 0 < theta) (hF : ContinuousOn F (Icc 0 theta)) (hzero : L 0 = 0)
    (hderiv : ∀ x ∈ Ico 0 theta, ∃ w > 0, HasDerivAt L (w * H x) x)
    (hsign : ∀ x ∈ Ioo 0 theta, (deriv F x < 0 ↔ L x < 0))
    (hinit : H 0 < 0) : ∃ d ∈ Ioo 0 theta, F d < F 0 := by
  obtain ⟨w, hw, hD⟩ := hderiv 0 ⟨le_rfl, hθ⟩
  have hneg : deriv L 0 < 0 := by rw [hD.deriv]; exact mul_neg_of_pos_of_neg hw hinit
  obtain ⟨a, b, hab, hlocal⟩ :=
    (eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hzero).exists_Ioo_subset
  obtain ⟨d, hd0, hdb⟩ := exists_between (lt_min hab.2 hθ)
  have hdθ : d < theta := hdb.trans_le (min_le_right _ _)
  have hm : StrictAntiOn F (Icc 0 d) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (hF.mono (Icc_subset_Icc_right hdθ.le))
    intro y hy
    rw [interior_Icc] at hy
    apply (hsign y ⟨hy.1, hy.2.trans hdθ⟩).mpr
    have h : SignType.sign (L y) = SignType.sign ((0 : ℝ) - y) :=
      hlocal ⟨by linarith [hab.1, hy.1], by linarith [min_le_left b theta, hy.2]⟩
    rw [sign_neg (by linarith [hy.1] : (0 : ℝ) - y < 0)] at h
    exact sign_eq_neg_one_iff.mp h
  exact ⟨d, ⟨hd0, hdθ⟩, hm ⟨le_rfl, hd0.le⟩ ⟨hd0.le, le_rfl⟩ hd0⟩

private theorem better_than_endpoint (hθ : 0 < theta) {v : ℝ}
    (hD : HasDerivAt F v theta) (hv : 0 < v) :
    ∃ d ∈ Ioo 0 theta, F d < F theta := by
  let f := fun x => F x - F theta
  have hfD : deriv f theta > 0 := by rw [(hD.sub_const (F theta)).deriv]; exact hv
  have hf0 : f theta = 0 := sub_self _
  obtain ⟨a, b, hab, hlocal⟩ :=
    (eventually_nhdsWithin_sign_eq_of_deriv_pos hfD hf0).exists_Ioo_subset
  obtain ⟨d, had, hdθ⟩ := exists_between (max_lt hab.1 hθ)
  have hd0 : 0 < d := (le_max_right _ _).trans_lt had
  have h : SignType.sign (f d) = SignType.sign (d - theta) :=
    hlocal ⟨(le_max_left _ _).trans_lt had, hdθ.trans hab.2⟩
  rw [sign_neg (sub_neg.mpr hdθ)] at h
  exact ⟨d, ⟨hd0, hdθ⟩, sub_neg.mp (sign_eq_neg_one_iff.mp h)⟩

/-- A negative initial control gives exactly one interior global minimum.
Only derivative-sign information is assumed; no optimizer is postulated.
The positive endpoint derivative replaces an infinite log-ratio limit. -/
theorem exists_unique_minimizer_of_initial_neg
    (hθ : 0 < theta) (hF : ContinuousOn F (Icc 0 theta)) (hzero : L 0 = 0)
    (hderiv : ∀ x ∈ Ico 0 theta, ∃ w > 0, HasDerivAt L (w * H x) x)
    (hmono : StrictMonoOn H (Ico 0 theta))
    (hsignneg : ∀ x ∈ Ioo 0 theta, (deriv F x < 0 ↔ L x < 0))
    (hsignzero : ∀ x ∈ Ioo 0 theta, (deriv F x = 0 ↔ L x = 0))
    {v : ℝ} (hend : HasDerivAt F v theta) (hv : 0 < v)
    (hinit : H 0 < 0) :
    ∃ d ∈ Ioo 0 theta, deriv F d = 0 ∧
      ∀ x ∈ Icc 0 theta, F d ≤ F x ∧ (F x = F d ↔ x = d) := by
  have interior_of_min {d : ℝ} (hd : d ∈ Icc 0 theta) (hm : IsMinOn F (Icc 0 theta) d) :
      d ∈ Ioo 0 theta := by
    have hd0 : d ≠ 0 := by
      intro heq
      obtain ⟨x, hx, hbetter⟩ := better_than_zero_of_initial_neg hθ hF hzero hderiv hsignneg hinit
      have h := hm ⟨hx.1.le, hx.2.le⟩
      rw [heq] at h
      exact (not_lt_of_ge h) hbetter
    have hdθ : d ≠ theta := by
      intro heq
      obtain ⟨x, hx, hbetter⟩ := better_than_endpoint hθ hend hv
      have h := hm ⟨hx.1.le, hx.2.le⟩
      rw [heq] at h
      exact (not_lt_of_ge h) hbetter
    exact ⟨lt_of_le_of_ne hd.1 hd0.symm, lt_of_le_of_ne hd.2 hdθ⟩
  obtain ⟨d, hd, hm⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hθ.le⟩⟩ hF
  have hdi := interior_of_min hd hm
  have hDd : deriv F d = 0 := (hm.isLocalMin (Icc_mem_nhds hdi.1 hdi.2)).deriv_eq_zero
  refine ⟨d, hdi, hDd, ?_⟩
  intro x hx
  refine ⟨hm hx, ⟨?_, fun heq => by rw [heq]⟩⟩
  intro heq
  have hmx : IsMinOn F (Icc 0 theta) x := by intro y hy; rw [heq]; exact hm hy
  have hxi := interior_of_min hx hmx
  have hDx : deriv F x = 0 := (hmx.isLocalMin (Icc_mem_nhds hxi.1 hxi.2)).deriv_eq_zero
  exact positive_roots_eq hzero hderiv hmono hxi hdi
    ((hsignzero x hxi).mp hDx) ((hsignzero d hdi).mp hDd)

end TauCeti.SingleCrossingMinimum
