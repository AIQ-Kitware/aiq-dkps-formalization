/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourSpectrum
public import ForTauCeti.Analysis.InnerProductSpace.NormalCharpolyCost
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The determinant-negative real four-dimensional transport cost

A determinant-negative orthogonal matrix in dimension four has fixed
eigenvalues `1,-1` and a conjugate pair. The full characteristic polynomial
computes its literal displacement cost, including repeated endpoint roots.
For a two-angle transport the trace bound selects reflection on the larger
angle and canonical rotation on the smaller one.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix Polynomial

/-- The literal ambient spectral displacement cost in the four-dimensional
cosine--sine coordinate model. All four singular values, including zeros,
are counted. -/
@[expose] def fourDisplacementCost (rho : ℝ → ℝ)
    (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) : ℝ :=
  ∑ i : Fin 4, rho ((LinearMap.id - W.toEuclideanLin).singularValues i)

/-- The trace parameter for either determinant-negative component. -/
@[expose] def oppositeFourTrace (t u a b e : ℝ) : ℝ :=
  (Real.cos t + e * Real.cos u) * Real.cos a +
    (Real.cos t - e * Real.cos u) * Real.cos b

/-- For ordered principal angles the determinant-negative trace is bounded
by twice the cosine of the smaller angle, in both components. -/
theorem oppositeFourTrace_mem (t u a b e : ℝ)
    (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ Real.pi / 2)
    (he : e = 1 ∨ e = -1) :
    oppositeFourTrace t u a b e ∈ Set.Icc (-2 * Real.cos u) (2 * Real.cos u) := by
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ht⟩
  have hd : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcd : Real.cos t ≤ Real.cos u :=
    Real.cos_le_cos_of_nonneg_of_le_pi hu (by linarith [Real.pi_pos]) hut
  have hplus : 0 ≤ Real.cos t + Real.cos u := add_nonneg hc hd
  have hminus : Real.cos t - Real.cos u ≤ 0 := sub_nonpos.mpr hcd
  have ha₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one a) hplus
  have ha₂ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos a) hplus
  have ha₃ := mul_le_mul_of_nonpos_left (Real.cos_le_one a) hminus
  have ha₄ := mul_le_mul_of_nonpos_left (Real.neg_one_le_cos a) hminus
  have hb₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one b) hplus
  have hb₂ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos b) hplus
  have hb₃ := mul_le_mul_of_nonpos_left (Real.cos_le_one b) hminus
  have hb₄ := mul_le_mul_of_nonpos_left (Real.neg_one_le_cos b) hminus
  rcases he with rfl | rfl <;>
    constructor <;> simp only [oppositeFourTrace, one_mul, neg_one_mul] <;> linarith

/-- A reciprocal quadratic on the unit circle has displacement cost
`2*rho(sqrt(2-T))`. The additional roots `1,-1` contribute `rho(0),rho(2)`.
The endpoint cases `T = ±2` use the same root multiset, with multiplicity. -/
theorem four_displacement_cost_of_negative_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose * A = 1)
    (T : ℝ) (hT : T ∈ Set.Icc (-2) 2)
    (hpoly : A.charpoly = (X ^ 2 - 1) * (X ^ 2 - C T * X + 1))
    (rho : ℝ → ℝ) :
    (∑ i : Fin (Fintype.card n), rho ((LinearMap.id - A.toEuclideanLin).singularValues i)) =
      rho 0 + rho 2 + 2 * rho (Real.sqrt (2 - T)) := by
  obtain ⟨w, hadd, hmul, hw⟩ := TauCeti.exists_unit_circle_pair_of_trace_mem T hT
  have hquad : (X - C w) * (X - C (star w)) =
      X ^ 2 - C (T : ℂ) * X + 1 := by
    calc
      _ = X ^ 2 - C (w + star w) * X + C (w * star w) := by
        simp only [map_add, map_mul]; ring
      _ = _ := by rw [hadd, hmul, map_one]
  have hwstar : ‖1 - star w‖ = Real.sqrt (2 - T) := by
    rw [← star_one (R := ℂ), ← star_sub, norm_star, hw]
  have hwconj : ‖1 - (starRingEnd ℂ) w‖ = Real.sqrt (2 - T) := hwstar
  let mu : Fin 4 → ℂ := ![1, -1, w, star w]
  have hfactor : A.charpoly.map Complex.ofRealHom =
      ∏ i : Fin 4, (X - C (mu i)) := by
    rw [hpoly]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
    simp only [Fin.prod_univ_four]
    change (X ^ 2 - 1) * (X ^ 2 - C (T : ℂ) * X + 1) =
      (X - C (1 : ℂ)) * (X - C (-1 : ℂ)) * (X - C w) * (X - C (star w))
    rw [mul_assoc ((X - C (1 : ℂ)) * (X - C (-1 : ℂ))), hquad]
    simp only [map_one, map_neg]
    ring
  calc
    _ = ((A.charpoly.map Complex.ofRealHom).roots.map (fun z => rho ‖1 - z‖)).sum := by
      exact Matrix.sum_displacement_singularValues_eq_complex_roots_of_orthogonal A hA rho
    _ = _ := by
      rw [hfactor, Polynomial.roots_prod _ _ (by
        simp only [Finset.prod_ne_zero_iff]
        exact fun i _ => Polynomial.X_sub_C_ne_zero (mu i))]
      norm_num [mu, hw, hwconj]
      ring

/-- Exact literal cost throughout both determinant-negative components.
The trace bound includes zero, equal and right principal angles. -/
theorem fourTransport_opposite_cost (t u a b e : ℝ)
    (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ Real.pi / 2)
    (he : e = 1 ∨ e = -1) (rho : ℝ → ℝ) :
    fourDisplacementCost rho (fourTransport ![t, u] a b e (-e)) =
      rho 0 + rho 2 + 2 * rho (Real.sqrt (2 - oppositeFourTrace t u a b e)) := by
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hf2 : (-e) ^ 2 = 1 := by nlinarith [he2]
  have htrace := oppositeFourTrace_mem t u a b e hu hut ht he
  have hT : oppositeFourTrace t u a b e ∈ Set.Icc (-2) 2 := by
    constructor <;> nlinarith [Real.cos_le_one u, htrace.1, htrace.2]
  have hcost := four_displacement_cost_of_negative_charpoly
    (fourTransport ![t, u] a b e (-e))
    (fourTransport_mem_fiber ![t, u] a b e (-e) he2 hf2).1
    (oppositeFourTrace t u a b e) hT
    (by rw [charpoly_fourTransport]; exact charpoly_fourTransportMatrix_opposite t u a b e he2) rho
  rw [Fintype.card_sum, Fintype.card_fin] at hcost
  exact hcost

/-- The sharp lower bound in the determinant-negative class compares with
every ambient orthogonal transporter of this source and target. It is
not restricted to prescribed principal-plane blocks. -/
theorem four_negative_transport_cost_lower_bound
    (t u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0)
    (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (hW : W.transpose * W = 1) (hdet : W.det = -1)
    (htrans : W * fourSourceProjection * W.transpose =
      fourCSRotation ![t, u] * fourSourceProjection * (fourCSRotation ![t, u]).transpose) :
    rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos u)) ≤ fourDisplacementCost rho W := by
  obtain ⟨a, b, e, f, he, hf, hform⟩ := exists_fourTransport_of_mem_fiber ![t, u] W hW htrans
  have hef : e * f = -1 := by simpa only [hform, det_fourTransport] using hdet
  have hf' : f = -e := by rcases he with rfl | rfl <;> linarith
  subst f
  rw [hform, fourTransport_opposite_cost t u a b e hu hut ht he, hzero, zero_add]
  have htrace := oppositeFourTrace_mem t u a b e hu hut ht he
  have hTlo : -2 ≤ oppositeFourTrace t u a b e := by
    nlinarith [htrace.1, Real.cos_le_one u]
  have hlow : Real.sqrt (2 - 2 * Real.cos u) ≤
      Real.sqrt (2 - oppositeFourTrace t u a b e) := Real.sqrt_le_sqrt (by linarith [htrace.2])
  have hbound : Real.sqrt (2 - oppositeFourTrace t u a b e) ≤ 2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ 2 - oppositeFourTrace t u a b e by
      nlinarith [htrace.2, Real.cos_le_one u])
    nlinarith [Real.sqrt_nonneg (2 - oppositeFourTrace t u a b e)]
  have hp := hrho ⟨Real.sqrt_nonneg _, hlow.trans hbound⟩
    ⟨Real.sqrt_nonneg _, hbound⟩ hlow
  linarith

/-- Reflection on the larger-angle principal plane, with canonical rotation
on the smaller plane, attains the sharp determinant-negative value. -/
theorem four_negative_transport_cost_attained
    (t u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hzero : rho 0 = 0) :
    fourDisplacementCost rho (fourTransport ![t, u] Real.pi 0 (-1) 1) =
      rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos u)) := by
  have hcost := fourTransport_opposite_cost t u Real.pi 0 (-1) hu hut ht (Or.inr rfl) rho
  have htrace : oppositeFourTrace t u Real.pi 0 (-1) = 2 * Real.cos u := by
    simp [oppositeFourTrace]
    ring
  simpa only [htrace, hzero, zero_add, neg_neg] using hcost

/-- Exact optimization over the entire determinant-negative ambient fiber,
with a constructed attaining transporter. Only monotonicity on `[0,2]`
and `rho(0)=0` are required, without continuity or strict increase. -/
theorem exists_minimizing_four_negative_transport
    (t u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    ∃ W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
      W.transpose * W = 1 ∧ W.det = -1 ∧
      W * fourSourceProjection * W.transpose =
        fourCSRotation ![t, u] * fourSourceProjection * (fourCSRotation ![t, u]).transpose ∧
      fourDisplacementCost rho W = rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos u)) ∧
      IsMinOn (fourDisplacementCost rho)
        {X | X.transpose * X = 1 ∧ X.det = -1 ∧
          X * fourSourceProjection * X.transpose =
            fourCSRotation ![t, u] * fourSourceProjection * (fourCSRotation ![t, u]).transpose} W := by
  let W := fourTransport ![t, u] Real.pi 0 (-1) 1
  have hmem := fourTransport_mem_fiber ![t, u] Real.pi 0 (-1) 1
    (by norm_num) (by norm_num)
  have hcost := four_negative_transport_cost_attained t u hu hut ht rho hzero
  refine ⟨W, hmem.1, by simp [W], hmem.2, hcost, ?_⟩
  intro X hX
  rw [hcost]
  exact four_negative_transport_cost_lower_bound t u hu hut ht rho hrho hzero X
    hX.1 hX.2.1 hX.2.2

/-- With a strictly increasing penalty, a determinant-negative coordinate
transporter is optimal exactly when its trace reaches the sharp upper
endpoint. This condition retains all repeated-angle and right-angle cases;
it does not assume a simple spectrum or a unique reflection. -/
theorem fourTransport_opposite_cost_eq_minimum_iff
    (t u a b e : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) (ht : t ≤ Real.pi / 2)
    (he : e = 1 ∨ e = -1) (rho : ℝ → ℝ)
    (hrho : StrictMonoOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    fourDisplacementCost rho (fourTransport ![t, u] a b e (-e)) =
        rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos u)) ↔
      oppositeFourTrace t u a b e = 2 * Real.cos u := by
  rw [fourTransport_opposite_cost t u a b e hu hut ht he, hzero, zero_add]
  constructor
  · intro hcost
    have htrace := oppositeFourTrace_mem t u a b e hu hut ht he
    have hrad : 0 ≤ 2 - oppositeFourTrace t u a b e := by
      nlinarith [htrace.2, Real.cos_le_one u]
    have hlowrad : 0 ≤ 2 - 2 * Real.cos u := by linarith [Real.cos_le_one u]
    have hbound : Real.sqrt (2 - oppositeFourTrace t u a b e) ≤ 2 := by
      have hs := Real.sq_sqrt hrad
      nlinarith [Real.sqrt_nonneg (2 - oppositeFourTrace t u a b e),
        htrace.1, Real.cos_le_one u]
    have hlow := Real.sqrt_le_sqrt (show 2 - 2 * Real.cos u ≤
      2 - oppositeFourTrace t u a b e by linarith [htrace.2])
    have heq : rho (Real.sqrt (2 - oppositeFourTrace t u a b e)) =
        rho (Real.sqrt (2 - 2 * Real.cos u)) := by linarith
    have hsqrt := hrho.injOn ⟨Real.sqrt_nonneg _, hbound⟩
      ⟨Real.sqrt_nonneg _, hlow.trans hbound⟩ heq
    nlinarith [Real.sq_sqrt hrad, Real.sq_sqrt hlowrad]
  · intro htrace
    rw [htrace]

private theorem signed_trace_eq_max_iff (c d a b : ℝ)
    (hc : 0 ≤ c) (hcd : c < d)
    (ha : a ∈ Set.Icc (-1) 1) (hb : b ∈ Set.Icc (-1) 1) :
    (c+d)*a + (c-d)*b = 2*d ↔ a = 1 ∧ b = -1 := by
  constructor
  · intro h
    have hplus : 0 < c+d := by linarith
    have hminus : 0 < d-c := sub_pos.mpr hcd
    have hA := mul_nonneg hplus.le (sub_nonneg.mpr ha.2)
    have hB := mul_nonneg hminus.le (show 0 ≤ 1+b by linarith [hb.1])
    have hsum : (c+d)*(1-a) + (d-c)*(1+b) = 0 := by nlinarith [h]
    have hzA : (c+d)*(1-a) = 0 := by linarith
    have hzB : (d-c)*(1+b) = 0 := by linarith
    have := (mul_eq_zero.mp hzA).resolve_left hplus.ne'
    have := (mul_eq_zero.mp hzB).resolve_left hminus.ne'
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

/-- With unequal principal angles and a strictly increasing penalty,
exactly the two displayed reflection choices minimize the full negative
class. The coordinate angles are specified through their cosines, so no
periodicity or orientation choice is hidden in the statement. -/
theorem fourTransport_opposite_minimizers_of_lt
    (t u a b e : ℝ) (hu : 0 ≤ u) (hut : u < t) (ht : t ≤ Real.pi / 2)
    (he : e = 1 ∨ e = -1) (rho : ℝ → ℝ)
    (hrho : StrictMonoOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    fourDisplacementCost rho (fourTransport ![t, u] a b e (-e)) =
        rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos u)) ↔
      (e = 1 ∧ Real.cos a = 1 ∧ Real.cos b = -1) ∨
      (e = -1 ∧ Real.cos a = -1 ∧ Real.cos b = 1) := by
  rw [fourTransport_opposite_cost_eq_minimum_iff t u a b e hu hut.le ht he rho hrho hzero]
  have hc : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ht⟩
  have hcd : Real.cos t < Real.cos u := Real.strictAntiOn_cos
    ⟨hu, by linarith [Real.pi_pos]⟩ ⟨by linarith, by linarith [Real.pi_pos]⟩ hut
  have ha : Real.cos a ∈ Set.Icc (-1) 1 := ⟨Real.neg_one_le_cos a, Real.cos_le_one a⟩
  have hb : Real.cos b ∈ Set.Icc (-1) 1 := ⟨Real.neg_one_le_cos b, Real.cos_le_one b⟩
  have hne : (1 : ℝ) ≠ -1 := by norm_num
  rcases he with rfl | rfl
  · simpa [oppositeFourTrace, hne, hne.symm, sub_eq_add_neg] using
      signed_trace_eq_max_iff (Real.cos t) (Real.cos u) (Real.cos a) (Real.cos b) hc hcd ha hb
  · simpa [oppositeFourTrace, hne, hne.symm, sub_eq_add_neg, add_comm, and_comm] using
      signed_trace_eq_max_iff (Real.cos t) (Real.cos u) (Real.cos b) (Real.cos a) hc hcd hb ha

/-- Equal non-right angles leave one free circle parameter in each of the
two negative components. This includes the zero-angle pair. -/
theorem fourTransport_opposite_minimizers_of_eq
    (t a b e : ℝ) (ht0 : 0 ≤ t) (ht : t < Real.pi / 2)
    (he : e = 1 ∨ e = -1) (rho : ℝ → ℝ)
    (hrho : StrictMonoOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    fourDisplacementCost rho (fourTransport ![t, t] a b e (-e)) =
        rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos t)) ↔
      (e = 1 ∧ Real.cos a = 1) ∨ (e = -1 ∧ Real.cos b = 1) := by
  rw [fourTransport_opposite_cost_eq_minimum_iff t t a b e ht0 le_rfl ht.le he rho hrho hzero]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht⟩
  have hne : (1 : ℝ) ≠ -1 := by norm_num
  have hfactor (x : ℝ) : (Real.cos t + Real.cos t)*x = 2*Real.cos t ↔ x = 1 := by
    constructor
    · intro h
      apply mul_left_cancel₀ hc.ne'
      nlinarith [h]
    · rintro rfl
      ring
  rcases he with rfl | rfl
  · simpa [oppositeFourTrace, hne, hne.symm] using hfactor (Real.cos a)
  · simpa [oppositeFourTrace, hne, hne.symm] using hfactor (Real.cos b)

/-- At a pair of right angles every determinant-negative transporter has
the same cost. Neither strict increase nor monotonicity is needed here. -/
theorem fourTransport_opposite_cost_at_right_angles
    (a b e : ℝ) (he : e = 1 ∨ e = -1) (rho : ℝ → ℝ) (hzero : rho 0 = 0) :
    fourDisplacementCost rho
        (fourTransport ![Real.pi / 2, Real.pi / 2] a b e (-e)) =
      rho 2 + 2 * rho (Real.sqrt 2) := by
  rw [fourTransport_opposite_cost _ _ _ _ _ (by positivity) le_rfl le_rfl he,
    oppositeFourTrace, Real.cos_pi_div_two]
  simp only [mul_zero, zero_add, zero_mul, add_zero, sub_zero, hzero]

/-- For unequal angles, every ambient determinant-negative optimizer is
one of exactly two concrete transports: reflect the larger-angle plane
through one of its two line-transporting reflection axes. The comparison
is against the entire negative fiber, including cross-plane competitors. -/
theorem four_negative_transport_minimizers_of_lt
    (t u : ℝ) (hu : 0 ≤ u) (hut : u < t) (ht : t ≤ Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : StrictMonoOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0)
    (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (hW : W.transpose * W = 1) (hdet : W.det = -1)
    (htrans : W * fourSourceProjection * W.transpose =
      fourCSRotation ![t, u] * fourSourceProjection * (fourCSRotation ![t, u]).transpose) :
    fourDisplacementCost rho W = rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos u)) ↔
      W = fourTransport ![t, u] Real.pi 0 (-1) 1 ∨
      W = fourTransport ![t, u] 0 Real.pi 1 (-1) := by
  constructor
  · intro hcost
    obtain ⟨a, b, e, f, he, hf, hform⟩ := exists_fourTransport_of_mem_fiber ![t, u] W hW htrans
    have hef : e * f = -1 := by simpa only [hform, det_fourTransport] using hdet
    have hf' : f = -e := by rcases he with rfl | rfl <;> linarith
    subst f
    rw [hform] at hcost
    obtain h | h := (fourTransport_opposite_minimizers_of_lt t u a b e hu hut ht he rho hrho hzero).mp hcost
    · obtain ⟨rfl, ha, hb⟩ := h
      right
      simpa only [fourTransport, TauCeti.Matrix.planeOrthogonal_eq_at_zero_of_cos_eq_one a 1 ha,
        TauCeti.Matrix.planeOrthogonal_eq_at_pi_of_cos_eq_neg_one b (-1) hb] using hform
    · obtain ⟨rfl, ha, hb⟩ := h
      left
      simpa only [fourTransport, neg_neg,
        TauCeti.Matrix.planeOrthogonal_eq_at_pi_of_cos_eq_neg_one a (-1) ha,
        TauCeti.Matrix.planeOrthogonal_eq_at_zero_of_cos_eq_one b 1 hb] using hform
  · rintro (rfl | rfl)
    · exact four_negative_transport_cost_attained t u hu hut.le ht rho hzero
    · have hcost := fourTransport_opposite_cost t u 0 Real.pi 1 hu hut.le ht (Or.inl rfl) rho
      have htrace : oppositeFourTrace t u 0 Real.pi 1 = 2 * Real.cos u := by
        simp [oppositeFourTrace]
        ring
      simpa only [htrace, hzero, zero_add] using hcost

/-- The two negative-class reflection optimizers in the unequal-angle
classification are distinct actual matrices, at every angle pair. -/
theorem four_negative_reflections_ne (t u : ℝ) :
    fourTransport ![t, u] Real.pi 0 (-1) 1 ≠ fourTransport ![t, u] 0 Real.pi 1 (-1) := by
  intro h
  have hh := congrArg (fun W => (fourCSRotation ![t, u]).transpose * W) h
  simp only [fourTransport, ← Matrix.mul_assoc, transpose_mul_fourCSRotation, one_mul] at hh
  have hentry := congrArg
    (fun W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ => W (Sum.inl 0) (Sum.inl 0)) hh
  norm_num [TauCeti.Matrix.planeOrthogonal] at hentry

/-- For equal non-right angles the complete negative-class optimizer set
is the union of the two displayed one-parameter families. At angle zero
the same statement describes the optimal reflections preserving the source. -/
theorem four_negative_transport_minimizers_of_eq
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < Real.pi / 2)
    (rho : ℝ → ℝ) (hrho : StrictMonoOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0)
    (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (hW : W.transpose * W = 1) (hdet : W.det = -1)
    (htrans : W * fourSourceProjection * W.transpose =
      fourCSRotation ![t, t] * fourSourceProjection * (fourCSRotation ![t, t]).transpose) :
    fourDisplacementCost rho W = rho 2 + 2 * rho (Real.sqrt (2 - 2 * Real.cos t)) ↔
      (∃ b : ℝ, W = fourTransport ![t, t] 0 b 1 (-1)) ∨
      (∃ a : ℝ, W = fourTransport ![t, t] a 0 (-1) 1) := by
  constructor
  · intro hcost
    obtain ⟨a, b, e, f, he, hf, hform⟩ := exists_fourTransport_of_mem_fiber ![t, t] W hW htrans
    have hef : e * f = -1 := by simpa only [hform, det_fourTransport] using hdet
    have hf' : f = -e := by rcases he with rfl | rfl <;> linarith
    subst f
    rw [hform] at hcost
    obtain h | h := (fourTransport_opposite_minimizers_of_eq t a b e ht0 ht he rho hrho hzero).mp hcost
    · obtain ⟨rfl, ha⟩ := h
      left
      refine ⟨b, ?_⟩
      simpa only [fourTransport, TauCeti.Matrix.planeOrthogonal_eq_at_zero_of_cos_eq_one a 1 ha] using hform
    · obtain ⟨rfl, hb⟩ := h
      right
      refine ⟨a, ?_⟩
      simpa only [fourTransport, neg_neg,
        TauCeti.Matrix.planeOrthogonal_eq_at_zero_of_cos_eq_one b 1 hb] using hform
  · rintro (⟨b, rfl⟩ | ⟨a, rfl⟩)
    · have hcost := fourTransport_opposite_cost t t 0 b 1 ht0 le_rfl ht.le (Or.inl rfl) rho
      have htrace : oppositeFourTrace t t 0 b 1 = 2 * Real.cos t := by
        simp [oppositeFourTrace]
        ring
      simpa only [htrace, hzero, zero_add] using hcost
    · have hcost := fourTransport_opposite_cost t t a 0 (-1) ht0 le_rfl ht.le (Or.inr rfl) rho
      have htrace : oppositeFourTrace t t a 0 (-1) = 2 * Real.cos t := by
        simp [oppositeFourTrace]
        ring
      simpa only [htrace, hzero, zero_add, neg_neg] using hcost

/-- Every ambient determinant-negative transporter at the right-angle pair
has the same literal cost. This is a theorem about the full fiber, rather
than just one prescribed reflection or rotation block. -/
theorem four_negative_transport_cost_at_right_angles
    (rho : ℝ → ℝ) (hzero : rho 0 = 0)
    (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (hW : W.transpose * W = 1) (hdet : W.det = -1)
    (htrans : W * fourSourceProjection * W.transpose =
      fourCSRotation ![Real.pi / 2, Real.pi / 2] * fourSourceProjection *
        (fourCSRotation ![Real.pi / 2, Real.pi / 2]).transpose) :
    fourDisplacementCost rho W = rho 2 + 2 * rho (Real.sqrt 2) := by
  obtain ⟨a, b, e, f, he, hf, hform⟩ :=
    exists_fourTransport_of_mem_fiber ![Real.pi / 2, Real.pi / 2] W hW htrans
  have hef : e * f = -1 := by simpa only [hform, det_fourTransport] using hdet
  have hf' : f = -e := by rcases he with rfl | rfl <;> linarith
  subst f
  rw [hform]
  exact fourTransport_opposite_cost_at_right_angles a b e he rho hzero

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
