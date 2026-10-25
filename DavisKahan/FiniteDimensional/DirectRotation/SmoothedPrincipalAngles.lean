/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSubspaceOptimization
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteSpectralTrace

public import DavisKahan.Geometry.Angle.CosineKernel

/-!
# The principal-angle formula for exact smoothed transport

The canonical paired cosine basis computes the directed sine spectral trace.
The accepted principal sines therefore identify its plane angles with the
accepted principal angles for every zero-preserving spectral sum.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- A paired canonical cosine basis computes every zero-preserving sum
of the accepted principal-angle sequence, without a sorting convention. -/
theorem sum_principalAngles_eq_paired_sum
    (U V : Submodule ℂ E) {n m : ℕ}
    (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta : Fin n → ℝ) (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (hC0 : ∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (0, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (0, i)))
    (hC1 : ∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (1, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (1, i)))
    (hCf : ∀ j, Proposition35.section3CosAngleOperator U V (e (.inr j)) = e (.inr j))
    (hJ0 : ∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i)))
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : Fin (Module.finrank ℂ U), f (U.principalAngles V i)) =
      ∑ i, f (theta i) := by
  let S := U.sinAngleOperator V
  have hS0 (i) : S (e (.inl (0, i))) = (Real.sin (theta i) : ℂ) • e (.inl (0, i)) := by
    exact Proposition35.sine_apply_of_cosine_apply U V _ _ ⟨(hθ i).1.le, (hθ i).2⟩ (hC0 i)
  have hS1 (i) : S (e (.inl (1, i))) = (Real.sin (theta i) : ℂ) • e (.inl (1, i)) := by
    exact Proposition35.sine_apply_of_cosine_apply U V _ _ ⟨(hθ i).1.le, (hθ i).2⟩ (hC1 i)
  have hSf (j) : S (e (.inr j)) = 0 := by
    have hc : Proposition35.section3CosAngleOperator U V (e (.inr j)) =
        (Real.cos 0 : ℂ) • e (.inr j) := by simpa using hCf j
    have hs := Proposition35.sine_apply_of_cosine_apply U V (e (.inr j)) 0
      ⟨le_rfl, by positivity⟩ hc
    change S (e (.inr j)) = (Real.sin 0 : ℂ) • e (.inr j) at hs
    simpa only [Real.sin_zero, Complex.ofReal_zero, zero_smul] using hs
  let : IsStarNormal S := (U.isPositive_sinAngleOperator V).isSelfAdjoint.isStarNormal
  have htrace := re_trace_cfc_mul_projection_of_paired_eigenbasis U S e
    (fun i => Real.sin (theta i)) hS0 hS1 hSf hJ0 (fun s => f (Real.arcsin s))
    (by simpa using hf)
  rw [U.re_trace_cfc_sinAngleOperator_mul_starProjection V
    (fun s => f (Real.arcsin s)) (by simpa using hf)] at htrace
  have hasin (i) : Real.arcsin (Real.sin (theta i)) = theta i :=
    Real.arcsin_sin (by linarith [(hθ i).1, Real.pi_pos]) (hθ i).2
  simpa only [← Submodule.principalAngles_apply, hasin] using htrace

/-- A bound on every nonzero paired cosine angle also bounds every accepted
principal angle, including the additional zero angles. -/
theorem principalAngles_le_of_paired_angles_le
    (U V : Submodule ℂ E) {n m : ℕ}
    (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta : Fin n → ℝ) (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (hC0 : ∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (0, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (0, i)))
    (hC1 : ∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (1, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (1, i)))
    (hCf : ∀ j, Proposition35.section3CosAngleOperator U V (e (.inr j)) = e (.inr j))
    (hJ0 : ∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i)))
    (bound : ℝ) (hbound : 0 ≤ bound) (hmax : ∀ i, theta i ≤ bound) :
    ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ bound := by
  have hsum := sum_principalAngles_eq_paired_sum U V e theta hθ hC0 hC1 hCf hJ0
    (fun t => max 0 (t - bound)) (max_eq_left (by linarith))
  have hz : (∑ i, max 0 (theta i - bound)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact max_eq_left (sub_nonpos.mpr (hmax i))
  rw [hz] at hsum
  intro i
  have hterm : max 0 (U.principalAngles V i - bound) ≤ 0 := by
    calc
      _ ≤ ∑ j : Fin (Module.finrank ℂ U), max 0 (U.principalAngles V j - bound) :=
        Finset.single_le_sum (fun j _ => le_max_left _ _) (Finset.mem_univ i)
      _ = 0 := hsum
  exact sub_nonpos.mp ((le_max_right _ _).trans hterm)

/-- An upper bound on the accepted principal angles also bounds every
nonzero angle in a paired canonical cosine basis. -/
theorem paired_angles_le_of_principalAngles_le
    (U V : Submodule ℂ E) {n m : ℕ}
    (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta : Fin n → ℝ) (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (hC0 : ∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (0, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (0, i)))
    (hC1 : ∀ i, Proposition35.section3CosAngleOperator U V (e (.inl (1, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (1, i)))
    (hCf : ∀ j, Proposition35.section3CosAngleOperator U V (e (.inr j)) = e (.inr j))
    (hJ0 : ∀ i, U.reflection (e (.inl (0, i))) = e (.inl (1, i)))
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hmax : ∀ i : Fin (Module.finrank ℂ U), U.principalAngles V i ≤ bound) :
    ∀ i, theta i ≤ bound := by
  have hsum := sum_principalAngles_eq_paired_sum U V e theta hθ hC0 hC1 hCf hJ0
    (fun t => max 0 (t - bound)) (max_eq_left (by linarith))
  have hz : (∑ i : Fin (Module.finrank ℂ U), max 0 (U.principalAngles V i - bound)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact max_eq_left (sub_nonpos.mpr (hmax i))
  rw [hz] at hsum
  intro i
  have hterm : max 0 (theta i - bound) ≤ 0 := by
    calc
      _ ≤ ∑ j, max 0 (theta j - bound) :=
        Finset.single_le_sum (fun j _ => le_max_left _ _) (Finset.mem_univ i)
      _ = 0 := hsum.symm
  exact sub_nonpos.mp ((le_max_right _ _).trans hterm)

/-- The explicit cosine spectral trace, after its ambient baseline is
removed, equals the sum of the scalar minima over the accepted principal
angles. This identity includes all zero and right principal angles. -/
theorem weightedRotationMinimum_sub_baseline_eq_sum_principalAngles
    (a b : ℝ) (hab : b ≤ a) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    weightedRotationMinimum a b (Proposition35.section3CosAngleOperator U V) -
        Module.finrank ℂ E * (a - b) =
      ∑ i : Fin (Module.finrank ℂ U),
        (weightedPhaseMinimum a b (U.principalAngles V i) - 2 * (a - b)) := by
  obtain ⟨n, m, e, theta, hθ, hC0, hC1, hCf, hJ0⟩ :=
    exists_subspace_paired_cosine_basis U V hUV
  let C := Proposition35.section3CosAngleOperator U V
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg U V)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  have hvalue := weightedRotationMinimum_eq_paired_sum a b hab C theta hθ e hC0 hC1 hCf
  have hsum := sum_principalAngles_eq_paired_sum U V e theta hθ hC0 hC1 hCf hJ0
    (fun t => weightedPhaseMinimum a b t - 2 * (a - b))
    (by rw [weightedPhaseMinimum_zero a b hab, sub_self])
  have hdim : Module.finrank ℂ E = 2 * n + m := by
    simpa using Module.finrank_eq_card_basis e.toBasis
  have hdimR : (Module.finrank ℂ E : ℝ) = 2 * (n : ℝ) + m := by exact_mod_cast hdim
  change weightedRotationMinimum a b C - _ = _
  rw [hsum, hvalue, hdimR, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The exact unrestricted smoothed transport value is the sum of its
explicit scalar formula over the accepted principal angles. -/
theorem smoothedTransportMinimum_eq_sum_principalAngles
    (tau : ℝ) (hτ : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    smoothedTransportMinimum tau U V =
      ∑ i : Fin (Module.finrank ℂ U), smoothedPhaseMinimum tau (U.principalAngles V i) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau hτ
  have hab : a⁻¹ ≤ a := (inv_le_one_of_one_le₀ ha.le).trans ha.le
  have hsum := weightedRotationMinimum_sub_baseline_eq_sum_principalAngles a a⁻¹ hab U V hUV
  rw [show a - a⁻¹ = tau from smoothingRadius_sub_inv tau hτ] at hsum
  change weightedRotationMinimum a a⁻¹ _ - Module.finrank ℂ E * tau = _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact (smoothedPhaseMinimum_eq_weighted tau (U.principalAngles V i) hτ).symm

/-- **Exact global smoothed transport theorem.** An ambient unitary attains
the sum of the explicit scalar minima over the principal angles, and every
unitary carrying the source onto the target has at least this cost. -/
theorem exists_unitary_minimizing_smoothed_transport_principalAngles
    (tau : ℝ) (hτ : 0 < tau) (U V : Submodule ℂ E)
    (hUV : Module.finrank ℂ U = Module.finrank ℂ V) :
    ∃ W : E ≃ₗᵢ[ℂ] E,
      U.map W.toLinearMap = V ∧
      smoothedDisplacementCost tau W.toLinearMap =
        (∑ i : Fin (Module.finrank ℂ U), smoothedPhaseMinimum tau (U.principalAngles V i)) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, U.map T.toLinearMap = V →
        (∑ i : Fin (Module.finrank ℂ U), smoothedPhaseMinimum tau (U.principalAngles V i)) ≤
          smoothedDisplacementCost tau T.toLinearMap := by
  obtain ⟨W, hWmap, hcost, hmin⟩ := exists_unitary_minimizing_smoothed_transport tau hτ U V hUV
  rw [smoothedTransportMinimum_eq_sum_principalAngles tau hτ U V hUV] at hcost
  exact ⟨W, hWmap, hcost, fun T hT => hcost ▸ hmin T hT⟩

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
