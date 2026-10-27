/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseMinimum
public import DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceOptimality
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Attained Schatten costs for complex scalar-phase transports

The scalar optimizer is realized by a bundled unitary transporting the two
complex lines. Its actual Schatten norm is the `p`-th root of the scalar
power sum. These are attaining candidates for the unrestricted unitary
problem; the unrestricted lower bound is a separate theorem.
-/

public section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.DavisKahan1970.Section4Examples
open scoped ENNReal

noncomputable section

private def scalarPhaseIsometry (t : ℝ) : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane where
  toLinearEquiv := DistribMulAction.toLinearEquiv ℂ ComplexPlane (Circle.exp t)
  norm_map' x := by
    change ‖(Circle.exp t : ℂ) • x‖ = ‖x‖
    rw [norm_smul, Circle.norm_coe, one_mul]

private theorem circle_exp_eq_phase (t : ℝ) : (Circle.exp t : ℂ) = example42Phase t := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, example42Phase]

/-- A scalar phase of the canonical planar transport, constructed from the
existing endpoint unitary by a norm-one scalar multiplication. -/
def scalarPhaseTransport (theta delta : ℝ) : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane :=
  (ComplexTraceOptimality.phaseUnitary theta).trans (scalarPhaseIsometry (delta - theta))

private theorem scalarPhaseTransport_eq_smul (theta delta : ℝ) :
    (scalarPhaseTransport theta delta).toLinearMap =
      example42Phase (delta - theta) •
        (ComplexTraceOptimality.phaseUnitary theta).toLinearMap := by
  apply LinearMap.ext
  intro x
  change (Circle.exp (delta - theta) : ℂ) •
    (ComplexTraceOptimality.phaseUnitary theta) x = _
  rw [circle_exp_eq_phase]
  rfl

/-- The bundled unitary is the scalar competitor used in the singular-value
calculation, with no angle or phase restriction. -/
theorem scalarPhaseTransport_toLinearMap (theta delta : ℝ) :
    (scalarPhaseTransport theta delta).toLinearMap = example42Competitor theta delta := by
  rw [scalarPhaseTransport_eq_smul, ComplexTraceOptimality.phaseUnitary_toLinearMap,
    example42Competitor_eq_phase_smul, example42Competitor_eq_phase_smul,
    smul_smul, example42Phase_mul, sub_add_cancel]

/-- First coordinate of the actual planar phase transporter. -/
theorem scalarPhaseTransport_apply_zero (theta delta : ℝ) (x : ComplexPlane) :
    scalarPhaseTransport theta delta x 0 = example42Phase (theta + delta) * x 0 := by
  change (scalarPhaseTransport theta delta).toLinearMap x 0 = _
  rw [scalarPhaseTransport_toLinearMap]
  simp [example42Competitor, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

/-- Second coordinate of the actual planar phase transporter. -/
theorem scalarPhaseTransport_apply_one (theta delta : ℝ) (x : ComplexPlane) :
    scalarPhaseTransport theta delta x 1 = example42Phase (delta - theta) * x 1 := by
  change (scalarPhaseTransport theta delta).toLinearMap x 1 = _
  rw [scalarPhaseTransport_toLinearMap]
  simp [example42Competitor, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

/-- Scalar phases preserve the target line, so every member of this family
is an admissible unitary transport for the same pair of lines. -/
theorem scalarPhaseTransport_transports (theta delta : ℝ) :
    ComplexTraceOptimality.sourceLine.map (scalarPhaseTransport theta delta).toLinearMap =
      ComplexTraceOptimality.targetLine theta := by
  rw [scalarPhaseTransport_eq_smul]
  have hphase : example42Phase (delta - theta) ≠ 0 := by
    rw [← circle_exp_eq_phase]
    exact Circle.coe_ne_zero _
  rw [Submodule.map_smul _ _ _ hphase]
  exact ComplexTraceOptimality.phaseUnitary_transports theta

/-- The actual Schatten norm of a planar phase transport agrees with the
`p`-th root of the scalar objective. The exponent uses Tau Ceti's finite
Schatten seminorm directly. -/
theorem scalarPhaseTransport_schatten (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (theta delta : ℝ) (hδ : 0 ≤ delta) (hδθ : delta ≤ theta)
    (hπ : theta ≤ Real.pi / 2) :
    UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
      (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) =
        phasePower p.toReal theta delta ^ (1 / p.toReal) := by
  rw [scalarPhaseTransport_toLinearMap,
    UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp]
  congr 1
  let A : ComplexPlane →ₗ[ℂ] ComplexPlane := LinearMap.id - example42Competitor theta delta
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  have hsum := A.sum_fin_singularValues (fun s : ℝ => s ^ p.toReal)
    (Real.zero_rpow hp0.ne')
  change A.singularValues.sum (fun _ s => s ^ p.toReal) = _
  rw [← hsum]
  rw [show Module.finrank ℂ ComplexPlane = 2 from finrank_euclideanSpace_fin,
    Fin.sum_univ_two]
  rcases eq_or_lt_of_le hδθ with heq | hlt
  · subst delta
    have hsing := ComplexTraceOptimality.singularValues_phaseUnitary theta hδ hπ
    rw [ComplexTraceOptimality.phaseUnitary_toLinearMap] at hsing
    dsimp only [A]
    rw [hsing]
    have hhalf : (theta + theta) / 2 = theta := by ring
    simp only [Fin.val_zero, Fin.val_one, pairSingularValues_zero, pairSingularValues_one, phasePower,
      phaseChord, hhalf, sub_self, zero_div, Real.sin_zero, mul_zero,
      Real.zero_rpow hp0.ne', add_zero]
  · exact (phasePower_eq_singularValues_rpow p.toReal theta delta hδ hlt hπ).symm

/-- The scalar minimum is attained by an admissible complex unitary, and
that unitary minimizes the actual Schatten norm throughout the scalar-phase
family on the closed interval. -/
theorem exists_scalarPhaseTransport_minimizer
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (theta : ℝ) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    ∃ delta ∈ Set.Icc 0 theta,
      ComplexTraceOptimality.sourceLine.map (scalarPhaseTransport theta delta).toLinearMap =
          ComplexTraceOptimality.targetLine theta ∧
      UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) =
            phaseMinimum p.toReal theta ^ (1 / p.toReal) ∧
      ∀ eta ∈ Set.Icc 0 theta,
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - (scalarPhaseTransport theta eta).toLinearMap) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  obtain ⟨delta, hδ, heq, _⟩ := exists_attains_phaseMinimum p.toReal theta hp1 hθ.1
  have hcost := scalarPhaseTransport_schatten p hp theta delta hδ.1 hδ.2 hθ.2
  rw [← heq] at hcost
  refine ⟨delta, hδ, scalarPhaseTransport_transports theta delta, hcost, ?_⟩
  intro eta heta
  rw [hcost, scalarPhaseTransport_schatten p hp theta eta heta.1 heta.2 hθ.2]
  exact Real.rpow_le_rpow (phaseMinimum_nonneg p.toReal theta hp1 hθ)
    (phaseMinimum_le_phasePower p.toReal theta hp1 hθ.1 heta) (by positivity)

end
end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
