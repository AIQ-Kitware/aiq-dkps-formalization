/-
Deterministic covariance-floor transfer for raw-response Quench.

This module isolates the first hard spectral-regularity seam from the random
sampling development.  A population quadratic-form floor and entrywise
covariance closeness imply a retained empirical quadratic-form floor.  The
proof does not add measurability or compactness hypotheses: the nondegeneracy
certificate itself forces integrability of every squared linear form with
nonzero coefficient vector, and polarization supplies the coordinate-product
integrability needed to expand the covariance matrix.
-/

import DkpsQuench2026.Geometry.Population
import ForMathlib.Analysis.Matrix.EntrywiseOpNorm

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open scoped RealInnerProductSpace InnerProductSpace Matrix
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

open Acharyya2024
open Acharyya2025.Bridge
open Acharyya2025.Deterministic

universe u v

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- Population covariance matrix around a supplied center. -/
noncomputable def perspectiveCovarianceMatrix
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d) (center : Vec d) : DisMat d :=
  fun i j => ∫ f, (ψ f - center) i * (ψ f - center) j ∂Pf

/-- A safe entrywise covariance tolerance.  The `d+1` denominator avoids a
special zero-dimensional branch while leaving more than enough slack for the
finite-dimensional `ℓ¹`--`ℓ²` estimate. -/
noncomputable def covarianceEntryTolerance (d : Nat) (κ : Real) : Real :=
  κ / (4 * (d + 1))

/-- Every population squared linear form is integrable under a positive
nondegeneracy certificate.

For a nonzero coefficient vector the quadratic floor makes the integral
strictly positive, whereas the Bochner integral of a nonintegrable function is
zero.  The zero coefficient vector is immediate. -/
private theorem integrable_population_linearForm_sq
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (x : Vec d) :
    Integrable
      (fun f => ((∑ j : Fin d,
        x j * (ψ f - perspectiveMean Pf ψ) j)) ^ 2) Pf := by
  by_cases hx : x = 0
  · subst x
    simp
  · apply Integrable.of_integral_ne_zero
    intro hzero
    have hnorm_pos : 0 < ‖x‖ ^ 2 := by
      have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      positivity
    have hfloor := Hnondeg.quadratic_floor x
    rw [hzero] at hfloor
    nlinarith [Hnondeg.kappa_pos]

/-- Products of centered coordinates are integrable.  This is recovered from
squared-linear-form integrability by the polarization identity
`uv = ((u+v)^2-u^2-v^2)/2`. -/
private theorem integrable_population_coordinate_mul
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (a b : Fin d) :
    Integrable
      (fun f =>
        (ψ f - perspectiveMean Pf ψ) a *
          (ψ f - perspectiveMean Pf ψ) b) Pf := by
  let ea : Vec d := EuclideanSpace.single a (1 : Real)
  let eb : Vec d := EuclideanSpace.single b (1 : Real)
  have haa := integrable_population_linearForm_sq Pf ψ Hnondeg ea
  have hbb := integrable_population_linearForm_sq Pf ψ Hnondeg eb
  have hab := integrable_population_linearForm_sq Pf ψ Hnondeg (ea + eb)
  have hcomb := ((hab.sub haa).sub hbb).div_const (2 : Real)
  convert hcomb using 1
  funext f
  have hea :
      (∑ j : Fin d, ea j * (ψ f - perspectiveMean Pf ψ) j) =
        (ψ f - perspectiveMean Pf ψ) a := by
    simp [ea, EuclideanSpace.single]
  have heb :
      (∑ j : Fin d, eb j * (ψ f - perspectiveMean Pf ψ) j) =
        (ψ f - perspectiveMean Pf ψ) b := by
    simp [eb, EuclideanSpace.single]
  have heab :
      (∑ j : Fin d, (ea + eb) j * (ψ f - perspectiveMean Pf ψ) j) =
        (ψ f - perspectiveMean Pf ψ) a +
          (ψ f - perspectiveMean Pf ψ) b := by
    simp [ea, eb, EuclideanSpace.single, add_mul, Finset.sum_add_distrib]
  change
    (ψ f - perspectiveMean Pf ψ) a *
        (ψ f - perspectiveMean Pf ψ) b =
      (((∑ j : Fin d, (ea + eb) j *
            (ψ f - perspectiveMean Pf ψ) j) ^ 2 -
          (∑ j : Fin d, ea j *
            (ψ f - perspectiveMean Pf ψ) j) ^ 2) -
        (∑ j : Fin d, eb j *
          (ψ f - perspectiveMean Pf ψ) j) ^ 2) / 2
  rw [hea, heb, heab]
  ring

/-- The population covariance quadratic form is exactly the integral of the
corresponding squared centered linear form. -/
private theorem population_covariance_quadratic_eq_integral
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (x : Vec d) :
    (∑ a : Fin d, ∑ b : Fin d,
      x a * perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ) a b * x b) =
      ∫ f, ((∑ j : Fin d,
        x j * (ψ f - perspectiveMean Pf ψ) j)) ^ 2 ∂Pf := by
  symm
  calc
    (∫ f, ((∑ j : Fin d,
        x j * (ψ f - perspectiveMean Pf ψ) j)) ^ 2 ∂Pf)
        = ∫ f, ∑ a : Fin d, ∑ b : Fin d,
            (x a * x b) *
              ((ψ f - perspectiveMean Pf ψ) a *
                (ψ f - perspectiveMean Pf ψ) b) ∂Pf := by
            apply integral_congr_ae
            filter_upwards with f
            simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = ∑ a : Fin d, ∫ f, ∑ b : Fin d,
          (x a * x b) *
            ((ψ f - perspectiveMean Pf ψ) a *
              (ψ f - perspectiveMean Pf ψ) b) ∂Pf := by
            apply integral_finsetSum
            intro a _
            apply integrable_finsetSum
            intro b _
            exact (integrable_population_coordinate_mul Pf ψ Hnondeg a b).const_mul _
    _ = ∑ a : Fin d, ∑ b : Fin d, ∫ f,
          (x a * x b) *
            ((ψ f - perspectiveMean Pf ψ) a *
              (ψ f - perspectiveMean Pf ψ) b) ∂Pf := by
            apply Finset.sum_congr rfl
            intro a _
            apply integral_finsetSum
            intro b _
            exact (integrable_population_coordinate_mul Pf ψ Hnondeg a b).const_mul _
    _ = ∑ a : Fin d, ∑ b : Fin d,
          (x a * x b) *
            ∫ f, (ψ f - perspectiveMean Pf ψ) a *
              (ψ f - perspectiveMean Pf ψ) b ∂Pf := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [integral_const_mul]
    _ = ∑ a : Fin d, ∑ b : Fin d,
          x a * perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ) a b * x b := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            simp only [perspectiveCovarianceMatrix]
            ring

/-- Entrywise covariance closeness preserves a uniform quadratic-form floor.

The population quadratic form is recovered exactly from the nondegeneracy
integral.  The perturbation quadratic form is bounded by
`ε * (∑ |xᵢ|)^2`, then by `d * ε * ‖x‖²`.  With
`ε = κ / (4(d+1))` this costs at most `κ/2 * ‖x‖²`, so at least half of the
population floor remains.  No random-sampling or compactness premise is used. -/
theorem empiricalCovariance_quadratic_floor_of_entrywise
    {d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (A : DisMat d)
    (hclose : EntrywiseClose A
      (perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ))
      (covarianceEntryTolerance d κ))
    (x : Vec d) :
    (κ / 2) * ‖x‖ ^ 2 ≤
      ∑ a, ∑ b, x a * A a b * x b := by
  let C := perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ)
  let ε := covarianceEntryTolerance d κ
  let qA : Real := ∑ a : Fin d, ∑ b : Fin d, x a * A a b * x b
  let qC : Real := ∑ a : Fin d, ∑ b : Fin d, x a * C a b * x b
  let qE : Real := ∑ a : Fin d, ∑ b : Fin d, x a * (A a b - C a b) * x b
  change (κ / 2) * ‖x‖ ^ 2 ≤ qA

  have hcloseC : EntrywiseClose A C ε := by
    simpa [C, ε] using hclose

  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε, covarianceEntryTolerance]
    exact div_nonneg Hnondeg.kappa_pos.le (by positivity)

  have hqC_floor : κ * ‖x‖ ^ 2 ≤ qC := by
    calc
      κ * ‖x‖ ^ 2
          ≤ ∫ f, ((∑ j : Fin d,
              x j * (ψ f - perspectiveMean Pf ψ) j)) ^ 2 ∂Pf :=
            Hnondeg.quadratic_floor x
      _ = qC := by
            dsimp [qC, C]
            exact (population_covariance_quadratic_eq_integral
              Pf ψ Hnondeg x).symm

  have herror_l1 :
      |qE| ≤ ε * (∑ a : Fin d, |x a|) ^ 2 := by
    dsimp [qE]
    calc
      |∑ a : Fin d, ∑ b : Fin d, x a * (A a b - C a b) * x b|
          ≤ ∑ a : Fin d, |∑ b : Fin d,
              x a * (A a b - C a b) * x b| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin d, ∑ b : Fin d,
            |x a * (A a b - C a b) * x b| := by
            apply Finset.sum_le_sum
            intro a _
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin d, ∑ b : Fin d,
            |x a| * ε * |x b| := by
            apply Finset.sum_le_sum
            intro a _
            apply Finset.sum_le_sum
            intro b _
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hcloseC a b) (abs_nonneg _))
              (abs_nonneg _)
      _ = ε * (∑ a : Fin d, |x a|) ^ 2 := by
            rw [pow_two]
            simp only [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring

  have hl1 :
      ∑ a : Fin d, |x a| ≤ Real.sqrt d * ‖x‖ := by
    simpa [Real.norm_eq_abs, Fintype.card_fin] using
      (ForMathlib.sum_norm_le_sqrt_card_mul_norm x)

  have hl1_sq :
      (∑ a : Fin d, |x a|) ^ 2 ≤ (d : Real) * ‖x‖ ^ 2 := by
    have hsum_nonneg : 0 ≤ ∑ a : Fin d, |x a| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hrhs_nonneg : 0 ≤ Real.sqrt d * ‖x‖ := by positivity
    have hsq :
        (∑ a : Fin d, |x a|) ^ 2 ≤
          (Real.sqrt d * ‖x‖) ^ 2 := by
      nlinarith
    calc
      (∑ a : Fin d, |x a|) ^ 2
          ≤ (Real.sqrt d * ‖x‖) ^ 2 := hsq
      _ = (d : Real) * ‖x‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity : (0 : Real) ≤ (d : Real))]

  have herror_dim : |qE| ≤ ((d : Real) * ε) * ‖x‖ ^ 2 := by
    calc
      |qE| ≤ ε * (∑ a : Fin d, |x a|) ^ 2 := herror_l1
      _ ≤ ε * ((d : Real) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hl1_sq hε_nonneg
      _ = ((d : Real) * ε) * ‖x‖ ^ 2 := by ring

  have hcoeff : (d : Real) * ε ≤ κ / 2 := by
    have hden : 0 < (4 : Real) * ((d : Real) + 1) := by positivity
    have hratio :
        (d : Real) / ((4 : Real) * ((d : Real) + 1)) ≤ (1 : Real) / 4 := by
      apply (div_le_iff₀ hden).2
      calc
        (d : Real) ≤ (d : Real) + 1 := by linarith
        _ = ((1 : Real) / 4) * ((4 : Real) * ((d : Real) + 1)) := by ring
    dsimp [ε, covarianceEntryTolerance]
    change
      (d : Real) * (κ / (4 * ((d : Real) + 1))) ≤ κ / 2
    calc
      (d : Real) * (κ / (4 * ((d : Real) + 1)))
          = κ * ((d : Real) / ((4 : Real) * ((d : Real) + 1))) := by
              ring
      _ ≤ κ * ((1 : Real) / 4) :=
          mul_le_mul_of_nonneg_left hratio (le_of_lt Hnondeg.kappa_pos)
      _ ≤ κ / 2 := by nlinarith [Hnondeg.kappa_pos]

  have herror_half : |qE| ≤ (κ / 2) * ‖x‖ ^ 2 := by
    calc
      |qE| ≤ ((d : Real) * ε) * ‖x‖ ^ 2 := herror_dim
      _ ≤ (κ / 2) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖x‖)

  have hsplit : qA = qC + qE := by
    dsimp [qA, qC, qE]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring

  have herror_lower : -(κ / 2 * ‖x‖ ^ 2) ≤ qE :=
    (abs_le.mp herror_half).1
  rw [hsplit]
  nlinarith

end DkpsQuench2026
