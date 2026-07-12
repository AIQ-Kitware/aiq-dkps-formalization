/-
Centered empirical covariance identities for raw-response Quench.

This module isolates the deterministic finite-sum bridge between a feature-space
empirical covariance matrix and the average squared projections of the centered
configuration.  It is independent of reference-sampling probability and can be
compiled before the larger spectral-regularity module.
-/

import DkpsQuench2026.Geometry.Covariance

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

/-- Feature-space empirical covariance of a centered finite configuration. -/
noncomputable def centeredEmpiricalCovariance
    {n d : Nat} (z : Config n d) : DisMat d :=
  fun a b => (n : Real)⁻¹ * ∑ i : Fin n,
    centerConfig z i a * centerConfig z i b

/-- The quadratic form of the centered empirical covariance is the average of
squared projections onto the centered configuration.

This identity is purely finite-dimensional algebra.  It remains valid for
`n = 0`, because both sides then vanish. -/
theorem centeredEmpiricalCovariance_quadratic_eq_projection_sq
    {n d : Nat} (z : Config n d) (x : Vec d) :
    (∑ a : Fin d, ∑ b : Fin d,
      x a * centeredEmpiricalCovariance z a b * x b) =
      (n : Real)⁻¹ * ∑ i : Fin n,
        (∑ a : Fin d, x a * centerConfig z i a) ^ 2 := by
  let c : Fin n → Fin d → Real := fun i a => centerConfig z i a
  let r : Real := (n : Real)⁻¹

  have hentry (a b : Fin d) :
      x a * (r * ∑ i : Fin n, c i a * c i b) * x b =
        ∑ i : Fin n, r * ((x a * c i a) * (x b * c i b)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

  have hswap :
      (∑ a : Fin d, ∑ b : Fin d, ∑ i : Fin n,
        r * ((x a * c i a) * (x b * c i b))) =
        ∑ i : Fin n, ∑ a : Fin d, ∑ b : Fin d,
          r * ((x a * c i a) * (x b * c i b)) := by
    calc
      (∑ a : Fin d, ∑ b : Fin d, ∑ i : Fin n,
        r * ((x a * c i a) * (x b * c i b))) =
          ∑ a : Fin d, ∑ i : Fin n, ∑ b : Fin d,
            r * ((x a * c i a) * (x b * c i b)) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ a : Fin d, ∑ b : Fin d,
            r * ((x a * c i a) * (x b * c i b)) := by
              rw [Finset.sum_comm]

  have hfactor (i : Fin n) :
      (∑ a : Fin d, ∑ b : Fin d,
        r * ((x a * c i a) * (x b * c i b))) =
        r * ∑ a : Fin d, ∑ b : Fin d,
          (x a * c i a) * (x b * c i b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]

  have hsquare (i : Fin n) :
      (∑ a : Fin d, ∑ b : Fin d,
        (x a * c i a) * (x b * c i b)) =
        (∑ a : Fin d, x a * c i a) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]

  change
    (∑ a : Fin d, ∑ b : Fin d,
      x a * (r * ∑ i : Fin n, c i a * c i b) * x b) =
      r * ∑ i : Fin n, (∑ a : Fin d, x a * c i a) ^ 2
  calc
    (∑ a : Fin d, ∑ b : Fin d,
      x a * (r * ∑ i : Fin n, c i a * c i b) * x b)
        = ∑ a : Fin d, ∑ b : Fin d, ∑ i : Fin n,
            r * ((x a * c i a) * (x b * c i b)) := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              exact hentry a b
    _ = ∑ i : Fin n, ∑ a : Fin d, ∑ b : Fin d,
          r * ((x a * c i a) * (x b * c i b)) := hswap
    _ = ∑ i : Fin n, r * ∑ a : Fin d, ∑ b : Fin d,
          (x a * c i a) * (x b * c i b) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hfactor i
    _ = ∑ i : Fin n, r * (∑ a : Fin d, x a * c i a) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hsquare i]
    _ = r * ∑ i : Fin n, (∑ a : Fin d, x a * c i a) ^ 2 := by
          rw [Finset.mul_sum]

/-- Entrywise closeness of a centered empirical covariance to a nondegenerate
population covariance gives the corresponding average squared-projection floor.

This is the deterministic bridge consumed by the reference-sampling spectral
argument. -/
theorem centeredEmpiricalCovariance_quadratic_floor_of_entrywise
    {n d : Nat}
    (Pf : Measure (Model Q X))
    (ψ : Model Q X → Vec d)
    {κ : Real}
    (Hnondeg : PerspectiveNondegeneracy Pf ψ κ)
    (z : Config n d)
    (hclose : EntrywiseClose
      (centeredEmpiricalCovariance z)
      (perspectiveCovarianceMatrix Pf ψ (perspectiveMean Pf ψ))
      (covarianceEntryTolerance d κ))
    (x : Vec d) :
    (κ / 2) * ‖x‖ ^ 2 ≤
      (n : Real)⁻¹ * ∑ i : Fin n,
        (∑ a : Fin d, x a * centerConfig z i a) ^ 2 := by
  calc
    (κ / 2) * ‖x‖ ^ 2
        ≤ ∑ a : Fin d, ∑ b : Fin d,
            x a * centeredEmpiricalCovariance z a b * x b :=
          empiricalCovariance_quadratic_floor_of_entrywise
            Pf ψ Hnondeg (centeredEmpiricalCovariance z) hclose x
    _ = (n : Real)⁻¹ * ∑ i : Fin n,
          (∑ a : Fin d, x a * centerConfig z i a) ^ 2 :=
        centeredEmpiricalCovariance_quadratic_eq_projection_sq z x

end DkpsQuench2026
