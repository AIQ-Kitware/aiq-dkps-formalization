/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds
import DavisKahan.Sources.DavisKahan1970.Section9.SchurComplement

/-!
# Davis--Kahan 1970, Section 9: individual eigenvectors inside a cluster

This module isolates the scalar geometry used after the Schur-complement
reduction.  The exact coefficient `sqrt 7 / 10` is the Euclidean combination
of half of the `tan(2 psi)` coefficient and the complementary-coordinate
`tangent` coefficient.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- Coefficient multiplying the Schur-complement `tan(2 psi)` bound after the
factor one half. -/
noncomputable def halfTanTwoPsiCoefficient : ℝ := Real.sqrt 3 / 30

/-- Coefficient multiplying the complementary-coordinate tangent bound. -/
noncomputable def tanEtaCoefficient : ℝ := Real.sqrt 15 / 15

lemma combined_individual_coefficient_sq :
    halfTanTwoPsiCoefficient ^ 2 + tanEtaCoefficient ^ 2 = (7 : ℝ) / 100 := by
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h15 : Real.sqrt (15 : ℝ) ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  unfold halfTanTwoPsiCoefficient tanEtaCoefficient
  nlinarith

lemma combined_individual_coefficient :
    Real.sqrt (halfTanTwoPsiCoefficient ^ 2 + tanEtaCoefficient ^ 2) =
      Real.sqrt 7 / 10 := by
  -- rewrite the radicand as an explicit square and cancel, rather than asking
  -- `nlinarith` to match two square roots
  rw [combined_individual_coefficient_sq,
    show (7 : ℝ) / 100 = (Real.sqrt 7 / 10) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]; norm_num,
    Real.sqrt_sq (by positivity)]

/-- Abstract form of the final combination: if the squared target angle is
bounded by the squared in-plane and out-of-plane contributions, then a common
positive denominator yields the `sqrt 7 / 10` envelope. -/
theorem individual_angle_le_exact_envelope
    {omega psi eta ε denominator : ℝ}
    (homega0 : 0 ≤ omega)
    (hpsi0 : 0 ≤ psi) (heta0 : 0 ≤ eta)
    (hden : 0 < denominator)
    (homega : omega ^ 2 ≤ psi ^ 2 + eta ^ 2)
    (hpsi : psi ≤ halfTanTwoPsiCoefficient * ε / denominator)
    (heta : eta ≤ tanEtaCoefficient * ε / denominator)
    (hε : 0 ≤ ε) :
    omega ≤ (Real.sqrt 7 / 10) * ε / denominator := by
  have hp0 : 0 ≤ halfTanTwoPsiCoefficient := by
    unfold halfTanTwoPsiCoefficient
    positivity
  have he0 : 0 ≤ tanEtaCoefficient := by
    unfold tanEtaCoefficient
    positivity
  have hpsq : psi ^ 2 ≤
      (halfTanTwoPsiCoefficient * ε / denominator) ^ 2 := by
    nlinarith
  have hetasq : eta ^ 2 ≤
      (tanEtaCoefficient * ε / denominator) ^ 2 := by
    nlinarith
  have hcoeff := combined_individual_coefficient_sq
  have htargetsq : omega ^ 2 ≤
      ((Real.sqrt 7 / 10) * ε / denominator) ^ 2 := by
    calc
      omega ^ 2 ≤ psi ^ 2 + eta ^ 2 := homega
      _ ≤ (halfTanTwoPsiCoefficient * ε / denominator) ^ 2 +
          (tanEtaCoefficient * ε / denominator) ^ 2 := add_le_add hpsq hetasq
      _ = ((Real.sqrt 7 / 10) * ε / denominator) ^ 2 := by
        have h7 : Real.sqrt (7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
        field_simp [ne_of_gt hden]
        nlinarith
  have hright0 : 0 ≤ (Real.sqrt 7 / 10) * ε / denominator := by positivity
  nlinarith

end Section9
end DavisKahan1970
end TauCeti