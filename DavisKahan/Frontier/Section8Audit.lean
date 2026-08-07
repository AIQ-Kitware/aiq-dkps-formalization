/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8SourceSurface

/-!
# Dependency audit for Davis--Kahan 1970 Section 8

This is the audit leaf for the **actual final capstones** of Section 8.  It
lives downstream of the Frontier layer because that is where Section 8's
analytic content lives; the upstream leaf
`DavisKahan/Sources/DavisKahan1970/Audits/Section8.lean` continues to audit the
internal infrastructure, which is no longer evidence about the printed
theorems.

Every target below should report exactly

```
[propext, Classical.choice, Quot.sound]
```

and nothing project-local.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

/-! ## Theorem 8.1: the branch, its characterization, its uniqueness -/

#check theorem8_1_source
#check theorem8_1_source_characterization
#check theorem8_1_source_uniqueness

#print axioms theorem8_1_source
#print axioms theorem8_1_source_characterization
#print axioms theorem8_1_source_uniqueness

/-! ## Theorem 8.1(i), both blocks -/

#check theorem8_1_upperCompressionRepulsion_source
#check theorem8_1_lowerCompressionRepulsion_source

#print axioms theorem8_1_upperCompressionRepulsion_source
#print axioms theorem8_1_lowerCompressionRepulsion_source

/-! ## Theorem 8.1(ii), both blocks

The shared Weyl step, the dimension-free approximation-number statements, and
the printed angle form. -/

#check theorem8_1_upperSandwichApproximation_source
#check theorem8_1_lowerSandwichApproximation_source
#check theorem8_1_upperApproximationRepulsion_source
#check theorem8_1_lowerApproximationRepulsion_source
#check theorem8_1_upperApproximationRepulsion_angle_source
#check theorem8_1_lowerApproximationRepulsion_angle_source

#print axioms theorem8_1_upperSandwichApproximation_source
#print axioms theorem8_1_lowerSandwichApproximation_source
#print axioms theorem8_1_upperApproximationRepulsion_source
#print axioms theorem8_1_lowerApproximationRepulsion_source
#print axioms theorem8_1_upperApproximationRepulsion_angle_source
#print axioms theorem8_1_lowerApproximationRepulsion_angle_source

/-! ## Theorem 8.1(iii), both blocks

The weak-majorization cores, the every-symmetric-gauge forms, the printed angle
forms, and the paper's increasing index order. -/

#check theorem8_1_upperWeightedWeakMajorization_source
#check theorem8_1_lowerWeightedWeakMajorization_source
#check theorem8_1_upperSymmetricGaugeRepulsion_source
#check theorem8_1_lowerSymmetricGaugeRepulsion_source
#check theorem8_1_upperSymmetricGaugeRepulsion_angle_source
#check theorem8_1_lowerSymmetricGaugeRepulsion_angle_source
#check theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source
#check theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source

#print axioms theorem8_1_upperWeightedWeakMajorization_source
#print axioms theorem8_1_lowerWeightedWeakMajorization_source
#print axioms theorem8_1_upperSymmetricGaugeRepulsion_source
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion_source
#print axioms theorem8_1_upperSymmetricGaugeRepulsion_angle_source
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion_angle_source
#print axioms theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source
#print axioms theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source

/-! ## The eigenvalue/angle source dictionary -/

#check approximationNumber_eq_eigenvalues_of_isPositive
#check approximationNumber_upperBlockShift_eq_zero_of_le
#check approximationNumber_lowerBlockShift_eq_zero_of_le
#check approximationNumber_cosineBlock_eq_principalCosines
#check approximationNumber_lowerCosineBlock_eq_principalCosines
#check norm_cosineBlock_eq_principalCosines_zero
#check norm_lowerCosineBlock_eq_principalCosines_zero
#check cos_arccos_approximationNumber_cosineBlock
#check arcsin_one_div_two
#check maximalAngle_le_pi_div_six_iff

#print axioms approximationNumber_eq_eigenvalues_of_isPositive
#print axioms approximationNumber_upperBlockShift_eq_zero_of_le
#print axioms approximationNumber_lowerBlockShift_eq_zero_of_le
#print axioms approximationNumber_cosineBlock_eq_principalCosines
#print axioms approximationNumber_lowerCosineBlock_eq_principalCosines
#print axioms norm_cosineBlock_eq_principalCosines_zero
#print axioms norm_lowerCosineBlock_eq_principalCosines_zero
#print axioms cos_arccos_approximationNumber_cosineBlock
#print axioms arcsin_one_div_two
#print axioms maximalAngle_le_pi_div_six_iff

/-! ## The generic sandwich majorization behind part (iii) -/

#check TauCeti.singularValues_adjoint_sandwich_weaklyMajorized
#check TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized

#print axioms TauCeti.singularValues_adjoint_sandwich_weaklyMajorized
#print axioms TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized

/-! ## Theorem 8.2

Both alternatives from the printed hypotheses, the inherited `sin 2Θ`
estimates, the Krein completion, equation (1.5), and the printed `Θ < π/4`. -/

#check theorem8_2_perturbationHalfGap_source
#check theorem8_2_residualHalfGap_source
#check theorem8_2_branch_source_directed
#check theorem8_2_krein_completion_source
#check theorem8_2_sinTwoTheta_perturbation_source
#check theorem8_2_sinTwoTheta_residual_source
#check subspaceGap_eq_directedGap_of_finrank_eq
#check theorem8_2_perturbationHalfGap_source_maximalAngle_lt
#check theorem8_2_residualHalfGap_source_maximalAngle_lt
#check theorem8_2_branch_source_maximalAngle_lt
#check theorem8_2_source

#print axioms theorem8_2_perturbationHalfGap_source
#print axioms theorem8_2_residualHalfGap_source
#print axioms theorem8_2_branch_source_directed
#print axioms theorem8_2_krein_completion_source
#print axioms theorem8_2_sinTwoTheta_perturbation_source
#print axioms theorem8_2_sinTwoTheta_residual_source
#print axioms subspaceGap_eq_directedGap_of_finrank_eq
#print axioms theorem8_2_perturbationHalfGap_source_maximalAngle_lt
#print axioms theorem8_2_residualHalfGap_source_maximalAngle_lt
#print axioms theorem8_2_branch_source_maximalAngle_lt
#print axioms theorem8_2_source

end Section8
end DavisKahan1970
end TauCeti
