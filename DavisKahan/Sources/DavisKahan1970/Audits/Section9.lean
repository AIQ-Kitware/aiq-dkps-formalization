/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section9.All

/-!
# Dependency audit for the Section 9 numerical example

Compile this module after repairing any elaboration issues, then inspect the
printed dependency sets before promoting the certificate bridge to exact source
coverage.
-/

namespace ForMathlib
namespace DavisKahan1970
namespace Section9

#check initial_residual_gram_from_affine_moments
#check recentered_residual_gram_from_affine_moments
#check residualGram_eigenvalueLow_charAt
#check residualGram_eigenvalueHigh_charAt
#check equation_9_1
#check equation_9_2
#check equation_9_3
#check equation_9_4
#check equation_9_5_low
#check equation_9_5_high
#check equation_9_6
#check equation_9_7
#check equation_9_8_lower
#check equation_9_8_upper
#check block_eigenproblem_iff
#check schur_complement_reduction
#check half_tanTwoPsi_ratio_lt_of_eigenvalue_upper
#check individual_angle_le_exact_envelope
#check final_lower_individual_angle_bound
#check final_upper_individual_angle_bound
#check NumericalExampleCertificate.printedConclusions

#print axioms initial_residual_gram_from_affine_moments
#print axioms recentered_residual_gram_from_affine_moments
#print axioms block_eigenproblem_iff
#print axioms schur_complement_reduction
#print axioms half_tanTwoPsi_ratio_lt_of_eigenvalue_upper
#print axioms NumericalExampleCertificate.printedConclusions

end Section9
end DavisKahan1970
end ForMathlib
