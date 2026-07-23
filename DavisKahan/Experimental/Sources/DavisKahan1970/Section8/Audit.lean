/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.All

/-!
# Dependency audit for Davis--Kahan 1970 Section 8

Compile this module after repairing any elaboration issues.  The printed axiom
sets should contain only the standard classical/choice foundations inherited
from the spectral calculus, and no project-local admissions.
-/

namespace ForMathlib
namespace DavisKahan1970
namespace Section8

#check maximalAngle_selectedSpectralSubspaces_lt_pi_div_four
#check selectedBranchConclusion_of_contour_bound
#check orientedSpectralRepulsionConclusion
#check theorem81CoreConclusion
#check upperCompressionRepulsion_of_data
#check lowerCompressionRepulsion_of_data
#check theorem82_branch_of_perturbationHalfGapBridge
#check theorem82_branch_of_residualHalfGapBridge
#check theorem8_1_selectedBranch_and_spectralRepulsion
#check theorem8_2_perturbationHalfGap_selectedBranch
#check theorem8_selectedBranch_tan_maximalAngle_le_div

#print axioms maximalAngle_selectedSpectralSubspaces_lt_pi_div_four
#print axioms selectedBranchConclusion_of_contour_bound
#print axioms orientedSpectralRepulsionConclusion
#print axioms theorem81CoreConclusion
#print axioms upperCompressionRepulsion_of_data
#print axioms lowerCompressionRepulsion_of_data
#print axioms theorem82_branch_of_perturbationHalfGapBridge
#print axioms theorem82_branch_of_residualHalfGapBridge

end Section8
end DavisKahan1970
end ForMathlib
