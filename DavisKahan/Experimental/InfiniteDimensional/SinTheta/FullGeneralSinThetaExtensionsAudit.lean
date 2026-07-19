/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions

/-!
# Trusted-dependency audit for optional natural-input extensions

Compile this leaf only after every imported extension module builds from
source.  The established source endpoints are repeated here so a repair pass
cannot accidentally regress the theorem completed at the base commit.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

#check ForMathlib.DavisKahan1970.sinTheta
#check ForMathlib.DavisKahan1970.generalizedSinTheta
#check ForMathlib.DavisKahan1970.sinTheta_real
#check ForMathlib.DavisKahan1970.generalizedSinTheta_real
#check ForMathlib.DavisKahan1970.sinTheta_real_spectralSubspace
#check ForMathlib.DavisKahan1970.generalizedSinTheta_real_spectralSubspace
#check ForMathlib.DavisKahan1970.generalizedSinTheta_spectralSubspace
#check ForMathlib.DavisKahan1970.sinTheta_reducingSubspace_complex
#check ForMathlib.DavisKahan1970.sinTheta_reducingSubspace_real
#check ForMathlib.DavisKahan1970.generalizedSinTheta_reducingSubspace_complex
#check ForMathlib.DavisKahan1970.generalizedSinTheta_reducingSubspace_real
#check ForMathlib.DavisKahan1970.sinTheta_bounded_spectralSubspace
#check ForMathlib.DavisKahan1970.generalizedSinTheta_bounded_spectralSubspace
#check ForMathlib.DavisKahan1970.sinTheta_bounded_real_spectralSubspace
#check ForMathlib.DavisKahan1970.generalizedSinTheta_bounded_real_spectralSubspace
#check mul_subspaceGap_le_of_two_directedGap_le
#check mul_subspaceGap_le_max_of_two_directedGap_le

#print axioms ForMathlib.DavisKahan1970.sinTheta
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta
#print axioms ForMathlib.DavisKahan1970.sinTheta_real
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_real
#print axioms ForMathlib.DavisKahan1970.sinTheta_real_spectralSubspace
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_real_spectralSubspace
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_spectralSubspace
#print axioms ForMathlib.DavisKahan1970.sinTheta_reducingSubspace_complex
#print axioms ForMathlib.DavisKahan1970.sinTheta_reducingSubspace_real
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_reducingSubspace_complex
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_reducingSubspace_real
#print axioms ForMathlib.DavisKahan1970.sinTheta_bounded_spectralSubspace
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_bounded_spectralSubspace
#print axioms ForMathlib.DavisKahan1970.sinTheta_bounded_real_spectralSubspace
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_bounded_real_spectralSubspace
#print axioms mul_subspaceGap_le_of_two_directedGap_le
#print axioms mul_subspaceGap_le_max_of_two_directedGap_le

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
