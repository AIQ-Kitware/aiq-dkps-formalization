/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.GenuineAllGap
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineOrderedEngine

/-!
# Full unbounded sine-theta trusted-dependency audit

Compile this leaf directly to inspect the trusted dependencies of the two
ordered engines, the genuine all-gap Sylvester theorem, and the final
source-shaped sine-theta capstones.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

#check GenuineOrderedSylvesterEngine
#check canonicalGenuineOrderedSylvesterEngine
#check davisKahan1970_sylvester_of_genuineSpectrumGap
#check generalizedSinTheta_unbounded_exact_of_genuineSpectrumGap
#check sinTheta_unbounded_exact_of_genuineSpectrumGap
#check GenuineGeneralSinThetaProblem.result
#check GenuineIsometricSinThetaProblem.result

#print axioms canonicalGenuineOrderedSylvesterEngine
#print axioms davisKahan1970_sylvester_of_genuineSpectrumGap
#print axioms generalizedSinTheta_unbounded_exact_of_genuineSpectrumGap
#print axioms sinTheta_unbounded_exact_of_genuineSpectrumGap
#print axioms GenuineGeneralSinThetaProblem.result
#print axioms GenuineIsometricSinThetaProblem.result

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
