/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Specializations

/-!
# Davis--Kahan 1970 general sine-theta manuscript surface

The unqualified generalized target now assembles the complete 1970 gap
disjunction: finite interval/exterior separation and both ordered half-line
orientations.  The ordered branches use double spectral cutoff and finite
Ky Fan passage; the finite-interval theorem is also exposed separately through
the cleaner genuine-spectrum interface.  Foundational spectrum and
approximation-number obligations remain visible in the lower layers.
-/

namespace ForMathlib
namespace DavisKahan1970

/-- Complete generalized 1970 target, including ordered half-lines. -/
alias GeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.GeneralSinThetaProblem

/-- Completed genuine-spectrum finite interval/exterior problem. -/
alias FiniteIntervalGeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.FiniteIntervalGeneralSinThetaProblem

alias IsometricSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem

alias generalizedSinTheta :=
  DavisKahan.Experimental.ExactSinTheta.GeneralSinThetaProblem.result
alias generalizedSinTheta_complementaryBlock :=
  DavisKahan.Experimental.ExactSinTheta.GeneralSinThetaProblem.complementaryBlock_result

/-- Completed generalized finite interval/exterior theorem. -/
alias generalizedSinTheta_finiteInterval :=
  DavisKahan.Experimental.ExactSinTheta.FiniteIntervalGeneralSinThetaProblem.result

/-- Complementary-overlap form of the completed finite interval/exterior theorem. -/
alias generalizedSinTheta_finiteInterval_complementaryBlock :=
  DavisKahan.Experimental.ExactSinTheta.FiniteIntervalGeneralSinThetaProblem.complementaryBlock_result

alias sinTheta :=
  DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem.result

/-- Bounded generalized problem, derived through the full-domain closed-operator
bridge rather than owning the canonical proof. -/
alias BoundedGeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.BoundedGeneralSinThetaProblem

/-- Bounded specialization derived from the canonical generalized theorem. -/
alias generalizedSinTheta_boundedSpecialization :=
  DavisKahan.Experimental.ExactSinTheta.BoundedGeneralSinThetaProblem.result

end DavisKahan1970
end ForMathlib
