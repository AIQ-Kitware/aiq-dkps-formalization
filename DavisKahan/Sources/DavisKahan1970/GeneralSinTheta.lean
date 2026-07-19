/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.LegacyGapCompletion
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.RealSpecializations

/-!
# Davis--Kahan 1970 general sine-theta manuscript surface

The unqualified manuscript names use the complex scalar convention and cover
the complete 1970 gap disjunction: finite interval/exterior separation and both
ordered half-line orientations.  Parallel real problem records and result
aliases are exposed explicitly.  The complex and real routes share the same
legacy statement surface but use the direct genuine engine and exact finite
Ky Fan transport underneath.
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

/-- Real lower-frame version of the complete source-shaped problem. -/
alias RealGeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.RealGeneralSinThetaProblem

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
  DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem.result_complex

/-- Explicit complex name for the manuscript's default scalar convention. -/
alias sinTheta_complex :=
  DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem.result_complex

/-- Real source-facing isometric theorem. -/
alias sinTheta_real :=
  DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem.result_real

/-- Real source-facing generalized theorem. -/
alias generalizedSinTheta_real :=
  DavisKahan.Experimental.ExactSinTheta.RealGeneralSinThetaProblem.result

/-- Real complementary-overlap form of the generalized theorem. -/
alias generalizedSinTheta_real_complementaryBlock :=
  DavisKahan.Experimental.ExactSinTheta.RealGeneralSinThetaProblem.complementaryBlock_result

/-- Bounded generalized problem, derived through the full-domain closed-operator
bridge rather than owning the canonical proof. -/
alias BoundedGeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.BoundedGeneralSinThetaProblem

/-- Bounded specialization derived from the canonical generalized theorem. -/
alias generalizedSinTheta_boundedSpecialization :=
  DavisKahan.Experimental.ExactSinTheta.BoundedGeneralSinThetaProblem.result

/-- Bounded real lower-frame problem. -/
alias RealBoundedGeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.RealBoundedGeneralSinThetaProblem

/-- Bounded real generalized specialization. -/
alias generalizedSinTheta_boundedSpecialization_real :=
  DavisKahan.Experimental.ExactSinTheta.RealBoundedGeneralSinThetaProblem.result

end DavisKahan1970
end ForMathlib
