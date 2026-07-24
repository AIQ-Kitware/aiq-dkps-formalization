/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
import DavisKahan.SinTheta.Natural.Reducing
import DavisKahan.SinTheta.Natural.GenuineGeneralized
import DavisKahan.SinTheta.Natural.Bounded
import DavisKahan.SinTheta.Natural.GapConvenience
import DavisKahan.SinTheta.NaturalTwoSubspace

/-!
# Optional natural-input extensions to the general sine-theta surface

The compiler-accepted `GeneralSinTheta` facade remains unchanged.  This separate
module exposes reducing-subspace, bounded natural-input, generalized complex
spectral-subspace, gap-constructor, and symmetric two-direction conveniences.
After this leaf is compiler-accepted, its aliases can be folded into the main
source facade without changing the verified theorem chain.
-/

namespace TauCeti
namespace DavisKahan1970

/-- Complex isometric unbounded theorem from a measurable exact spectral set. -/
alias sinTheta_spectralSubspace :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap

/-- Complex generalized unbounded theorem from a measurable exact spectral set. -/
alias generalizedSinTheta_spectralSubspace :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded_spectralSubspace_of_genuineSpectrumGap

/-- Scalar-generic natural isometric problem over a reducing exact subspace. -/
alias NaturalReducingIsometricSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.NaturalReducingIsometricSinThetaProblem

/-- Scalar-generic natural lower-frame problem over a reducing exact subspace. -/
alias NaturalReducingGeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.NaturalReducingGeneralSinThetaProblem

/-- Complex natural theorem when the exact subspace is supplied as reducing. -/
alias sinTheta_reducingSubspace_complex :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_complex_reducingSubspace

/-- Real natural theorem when the exact subspace is supplied as reducing. -/
alias sinTheta_reducingSubspace_real :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_real_reducingSubspace

/-- Complex lower-frame theorem when the exact subspace is supplied as reducing. -/
alias generalizedSinTheta_reducingSubspace_complex :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded_complex_reducingSubspace

/-- Real lower-frame theorem when the exact subspace is supplied as reducing. -/
alias generalizedSinTheta_reducingSubspace_real :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace

/-- Bounded complex isometric theorem from a measurable exact spectral set. -/
alias sinTheta_bounded_spectralSubspace :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_bounded_spectralSubspace_of_genuineSpectrumGap

/-- Bounded complex generalized theorem from a measurable exact spectral set. -/
alias generalizedSinTheta_bounded_spectralSubspace :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_bounded_spectralSubspace_of_genuineSpectrumGap

/-- Bounded real isometric theorem from a measurable exact spectral set. -/
alias sinTheta_bounded_real_spectralSubspace :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_bounded_real_spectralSubspace

/-- Bounded real generalized theorem from a measurable exact spectral set. -/
alias generalizedSinTheta_bounded_real_spectralSubspace :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_bounded_real_spectralSubspace

end DavisKahan1970
end TauCeti