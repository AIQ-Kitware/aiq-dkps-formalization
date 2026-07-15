/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Specializations

/-!
# Davis--Kahan 1970 general sine-theta manuscript surface

This module exposes the intended source theorem order.  It is an experimental
manuscript facade, not a proof-completion claim.  The generalized unbounded
result owns the unqualified source role; the isometric, bounded, and finite
forms are specializations or alternative proofs.
-/

namespace ForMathlib
namespace DavisKahan1970

alias GeneralSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.GeneralSinThetaProblem
alias IsometricSinThetaProblem :=
  DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem

alias generalizedSinTheta :=
  DavisKahan.Experimental.ExactSinTheta.GeneralSinThetaProblem.result
alias generalizedSinTheta_complementaryBlock :=
  DavisKahan.Experimental.ExactSinTheta.GeneralSinThetaProblem.complementaryBlock_result
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
