/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakage

/-!
# Mathematics-ahead proof of Davis--Kahan Lemma 6.3 — promoted

The corrected, source-faithful proof of Lemma 6.3 (block hypothesis
`K * P = Q * K * P`, not the overstrong `K * P = Q * K`) has been promoted to
the production module `DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakage`
(graduated out of the experimental frontier), where it now closes the
source-facing statements directly.

This module retains the former ahead-of-frontier names as thin re-exports so
existing references continue to resolve.  The mathematics lives at the
frontier; see `dev/overlays/lemma63-promotion-scratch-7f9f562-gpt56.md` for the
promotion record.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace Section6Appendix

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Former name for the promoted prefix square energy
`Frontier.Section6Appendix.approximationEnergy`. -/
noncomputable abbrev approximationSquareEnergy (T : E →L[ℂ] F) (n : ℕ) : ℝ :=
  Frontier.Section6Appendix.approximationEnergy T n

/-- Former name for the promoted approximation-number form of Lemma 6.3. -/
theorem lemma6_3_approximationNumber_leakage_completed
    (K : E →L[ℂ] F)
    (P : Submodule ℂ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      approximationSquareEnergy (K ∘L P.starProjection) n >
        approximationSquareEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η :=
  Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage
    K P Q n hn η hη hKP hrankP hrankQ hnear

end Section6Appendix
end MathAhead
end Experimental
end DavisKahan
end TauCeti