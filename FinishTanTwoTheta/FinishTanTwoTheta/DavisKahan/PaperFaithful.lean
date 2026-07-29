/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.DavisKahan.SharpIdeal
import DavisKahan.Sources.DavisKahan1970.TanTwoTheta

/-!
# Paper-faithful `tan 2Theta` target

The compiled `FinishTanTwoTheta` core proves the sharp approximation-number and
standard-ideal estimate after passing to a strictly contractive Riccati graph
coordinate.  That is a strong analytic theorem, but it is not by itself the
source-shaped Davis--Kahan statement.

The maintained 1970-paper distillation records the missing endpoint as follows:

* start with two bounded self-adjoint operators `A` and `A + H`;
* `H` is fully off-diagonal for the reference splitting `U + U-perp`;
* `U` reduces `A` and `V` reduces `A + H`;
* the two reducing splittings obey the same ordered form gap `[a,b]`;
* the strict quarter-turn branch is a conclusion, not an input;
* every source unitary-invariant norm satisfies the sharp factor-two bound for
  the canonical double-angle tangent operator and the full perturbation `H`.

The theorem below intentionally records that exact target with `sorry`.  It is
not an alias for the proved Riccati-coordinate theorem, and its presence prevents
a green aggregate build from being mistaken for completion of the paper-facing
statement.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open DavisKahanExt
open Experimental.ExactSinTheta

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- **Paper-faithful Davis--Kahan `tan 2Theta` theorem, admitted target.**

For a fully off-diagonal bounded self-adjoint perturbation across a common
ordered gap, the selected reducing subspaces are strictly quarter-acute.  For
every source unitary-invariant norm, ideal membership of the full perturbation
passes to the canonical double-angle tangent operator, with the sharp estimate

`(b - a) * N(tan 2Theta(U,V)) <= 2 * N(H)`.

This is the source-shaped arbitrary-Hilbert-space endpoint identified by the
maintained Section 2 / Section 7 distillation.  The current proved theorem
`sharp_paperUnitaryInvariantNorm` starts after branch selection in Riccati
coordinates and therefore does not discharge this declaration by itself. -/
theorem paperFaithful_tanTwoTheta_uiNorm
    (N : PaperUnitaryInvariantNorm)
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    ∃ hquarter : IsQuarterAcute U V,
      N.Mem (tanTwoAngleOperatorC U V hquarter) ∧
        (b - a) * N.gauge (tanTwoAngleOperatorC U V hquarter) ≤
          2 * N.gauge H := by
  sorry

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
