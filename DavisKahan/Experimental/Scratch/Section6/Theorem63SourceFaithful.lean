/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.TanTheta.Theorem63FiniteSource

/-!
# Source-faithful Davis--Kahan 1970, Theorem 6.3

This scratch seam originally isolated the directed tangent definition and the
then-open Ky Fan core after the false `hdim → IsAcute` distillation was
removed.  The bounded source theorem is now proved in
`DavisKahan.TanTheta.Theorem63FiniteSource`.

The key source observation is that Davis--Kahan work globally in a separable
Hilbert space and assume a strict Hilbert-dimension inequality in Theorem 6.3.
Consequently the smaller trial-coordinate space is finite-dimensional.  The
proof therefore needs finite singular vectors on the source, but permits an
arbitrary complete ambient Hilbert space.  It does not require symmetric
acuteness and it does not require the Appendix's equal-dimension noncompact
cutoff argument.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace Section6

open ExactTanTheta

/-- Historical scratch name for the directed sine block. -/
abbrev directedSineBlock := theorem63DirectedSineBlock

/-- Historical scratch name for the directed tangent singular-value data. -/
abbrev HasDirectedTangentApproximationNumbers :=
  HasTheorem63DirectedTangentApproximationNumbers

/-- Historical scratch proposition used while the Ky Fan root was open. -/
def Theorem63KyFanCore
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (delta : ℝ) (tanTheta0 residual : E →L[ℂ] F) : Prop :=
  ∀ k, delta * ExactSinTheta.kyFanApproximationGauge k tanTheta0 ≤
    ExactSinTheta.kyFanApproximationGauge k residual

/-- Fan-dominance promotion retained at its historical scratch name. -/
theorem theorem6_3_ideal_of_kyFan_core
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {delta : ℝ} (hdelta : 0 < delta)
    {tanTheta0 residual : E →L[ℂ] F}
    (hResidual : N.toRectangularSymmetricIdealFamily.Mem residual)
    (hcore : Theorem63KyFanCore delta tanTheta0 residual) :
    N.toRectangularSymmetricIdealFamily.Mem tanTheta0 ∧
      delta * N.toRectangularSymmetricIdealFamily.gauge tanTheta0 ≤
        N.toRectangularSymmetricIdealFamily.gauge residual :=
  ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hdelta hResidual hcore

/-- Completed source Ky Fan core, retained under the former scratch-facing
name for downstream compatibility. -/
alias theorem6_3_all_kyFan_core :=
  ExactTanTheta.theorem6_3_all_kyFan_core

/-- Completed bounded source theorem, retained under a scratch-facing alias for
older frontier consumers. -/
alias theorem6_3_generalizedTanTheta_source_ideal :=
  ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal

end Section6
end Scratch
end Experimental
end DavisKahan
end ForMathlib
