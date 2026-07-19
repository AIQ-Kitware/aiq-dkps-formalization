/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbersReal

/-!
# Real-Hilbert-space approximation-number compatibility layer

The real localization, strong-cutoff, and infinite-dimensional Ky Fan triangle
arguments are proved in `ApproximationNumbersReal`. This module exposes the
three scalar-specific endpoints in the parent `ExactSinTheta` namespace used by
the aggregate ideal infrastructure and earlier roadmap clients.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe v w

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Real-Hilbert-space continuity of approximation numbers under strongly
convergent orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (n : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  exact
    ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
      hPproj hP n K

/-- Real-Hilbert-space finite Ky Fan convergence under strongly convergent
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (k : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  exact
    ApproximationNumbersReal.kyFanApproximationGauge_comp_strongProjection_tendsto_real
      hPproj hP k K

/-- Real-Hilbert-space infinite-dimensional Ky Fan triangle inequality. -/
theorem kyFanApproximationGauge_add_le_real
    (k : ℕ) (K L : E →L[ℝ] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L := by
  exact ApproximationNumbersReal.kyFanApproximationGauge_add_le_real k K L

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
