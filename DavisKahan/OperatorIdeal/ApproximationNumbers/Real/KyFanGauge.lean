/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking, Claude Opus 5
-/

module

public import DavisKahan.OperatorIdeal.ApproximationNumbers.Core
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Strong cutoffs and finite Ky Fan gauges over real Hilbert spaces

The retained real cutoff-convergence theorems instantiate the field-generic
proofs at the accepted `TauCeti.HasMinMaxLowerBound.of_completeSpace`:

* `approximationSingularValue_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_comp_strongProjection_tendsto_real`.

The former real threshold proof and field-specific Ky Fan triangle wrapper are
retired. The accepted converse localization supplies the input uniformly over
`RCLike`, without requiring target completeness.
-/

public section

open scoped InnerProductSpace Topology

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace ApproximationNumbersReal

open Filter

noncomputable section

universe v vF w

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Real-Hilbert-space cutoff convergence for approximation singular values. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (n : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace hPproj hP n K

omit [CompleteSpace F] in
/-- Real-Hilbert-space cutoff convergence for finite Ky Fan gauges. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (k : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) :=
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace hPproj hP k K


end

end ApproximationNumbersReal
end ExactSinTheta
end DavisKahan
end TauCeti
