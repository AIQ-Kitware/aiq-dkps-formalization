/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral

/-!
# Coherent cutoff interface for the genuine unbounded Sylvester proof

The ordered two-unbounded argument needs a small, stable interface rather than
an undifferentiated dependency on the legacy spectral facade.  This leaf names
that interface explicitly.  Direct vendored-Spectra implementations are
provided by `GenuineSpectralCutoff` and `GenuineBoundedTruncation`, while the
legacy constructors at the end remain available as compatibility witnesses.
-/

open scoped InnerProductSpace Topology
open Filter

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The exact projection, domain, commutation, and strong-convergence laws
needed from a spectral cutoff family. -/
structure GenuineSpectralCutoffInterface
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) where
  cutoff : ℝ → E →L[𝕜] E
  isOrthogonalProjection : ∀ τ,
    cutoff τ ∘L cutoff τ = cutoff τ ∧ (cutoff τ).IsSymmetric
  range_le_domain : ∀ τ, LinearMap.range (cutoff τ).toLinearMap ≤ A.domain
  commutes_on_domain : ∀ τ (x : A.domain),
    ∃ hx : cutoff τ (x : E) ∈ A.domain,
      A.toLinearMap ⟨cutoff τ (x : E), hx⟩ = cutoff τ (A.toLinearMap x)
  tendsto_identity : ∀ x,
    Tendsto (fun τ : ℝ => cutoff τ x) atTop (𝓝 x)

/-- The bounded truncation laws needed after a cutoff family has been chosen. -/
structure GenuineBoundedTruncationInterface
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint)
    (P : GenuineSpectralCutoffInterface A hA) where
  truncation : ℝ → E →L[𝕜] E
  isSymmetric : ∀ τ, (truncation τ).IsSymmetric
  eq_on_cutoff : ∀ τ x,
    ∃ hx : P.cutoff τ x ∈ A.domain,
      truncation τ x = A.toLinearMap ⟨P.cutoff τ x, hx⟩
  tendsto_on_domain : ∀ x : A.domain,
    Tendsto (fun τ : ℝ => truncation τ (x : E)) atTop
      (𝓝 (A.toLinearMap x))
  lowerBound : ∀ {c : ℝ}, SemiboundedBelow A c →
    ∀ {τ : ℝ}, 0 ≤ τ → ∀ x,
      c * ‖P.cutoff τ x‖ ^ 2 ≤
        RCLike.re ⟪truncation τ x, P.cutoff τ x⟫_𝕜
  upperBound : ∀ {c : ℝ}, SemiboundedAbove A c →
    ∀ {τ : ℝ}, 0 ≤ τ → ∀ x,
      RCLike.re ⟪truncation τ x, P.cutoff τ x⟫_𝕜 ≤
        c * ‖P.cutoff τ x‖ ^ 2
  commutes_cutoff : ∀ τ,
    truncation τ ∘L P.cutoff τ = truncation τ ∧
      P.cutoff τ ∘L truncation τ = truncation τ

/-- Package the current cutoff declarations behind the coherent interface. -/
noncomputable def legacySpectralCutoffInterface
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    GenuineSpectralCutoffInterface A hA where
  cutoff := spectralCutoff A hA
  isOrthogonalProjection := spectralCutoff_isOrthogonalProjection A hA
  range_le_domain := spectralCutoff_range_le_domain A hA
  commutes_on_domain := spectralCutoff_commutes_on_domain A hA
  tendsto_identity := spectralCutoff_tendsto_identity A hA

/-- Package the current bounded truncation declarations behind the coherent
interface. -/
noncomputable def legacyBoundedTruncationInterface
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    GenuineBoundedTruncationInterface A hA
      (legacySpectralCutoffInterface A hA) where
  truncation := boundedSpectralTruncation A hA
  isSymmetric := boundedSpectralTruncation_isSymmetric A hA
  eq_on_cutoff := boundedSpectralTruncation_eq_on_cutoff A hA
  tendsto_on_domain := boundedSpectralTruncation_tendsto_on_domain A hA
  lowerBound := by
    intro c hLower τ hτ x
    exact boundedSpectralTruncation_lowerBound A hA hLower hτ x
  upperBound := by
    intro c hUpper τ hτ x
    exact boundedSpectralTruncation_upperBound A hA hUpper hτ x
  commutes_cutoff := boundedSpectralTruncation_commutes_cutoff A hA

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
