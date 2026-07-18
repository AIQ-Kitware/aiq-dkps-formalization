/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral

/-!
# Approximation numbers and strong spectral cutoffs

Davis--Kahan Lemma 5.1 passes from bounded spectral truncations to the original
operator one singular value at a time.  These declarations expose the required
approximation-number and Ky Fan convergence results separately.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Strong operator convergence expressed pointwise. -/
def StronglyTendsto {ι : Type w} (T : ι → E →L[𝕜] E)
    (l : Filter ι) (S : E →L[𝕜] E) : Prop :=
  ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x))

/-- Orthogonal projection predicate for bounded operators. -/
def IsOrthogonalProjectionMap (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ P.IsSymmetric

/-- Zero-based approximation singular value.  The intended definition is the
operator-norm distance to operators of rank at most `n`; in particular index
zero is the operator norm. -/
noncomputable def approximationSingularValue
    (n : ℕ) (K : E →L[𝕜] F) : ℝ := by
  sorry

/-- Approximation singular values are nonnegative. -/
theorem approximationSingularValue_nonneg
    (n : ℕ) (K : E →L[𝕜] F) :
    0 ≤ approximationSingularValue n K := by
  sorry

/-- The zero-based first approximation singular value is the operator norm. -/
theorem approximationSingularValue_zero
    (K : E →L[𝕜] F) :
    approximationSingularValue 0 K = ‖K‖ := by
  sorry

/-- Approximation singular values are absolutely homogeneous. -/
theorem approximationSingularValue_smul
    (n : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    approximationSingularValue n (c • K) =
      ‖c‖ * approximationSingularValue n K := by
  sorry

/-- Approximation singular values decrease with the index. -/
theorem approximationSingularValue_antitone
    (K : E →L[𝕜] F) :
    Antitone (fun n => approximationSingularValue n K) := by
  sorry

/-- The first approximation singular value is controlled by operator norm. -/
theorem approximationSingularValue_le_opNorm
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K ≤ ‖K‖ := by
  sorry

/-- Adjoint invariance of approximation singular values. -/
theorem approximationSingularValue_adjoint
    (n : ℕ) (K : E →L[𝕜] F) :
    approximationSingularValue n K.adjoint =
      approximationSingularValue n K := by
  sorry

/-- Ideal inequality for approximation singular values. -/
theorem approximationSingularValue_comp_le
    {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (n : ℕ) (L : F →L[𝕜] G) (K : E →L[𝕜] F)
    (R : H →L[𝕜] E) :
    approximationSingularValue n (L ∘L K ∘L R)
      ≤ ‖L‖ * approximationSingularValue n K * ‖R‖ := by
  sorry

/-- Continuity of each singular value under strong orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  sorry

/-- Finite Ky Fan gauge built from approximation singular values. -/
noncomputable def kyFanApproximationGauge
    (k : ℕ) (K : E →L[𝕜] F) : ℝ :=
  ∑ n ∈ Finset.range k, approximationSingularValue n K

/-- Ky Fan approximation gauges are absolutely homogeneous. -/
theorem kyFanApproximationGauge_smul
    (k : ℕ) (c : 𝕜) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k (c • K) =
      ‖c‖ * kyFanApproximationGauge k K := by
  sorry

/-- Ky Fan approximation gauges are nonnegative. -/
theorem kyFanApproximationGauge_nonneg
    (k : ℕ) (K : E →L[𝕜] F) :
    0 ≤ kyFanApproximationGauge k K := by
  sorry

/-- Ky Fan approximation gauges are invariant under adjoint. -/
theorem kyFanApproximationGauge_adjoint
    (k : ℕ) (K : E →L[𝕜] F) :
    kyFanApproximationGauge k K.adjoint =
      kyFanApproximationGauge k K := by
  sorry

/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  sorry

/-- A rectangular ideal family whose gauge is fully symmetric with respect
    to all finite Ky Fan approximation gauges.

This is intentionally stronger than `RectangularSymmetricIdealFamily`.  The
ordinary two-sided ideal and completeness laws do not imply Fan dominance on
nonseparable Hilbert spaces. -/
structure KyFanDominantIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  toRectangularSymmetricIdealFamily :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜)
  majorization_mem_and_gauge_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F},
      toRectangularSymmetricIdealFamily.Mem B →
      (∀ k, kyFanApproximationGauge k A ≤
        kyFanApproximationGauge k B) →
      toRectangularSymmetricIdealFamily.Mem A ∧
        toRectangularSymmetricIdealFamily.gauge A ≤
          toRectangularSymmetricIdealFamily.gauge B

/-- Source-facing name for the infinite-dimensional unitarily invariant norm
families supported by the Davis--Kahan cutoff proof.  The finite-Ky-Fan
majorization law is part of the abstraction, not an extra theorem inferred from
ordinary Banach ideal laws. -/
abbrev UnitaryInvariantIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] :=
  KyFanDominantIdealFamily (𝕜 := 𝕜)

namespace KyFanDominantIdealFamily

/-- The ordinary operator norm with its finite-Ky-Fan dominance property. -/
noncomputable def operatorNorm :
    KyFanDominantIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Compact operators with the operator norm and the induced
finite-Ky-Fan dominance property. -/
noncomputable def compactOperatorNorm :
    KyFanDominantIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Existence of the fixed positive Ky Fan family with the intended concrete
membership and gauge.  This is the single foundational Ky Fan package needed
by the ordered unbounded cutoff proof. -/
theorem exists_kyFan_family (k : ℕ) (hk : 0 < k) :
    ∃ N : KyFanDominantIdealFamily (𝕜 := 𝕜),
      ∀ {E F : Type v}
        [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
        [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
        (A : E →L[𝕜] F),
        N.toRectangularSymmetricIdealFamily.Mem A ∧
          N.toRectangularSymmetricIdealFamily.gauge A =
            kyFanApproximationGauge k A := by
  sorry

/-- A fixed positive Ky Fan gauge with its own dominance property. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    KyFanDominantIdealFamily (𝕜 := 𝕜) :=
  Classical.choose (exists_kyFan_family (𝕜 := 𝕜) k hk)

/-- Every bounded operator belongs to the fixed finite Ky Fan family. -/
theorem kyFan_mem (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.Mem A :=
  (Classical.choose_spec (exists_kyFan_family (𝕜 := 𝕜) k hk) A).1

/-- The abstract fixed-family gauge is the concrete finite Ky Fan sum. -/
theorem kyFan_gauge (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.gauge A =
      kyFanApproximationGauge k A :=
  (Classical.choose_spec (exists_kyFan_family (𝕜 := 𝕜) k hk) A).2

/-- Hilbert--Schmidt norm with its finite-Ky-Fan dominance property. -/
noncomputable def hilbertSchmidt :
    KyFanDominantIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Trace norm with its finite-Ky-Fan dominance property. -/
noncomputable def traceClass :
    KyFanDominantIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Schatten `p` norm with its finite-Ky-Fan dominance property. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    KyFanDominantIdealFamily (𝕜 := 𝕜) := by
  sorry

end KyFanDominantIdealFamily

/-- Infinite-dimensional Fan dominance, now made an explicit field of the
stronger family rather than incorrectly derived from ordinary ideal laws. -/
theorem mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ k, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B :=
  N.majorization_mem_and_gauge_le hB h


/-- Scaled Fan dominance in the exact form consumed by the Sylvester theorem. -/
theorem mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F} {δ : ℝ}
    (hδ : 0 < δ)
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ k, δ * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B := by
  sorry

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
