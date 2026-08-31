/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial
import DavisKahan.Sources.DavisKahan1970.DirectedUnboundedReal
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-!
# Davis--Kahan 1970, the Section 2 `tan Θ` DIRECTED clause, at the source norm

The Section 2 tangent theorem has two printed conclusions:

```text
directed:  δ ‖tan Θ₀‖ ≤ ‖R‖
ambient:   δ ‖tan Θ‖  ≤ ‖H‖
```

The ambient clause is `tanTheta_ambient_unboundedRitz_paperUINorm_complex` and its
real sibling.  This module supplies the **directed** clause at the same scope: an
unbounded self-adjoint ambient operator, an arbitrary complete trial subspace,
the source residual on the right-hand side, and an arbitrary
`PaperUnitaryInvariantNorm`.

## Why this was missing

The mathematics was already here.  `theorem6_3_unbounded_infiniteTrial_ideal` and
its real sibling prove exactly this estimate for every Ky-Fan-dominant ideal
family, with an unbounded `A : H →ₗ.[𝕜] H` and the residual `D.residual` on the
right.  What did not exist was the promotion to the paper's universal norm
quantifier, and the result inventory had registered in its place two declarations
that do not carry the scope they were credited with:

* `Section2.theorem6_3_perturbation_infiniteTrial` -- a **bounded** ambient
  operator (`T E : H →L[ℂ] H`) at a Ky Fan family;
* `partIII_tanTheta_ritzResidual_uiNorm` -- **finite-dimensional**
  (`[FiniteDimensional 𝕜 E]`, `[FiniteDimensional 𝕜 F]`) at a rectangular
  seminorm.

Both remain useful and remain registered as supporting evidence; neither
establishes the directed clause at the printed scope.

## The one structural point

The Ky-Fan-level theorem also has an existential form producing a tangent
representative.  That form cannot be promoted: the promotion evaluates the
estimate at every Ky Fan index, and an existential would return a possibly
different witness each time.  The representative is therefore a **parameter**
here, characterized by the paper's own instruction that its approximation numbers
be `tan θ_j` -- `HasTheorem63DirectedTangentApproximationNumbersInfinite`.  That
is the source's own way of saying what `tan Θ₀` is, and it makes the statement
independent of which representative a caller holds.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the Section 2 `tan Θ` theorem and
  Theorem 6.3.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactTanTheta

noncomputable section

universe v

/-! ## Over a complex Hilbert space -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the Section 2 `tan Θ` directed clause, over `ℂ`, at every
source unitarily invariant norm.**

`δ N(tan Θ₀) ≤ N(R)`, with `R` the trial residual, for an unbounded self-adjoint
ambient operator, an arbitrary complete trial subspace, arbitrary Hilbert
dimension, and an arbitrary `PaperUnitaryInvariantNorm`.

The gap is the source's ordered configuration: the trial compression is bounded
above by `α` in form and `A` has no spectrum in `(α, α + δ)`, so the exact space
is the spectral subspace for `(-∞, α]`.  Both separating intervals are
half-infinite, which is the scope the source states for this theorem. -/
theorem tanTheta_directed_unboundedTrial_paperUINorm_complex
    (N : PaperUnitaryInvariantNorm)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : TanTheta.UnboundedTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z
      (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := theorem6_3_unbounded_infiniteTrial_ideal
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos) A hA D hdelta hgap
      hCompression tanTheta0 htan
      (KyFanDominantIdealFamily.kyFan_mem k hkpos D.residual)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

end Complex

/-! ## Over a real Hilbert space -/

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open TauCeti.DavisKahan.RealSpectralRestriction

/-- **Davis--Kahan 1970, the Section 2 `tan Θ` directed clause, over `ℝ`, at every
source unitarily invariant norm.**  The real sibling of
`tanTheta_directed_unboundedTrial_paperUINorm_complex`. -/
theorem tanTheta_directed_unboundedTrial_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    {Z : Submodule ℝ E} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : TanTheta.UnboundedTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSelfAdjointSpectralProjection A hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z
      (realSelfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := theorem6_3_unbounded_infiniteTrial_ideal_real A hA
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hkpos) D hdelta hgap
      hCompression tanTheta0 htan
      (KyFanDominantIdealFamily.kyFan_mem k hkpos D.residual)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

end Real

end

end DavisKahan1970
end TauCeti
