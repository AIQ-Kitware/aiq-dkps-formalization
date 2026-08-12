/-
# Headline Davis--Kahan sin-Theta comparators

This challenge pins both the source residual theorem and the familiar
perturbation-form endpoint.  The residual statement is the finite source form
for every rectangular unitarily invariant norm; the perturbation statement is
the square full-space companion.
-/

import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
import ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import DavisKahan.BoundedOperator.Compat
import DavisKahan.Geometry.Angle.PaperOperatorAngle
import DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras
import DavisKahan.Sylvester.Unbounded.LegacyGap
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-!
## Comparator maintenance rule

The open proofs below are deliberate challenge placeholders. The implementation
lives in the ordinary library modules imported by the paired leaderboard.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

section Residual

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Davis--Kahan Part III directed sin-Theta residual theorem in every
rectangular unitarily invariant norm, with the source interval/exterior gap. -/
theorem partIII_sinTheta_residual_uiNorm
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hMspec : SpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : SpectrumIn A Uᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  sorry

end Residual

section Perturbation

variable [CompleteSpace E] {T S : E →ₗ[𝕜] E}

/-- Davis--Kahan Part III perturbation sin-Theta theorem in every square
unitarily invariant norm. -/
theorem partIII_sinTheta_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    N ((V.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  sorry

end Perturbation

end DavisKahanTheory
end TauCeti

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Arbitrary-Hilbert-space/source-UI ambient sin-Theta theorem, with the two
source gap applications of Proposition 6.1 spelled out rather than hidden
inside `PaperSymmetricSinThetaProblem`. -/
theorem sinTheta_wholeSpace_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {gap : ℝ} (hgap : 0 < gap)
    (hgapUV : FormBoundedSylvesterGap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) U
        (ClosedOperator.ofBounded_reducesSubspace A U hU))
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) Vᗮ
        (ClosedOperator.ofBounded_reducesSubspace B V hV).orthogonal)
      gap)
    (hgapVU : FormBoundedSylvesterGap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) V
        (ClosedOperator.ofBounded_reducesSubspace B V hV))
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) Uᗮ
        (ClosedOperator.ofBounded_reducesSubspace A U hU).orthogonal)
      gap)
    (hMem : N.Mem (B - A)) :
    N.Mem (paperSinAngleOperatorC U V) ∧
      gap * N.gauge (paperSinAngleOperatorC U V) ≤ N.gauge (B - A) := by
  sorry

end
end DavisKahan1970
end TauCeti
