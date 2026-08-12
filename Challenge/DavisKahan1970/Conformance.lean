/-
# Davis--Kahan 1970 exhibition challenge

A source-oriented comparator surface for the 1970 Davis--Kahan paper.

This is deliberately not organized as a Mathlib promotion queue.  The targets
are selected because they are recognizable mathematical endpoints of the paper
or because they exhibit an important formalization fact.  They need not be leaf
nodes in the repository proof graph: headline theorems are useful precisely
because later source results reuse them.

The final `tan 2Theta` target is intentionally stronger than the currently
available production wrappers: it states the ambient Section 2 theorem without
an added pole-exclusion or selected-block spectral-placement premise.  Its
presence in the comparator is an executable record of that remaining
paper-faithfulness obligation.
-/

import DavisKahan.FiniteDimensional.Core.All
import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
import ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import DavisKahan.BoundedOperator.Compat
import DavisKahan.Geometry.Angle.PaperOperatorAngle
import DavisKahan.Geometry.Angle.PaperDoubleAngle
import DavisKahan.Geometry.Angle.PaperTanAngle
import DavisKahan.Geometry.Halmos.CrossedDefectGap
import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.DoubleAngle.TanTwoThetaBranchFree
import DavisKahan.BoundedOperator.TrialResidual
import DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras
import DavisKahan.Sylvester.Unbounded.LegacyGap
import DavisKahan.Sylvester.Spectrum
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import DavisKahan.TanTheta.Theorem63FiniteSource
import DavisKahan.TanTheta.Theorem63InfiniteTrial

/-!
## Comparator maintenance rule

Every proof hole below is intentional.  `Conformance.lean` states the challenge;
`Leaderboard.lean` exposes the production proofs that currently discharge it.
A statement may remain here even when no matching leaderboard declaration
exists yet.  In that case `lake build Challenge` stays useful, while the
comparator/signature gate remains red until the paper-faithful production
endpoint exists.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace
open Module (finrank)

universe u

/-! ### Finite source-facing compatibility endpoints -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

section SinThetaFinite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Finite Part III directed `sin Theta` residual theorem in every rectangular
unitarily invariant norm.  This remains in the exhibition because it is the
low-dependency specialization from which many computational applications start. -/
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

end SinThetaFinite

section SinThetaPerturbationFinite

variable [CompleteSpace E] {T S : E →ₗ[𝕜] E}

/-- Finite Part III perturbation `sin Theta` theorem in every square UI norm. -/
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

end SinThetaPerturbationFinite

section TanThetaFinite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Finite source-shaped directed `tan Theta` Ritz-residual theorem. -/
theorem partIII_tanTheta_source_uiNorm
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) (hrank : finrank 𝕜 F = finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hMspec : SpectrumIn (compression A X) ⊤ (Set.Icc β α))
    (hAspec : SpectrumIn A Uᗮ (Set.Ici (α + δ)))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  sorry

end TanThetaFinite

section SinTwoThetaFinite

variable [CompleteSpace E] {T S : E →ₗ[𝕜] E}

/-- Finite Part III `sin 2Theta` theorem in every unitarily invariant seminorm. -/
theorem partIII_sinTwoTheta_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    N ((Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) := by
  sorry

end SinTwoThetaFinite

section TanTwoThetaFinite

/-- Sharp finite operator-norm Part III `tan 2Theta` theorem. -/
theorem partIII_tanTwoTheta_opNorm {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b ε : ℝ} (hab : a < b) (hε0 : 0 ≤ ε)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hVb : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜)
    (hVa : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2 < 1 / 2 ∧
      (b - a) * (2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖
          * Real.sqrt
            (1 - ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2))
        ≤ 2 * ε *
          (1 - 2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2) := by
  sorry

end TanTwoThetaFinite

/-! ### Modern infinite-dimensional projector form -/

section ProjectorDifference

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Canonical modern projector-distance formulation on an arbitrary complex
Hilbert space, at genuine restriction spectra. -/
theorem projectorDifference_restrictionSpectra_opNorm
    {A B : H →L[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule ℂ H} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : Reduces A U) (hW : Reduces B W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : H →L[ℂ] H)‖ ≤ ‖B - A‖ / g := by
  sorry

end ProjectorDifference

/-! ### Faithful treatment of the false printed Proposition 4.4 -/

/-- A concrete `R^4` counterexample to the printed Proposition 4.4: an acute
pair with all principal angles at most `pi/3` admits an intertwining unitary
whose trace-norm displacement is strictly smaller than that of the direct
rotation. -/
theorem proposition4_4_counterexample :
    ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
      (hacute : IsAcute U V)
      (W : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      U.map W.toLinearMap = V ∧
      principalAngles U V 0 ≤ Real.pi / 3 ∧
      kyFanSum 4 (LinearMap.id - W.toLinearMap) <
        kyFanSum 4 (LinearMap.id - (directRotation U V hacute).toLinearMap) := by
  sorry

end DavisKahanTheory
end TauCeti

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactTanTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Orthogonally complemented subspaces of a complete Hilbert space are
complete.  The source theorem signatures use compressions to such subspaces,
so the challenge installs the same local instance as the production modules. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionChallenge
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (W : Submodule ℂ G) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-! ### Full Hilbert-space headline surfaces -/

/-- Arbitrary-Hilbert-space/source-UI ambient `sin Theta` theorem, with the two
source gap applications written explicitly. -/
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

/-- Theorem 6.3 directed `tan Theta` theorem on arbitrary complete complex
Hilbert spaces and arbitrary complete trial subspaces, for every source UI norm. -/
theorem tanTheta_directed_paperUINorm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (N : PaperUnitaryInvariantNorm)
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  sorry

/-- Ambient `tan Theta` theorem under the paper's standing crossed-defect
condition (3.5), which supplies transversality rather than assuming it separately. -/
theorem tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent
    (N : PaperUnitaryInvariantNorm)
    {T A : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hT : T.IsSymmetric) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (h35 : DavisKahan.Frontier.CrossedDefectsEquivalent U V)
    (hMem : N.Mem (T - A)) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge (T - A) := by
  sorry

/-- Full-Hilbert directed residual `sin 2Theta` theorem for every source UI norm. -/
theorem sinTwoTheta_directedResidual_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (M : V →L[ℂ] V)
    (hMem : N.Mem (residual A V.subtypeL M)) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      d * N.gauge (sinTwoThetaIdealBlock U V) ≤
        2 * N.gauge (residual A V.subtypeL M) := by
  sorry

/-- Full-Hilbert ambient `sin 2Theta` theorem for every source UI norm. -/
theorem sinTwoTheta_wholeSpace_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (paperSinTwoAngleOperatorC U V) ∧
      d * N.gauge (paperSinTwoAngleOperatorC U V) ≤
        2 * N.gauge (B - A) := by
  sorry

/-- Current branch-free graph-coordinate `tan 2Theta` endpoint.

This is valuable infrastructure at arbitrary Hilbert/source-UI scope, but its
right-hand side is the whole off-diagonal perturbation `H`; it is not used as a
substitute for the paper's separate directed residual conclusion below. -/
theorem tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace
    (N : PaperUnitaryInvariantNorm)
    {A H T : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[ℂ] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      DavisKahanTheory.absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H := by
  sorry


/-- **Intentional red comparator target:** literal directed Section 2
`tan 2Theta` residual theorem at arbitrary Hilbert/source-UI scope.

The directed angle is encoded independently of the source proof modules.  The
operator `sinAngleOperatorDirectedC U V` has the directed principal sines on
`U` and zero on `U perp`; applying `s ↦ |tan (2 * arcsin s)|` by continuous
functional calculus therefore gives the source `|tan 2Theta_0|` singular-value
sequence without choosing a graph chart or assuming the quarter-acute branch.
The conclusion also returns pole exclusion explicitly, because Lean's
`Real.tan` is totalized at the poles whereas the printed theorem asserts a
finite tangent.  Under the printed off-diagonal hypothesis,
`P_{U perp} H P_U` is the ambient extension of the source residual `R`.
No independent pole-exclusion or selected-block placement premise is included. -/
theorem tanTwoTheta_directedResidual_paperUINorm_exactPaper
    (N : PaperUnitaryInvariantNorm)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hRmem : N.Mem (Uᗮ.starProjection ∘L H ∘L U.starProjection)) :
    let tanTwoTheta0 : E →L[ℂ] E :=
      cfc (fun s : ℝ => |Real.tan (2 * Real.arcsin s)|)
        (sinAngleOperatorDirectedC U V)
    (∀ s ∈ spectrum ℝ (sinAngleOperatorDirectedC U V),
        Real.cos (2 * Real.arcsin s) ≠ 0) ∧
      N.Mem tanTwoTheta0 ∧
      (b - a) * N.gauge tanTwoTheta0 ≤
        2 * N.gauge (Uᗮ.starProjection ∘L H ∘L U.starProjection) := by
  sorry

/-- Best currently proved ambient branch-free `tan 2Theta` endpoint.  The
explicit `hcos` premise records the remaining gap to the literal Section 2
hypothesis surface. -/
theorem tanTwoTheta_wholeSpace_paperUINorm_branchFree
    (N : PaperUnitaryInvariantNorm)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (paperAngleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (hHmem : N.Mem H) :
    N.Mem (paperAbsTanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (paperAbsTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  sorry

/-- **Intentional red comparator target:** literal ambient Section 2
`tan 2Theta` theorem at arbitrary Hilbert/source-UI scope.

Unlike the currently proved wrappers, this statement assumes neither explicit
pole exclusion nor spectral placement of the selected `V` blocks.  The paper's
proof is supposed to derive pole exclusion from the one-sided gap and the
fully off-diagonal perturbation.  The pole-exclusion predicate is returned
explicitly because Lean's `Real.tan` is totalized at poles; this prevents the
formal statement from becoming accidentally weaker than the paper. -/
theorem tanTwoTheta_wholeSpace_paperUINorm_exactPaper
    (N : PaperUnitaryInvariantNorm)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    (∀ t ∈ spectrum ℝ (paperAngleOperatorC U V), Real.cos (2 * t) ≠ 0) ∧
      N.Mem (paperAbsTanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (paperAbsTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  sorry

end
end DavisKahan1970
end TauCeti
