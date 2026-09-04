/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidual
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaUnboundedDirectedResidualReal
import DavisKahan.DoubleAngle.DirectedAngleGeneric

open TauCeti.DavisKahan.Sylvester

/-!
# The printed directed `sin 2Θ` conclusion, on the paper's own angle

The estimates in `SinTwoThetaUnboundedDirectedResidual.lean` and its real sibling conclude on
`sinTwoThetaIdealBlock U V`, a one-sided block and not an angle.  This module restates them on
`Angle.directedSinTwoAngleOperator`, the mathematical directed double-angle sine, in the
orientation Davis and Kahan use.

## Which orientation the source uses

Section 1 fixes `P` reducing `A` with isometries `E₀, E₁`, `A₀` the trial (Ritz) operator and
`R = (A + H)E₀ - E₀A₀` the residual, and `Q` reducing `A + H` with blocks `Λ₀, Λ₁`.  The `sin 2θ`
theorem separates `spec Λ₀` from `spec Λ₁`, so the *gap-carrying* subspace is `Q`.  The paper's
directed angle is read off in (1.16)--(1.17) as

`‖Q^⊥ P‖ = ‖Q^⊥ E₀‖ = ‖sin Θ₀‖`,

so `sin Θ₀` is the cross-projection with the **trial** subspace on the right and the complement
of the gap-carrying subspace on the left.  In this development that operator is
`Angle.directedSinAngleOperator V U` -- trial first, gap-carrying subspace second -- because
`directedSinAngleOperator X Y = |P_{Yᗮ} P_X|`.

The block estimate is naturally parameterized the other way round, and
`Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_rclike` lands on
`directedSinTwoAngleOperator U V`.  The two orderings are *not* interchangeable by renaming
arguments: `sin Θ₀(U, V)` and `sin Θ₀(V, U)` genuinely differ, and a line inside a plane makes
one zero and the other not.  What is true, and what
`Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap` proves, is that the
*doubled* sines have the same complete approximation-number sequence.  The statements below
consume that theorem through
`Angle.mem_directedSinTwoAngleOperator_trialSide_iff` and
`Angle.gauge_directedSinTwoAngleOperator_trialSide`.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.RealSpectralRestriction

open scoped InnerProductSpace

noncomputable section

universe v

/-- A subspace admitting an orthogonal projection inside a complete ambient space is itself
complete.  `local instance` does not propagate through imports, so it is reinstalled here. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedAngle
    {𝕜 : Type*} [RCLike 𝕜] {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Submodule ℂ H} [V.HasOrthogonalProjection]
  {M : V →L[ℂ] V} {R : V →L[ℂ] H}
  {A : H →ₗ.[ℂ] H}

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem, over `ℂ`, on the paper's own
angle.**

`δ N(sin 2Θ₀) ≤ 2 N(R)`, `R = A E₀ - E₀ A₀`, for every `SymmetricNormingFunction`, with the
printed residual, the printed factor two, and the separating interval allowed to be
half-infinite.

`A` is the possibly unbounded self-adjoint operator whose blocks are separated, `B` selects its
spectral subspace, `V` is the trial subspace inside `dom A`, `M` is the trial operator `A₀`, and
`R` is the printed residual.  The conclusion is on
`Angle.directedSinTwoAngleOperator V (selfAdjointSpectralSubspace A hA B hB)` -- **trial first**,
matching the source's `‖sin Θ₀‖ = ‖Q^⊥ E₀‖`. -/
theorem sinTwoTheta_directed_unboundedResidual_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hRmem : N.Mem R) :
    N.Mem (Angle.directedSinTwoAngleOperator V
        (selfAdjointSpectralSubspace A hA B hB)) ∧
      δ * N.gauge (Angle.directedSinTwoAngleOperator V
        (selfAdjointSpectralSubspace A hA B hB)) ≤ 2 * N.gauge R := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_complex
      N hA B hB hVdom hres hδ hgap hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem, over `ℂ`, on the paper's own
angle, at an arbitrary reducing subspace.**

The same conclusion with the spectral *selection* removed: `U` is any subspace reducing `A`, and
the separation is the form-bounded Sylvester gap between its two reducing restrictions.  Section 1
of the source says in as many words that neither projector is assumed spectral.

Note which subspace reduces which operator: `hred` is about `U`, the gap-carrying subspace, not
about the trial subspace `V`, which is assumed only to lie inside `dom A`. -/
theorem sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hRmem : N.Mem R) :
    N.Mem (Angle.directedSinTwoAngleOperator V U) ∧
      δ * N.gauge (Angle.directedSinTwoAngleOperator V U) ≤ 2 * N.gauge R := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_complex
      N hA hred hVdom hres hδ hgap hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

end Complex

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {V : Submodule ℝ E} [V.HasOrthogonalProjection]
  {M : V →L[ℝ] V} {R : V →L[ℝ] E}
  {A : E →ₗ.[ℝ] E}

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem, over `ℝ`, on the paper's own
angle.**

The real sibling of `sinTwoTheta_directed_unboundedResidual_symmetricNorming_complex`: same
residual, same factor two, same trial-first orientation, with the real directed double-angle
sine `Angle.directedSinTwoAngleOperator` of the real pair.  Nothing here is read in a
complexification. -/
theorem sinTwoTheta_directed_unboundedResidual_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hRmem : N.Mem R) :
    N.Mem (Angle.directedSinTwoAngleOperator V
        (realSelfAdjointSpectralSubspace A hA B hB)) ∧
      δ * N.gauge (Angle.directedSinTwoAngleOperator V
        (realSelfAdjointSpectralSubspace A hA B hB)) ≤ 2 * N.gauge R := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real
      N hA B hB hVdom hres hδ hgap hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem, over `ℝ`, on the paper's own
angle, at an arbitrary reducing subspace.**

`hred` is about `U`, the gap-carrying subspace; the trial subspace `V` is assumed only to lie
inside `dom A`. -/
theorem sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hRmem : N.Mem R) :
    N.Mem (Angle.directedSinTwoAngleOperator V U) ∧
      δ * N.gauge (Angle.directedSinTwoAngleOperator V U) ≤ 2 * N.gauge R := by
  obtain ⟨hmem, hle⟩ :=
    sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_real
      N hA hred hVdom hres hδ hgap hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

end Real

end

end DavisKahan1970
end TauCeti
