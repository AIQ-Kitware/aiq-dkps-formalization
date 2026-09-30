/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric
import DavisKahan.Sources.DavisKahan1970.SineTheta.SymmetricReal
import DavisKahan.Geometry.Angle.AngleFunctionalCalculus
import DavisKahan.Geometry.Angle.OperatorAngleGeneric
import DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomainSymmetric
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import DavisKahan.Sylvester.ScalarTransport
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Proposition 6.1, on ordinary mathematical hypotheses

Proposition 6.1 is the whole-space (ambient) sine theorem: two bounded
self-adjoint operators, a subspace reducing each, a separation `δ` between the
two crossed pairs of blocks, and the conclusion `δ · N(sin Θ) ≤ N(B − A)` for
every source unitarily invariant norm.

## What changed, and why

The canonical Proposition 6.1 declarations used to be *methods on a record*:
a caller had to build `SymmetricSinThetaProblem` (or its real sibling) and
then invoke `result_every_unitarilyInvariantNorm`.  That record is good proof
organisation -- it names the two directed applications of the single-angle
theorem that the paper's proof makes -- but it is not something a reader of the
paper should have to construct in order to use the theorem.

The two theorems below take the mathematics directly: the operators, their
self-adjointness, the two subspaces, the two reducing hypotheses, the gap, the
two separations, and membership of the perturbation.  The record is built inside
the proof.  `DavisKahanExt.PartialMap.boundedReducingBlock` and its
complement partner are what make the separation hypotheses readable; before
them, each was a four-line inline composite, and that unreadability is most of
why the record existed.

## Presentation object and proof representatives

The canonical complex and real declarations are both stated on the paper's
literal expression `cfc Real.sin (Angle.angleOperator U V)`.  The exact theorem
`Angle.cfc_sin_angleOperator` identifies this functional-calculus expression with
the positive ambient sine operator.

The proof engines remain representation-oriented.  Over `ℂ` they use
`sinAngleOperatorC = |P_U - P_V|`; over `ℝ` they pass through the projector
difference `P_V - P_U`, whose complete approximation-number sequence is proved
to agree with the positive sine.  `crossSineSum` -- the still lower-level
representative `P_Uᗮ P_V + P_U P_Vᗮ` -- remains the object the real proof computes
with.  These correspondences are explicit theorems and are used only to transport
the proof result back to the literal source object.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Proposition 6.1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta


open TauCeti.DavisKahan

noncomputable section

universe u v

/-! ## Over a complex Hilbert space -/

section Complex

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 6.1, over `ℂ`.**

`A` and `B` are bounded self-adjoint operators, `U` reduces `A`, `V` reduces
`B`, and `δ > 0` separates each selected block from the other's complementary
block.  Then the ambient `sin Θ` between `U` and `V` lies in the ideal of every
source unitarily invariant norm and satisfies `δ · N(sin Θ) ≤ N(B − A)`.

This proof-facing theorem concludes on the positive sine representative
`sinAngleOperatorC U V`.  The canonical source-facing theorem immediately
below rewrites it to the paper's literal `cfc Real.sin (Angle.angleOperator U V)`
through an exact functional-calculus identity. -/
theorem proposition6_1_sinAngleOperator_complex
    (N : SymmetricNormingFunction)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock A U hU)
      (PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock B V hV)
      (PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (sinAngleOperatorC U V) ∧
      δ * N.gauge (sinAngleOperatorC U V) ≤ N.gauge (B - A) := by
  let P : SymmetricSinThetaProblem (E := E) :=
    { A := A
      B := B
      selfAdjoint_A := hA
      selfAdjoint_B := hB
      U := U
      V := V
      proj_U := inferInstance
      proj_V := inferInstance
      reduces_A_U := hU
      reduces_B_V := hV
      gap := δ
      gap_pos := hδ
      gap_U_to_Vperp := hgapUV
      gap_V_to_Uperp := hgapVU }
  have hsource := P.result_every_unitarilyInvariantNorm N (by
    simpa [P, SymmetricSinThetaProblem.perturbation] using hMem)
  simpa [P, SymmetricSinThetaProblem.perturbation] using hsource

/-- **Davis--Kahan 1970, Proposition 6.1, over `ℂ`, literal presentation.**

The theorem is stated on the expression printed in the source,
`sin Θ = cfc Real.sin (Angle.angleOperator U V)`.  The proof-facing positive
sine `sinAngleOperatorC` remains underneath, and `Angle.cfc_sin_angleOperator`
proves the two operators are exactly equal. -/
theorem proposition6_1_complex
    (N : SymmetricNormingFunction)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock A U hU)
      (PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock B V hV)
      (PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (cfc Real.sin (Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (Angle.angleOperator U V)) ≤ N.gauge (B - A) := by
  rw [Angle.cfc_sin_angleOperator, Angle.sinAngleOperator_complex]
  exact proposition6_1_sinAngleOperator_complex
    N hA hB hU hV hδ hgapUV hgapVU hMem

/-- **Proposition 6.1 over `ℂ`, read on the projector difference.**

`sinAngleOperatorC U V` is `|P_U − P_V|` by definition, and a modulus has the
singular values of its argument, so this is the same estimate on `P_V − P_U`.
It is stated because it is the shape the real theorem below has, which is what
makes the two fields visibly one theorem. -/
theorem proposition6_1_projectorDifference_complex
    (N : SymmetricNormingFunction)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock A U hU)
      (PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock B V hV)
      (PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (V.starProjection - U.starProjection) ∧
      δ * N.gauge (V.starProjection - U.starProjection) ≤ N.gauge (B - A) := by
  obtain ⟨hmem, hle⟩ :=
    proposition6_1_sinAngleOperator_complex N hA hB hU hV hδ hgapUV hgapVU hMem
  have hflip : U.starProjection - V.starProjection
      = -(V.starProjection - U.starProjection) := by abel
  have hext : N.extendedGauge (sinAngleOperatorC U V)
      = N.extendedGauge (V.starProjection - U.starProjection) := by
    rw [N.gauge_eq_of_sameApproximationSingularValues
      (sin_same_projectionDiff U V), hflip]
    exact N.gauge_eq_of_sameApproximationSingularValues
      (sameApproximationSingularValues_neg _)
  have hmem' : N.Mem (V.starProjection - U.starProjection) := by
    have : N.extendedGauge (V.starProjection - U.starProjection) ≠ ⊤ := by
      rw [← hext]; exact hmem
    exact this
  have hgauge : N.gauge (sinAngleOperatorC U V)
      = N.gauge (V.starProjection - U.starProjection) := by
    unfold SymmetricNormingFunction.gauge
    rw [hext]
  exact ⟨hmem', by rwa [hgauge] at hle⟩

end Complex

/-! ## Over a real Hilbert space -/

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 6.1, over `ℝ`.**

The same theorem as `proposition6_1_projectorDifference_complex`, over a
real Hilbert space, with the same hypotheses and the same conclusion on the
projector difference `P_V − P_U`, whose approximation numbers are the sines of
the principal angles between `U` and `V`.

No functional calculus, no complexification and no representative supplied by
the caller occurs in the statement.  The proof runs through
`crossSineSum`, which the source real development computes with, and
transports the conclusion off it. -/
theorem proposition6_1_projectorDifference_real
    (N : SymmetricNormingFunction)
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock A U hU)
      (PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock B V hV)
      (PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (V.starProjection - U.starProjection) ∧
      δ * N.gauge (V.starProjection - U.starProjection) ≤ N.gauge (B - A) := by
  let P : RealSymmetricSinThetaProblem (E := E) :=
    { A := A
      B := B
      selfAdjoint_A := hA
      selfAdjoint_B := hB
      U := U
      V := V
      proj_U := inferInstance
      proj_V := inferInstance
      reduces_A_U := hU
      reduces_B_V := hV
      gap := δ
      gap_pos := hδ
      gap_U_to_Vperp := hgapUV
      gap_V_to_Uperp := hgapVU }
  have hsource := P.result_every_unitarilyInvariantNorm_real N (by
    simpa [P, RealSymmetricSinThetaProblem.perturbation] using hMem)
  obtain ⟨hiff, hgauge⟩ := P.crossSineSum_normingMem_iff_and_gauge_eq N
  have hmem : N.Mem (V.starProjection - U.starProjection) := by
    have := hiff.mp (by simpa [P] using hsource.1)
    simpa [P] using this
  refine ⟨hmem, ?_⟩
  have hle := hsource.2
  rw [hgauge] at hle
  simpa [P, RealSymmetricSinThetaProblem.perturbation] using hle

/-- **Davis--Kahan 1970, Proposition 6.1, over `ℝ`, literal presentation.**

The conclusion is on `cfc Real.sin (Angle.angleOperator U V)`.  The real proof
continues to compute with the projector difference; the complete
approximation-number bridge and the exact identity
`Angle.cfc_sin_angleOperator` make the presentation transport explicit. -/
theorem proposition6_1_real
    (N : SymmetricNormingFunction)
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock A U hU)
      (PartialMap.boundedReducingBlockCompl B V hV) δ)
    (hgapVU : FormBoundedSylvesterGap
      (PartialMap.boundedReducingBlock B V hV)
      (PartialMap.boundedReducingBlockCompl A U hU) δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (cfc Real.sin (Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (Angle.angleOperator U V)) ≤ N.gauge (B - A) := by
  obtain ⟨hprojMem, hprojBound⟩ :=
    proposition6_1_projectorDifference_real
      N hA hB hU hV hδ hgapUV hgapVU hMem
  have hseq := Angle.sinAngleOperator_hasSameApproximationNumbers_projectorDifference U V
  have htransport :=
    TauCeti.DavisKahan.ExactSinTheta.SameApproximationSingularSequence.normingMem_iff_and_gauge_eq
      N hseq
  rw [Angle.cfc_sin_angleOperator]
  refine ⟨htransport.1.mpr hprojMem, ?_⟩
  rw [htransport.2]
  exact hprojBound

end Real

/-! ## The Appendix common-domain relaxation

The Appendix to Section 6 says, after describing the unbounded reading of the
sine theorem:

> Proposition 6.1 and Theorem 6.1 admit the analogous relaxation.

That is an explicit extension of Proposition 6.1's proved scope, and it is
`DK-6-appendix.proposition61-common-domain-extension` in the source-atom ledger.
The relaxation replaces the two bounded self-adjoint operators by two *closed*
self-adjoint operators sharing one dense domain, whose difference there is the
paper's bounded `H`.

The domain hypothesis is `A.domain = B.domain`, not a residual relation, so
`IsTrialResidualEquation` is deliberately **not** used here: it would express a
different (weaker, one-sided) condition than the source states. -/

section CommonDomain

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 6.1 under the Appendix common-domain
relaxation, over `ℂ`.**

`A` and `B` are closed self-adjoint operators sharing one domain, `U` reduces
`A`, `V` reduces `B`, and on the common domain `B − A` is the bounded `H`.  The
conclusion is the same as in the bounded case, on the paper's literal `sin Θ`.

`proposition6_1_commonDomain_ofBounded` records that the bounded inputs are an
instance, so this is a genuine relaxation rather than a parallel statement. -/
theorem proposition6_1_commonDomain_sinAngleOperator_complex
    (N : SymmetricNormingFunction)
    {A B : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace B V)
    (Hop : E →L[ℂ] E)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hU)
      (TauCeti.LinearPMap.reducingRestriction B Vᗮ hV.orthogonal) δ)
    (hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B V hV)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hU.orthogonal) δ)
    (hMem : N.Mem Hop) :
    N.Mem (sinAngleOperatorC U V) ∧
      δ * N.gauge (sinAngleOperatorC U V) ≤ N.gauge Hop := by
  let P : CommonDomainSymmetricSinThetaProblem (𝕜 := ℂ) (E := E) U V :=
    { A := A
      B := B
      selfAdjoint_A := hA
      selfAdjoint_B := hB
      reduces_A_U := hU
      reduces_B_V := hV
      perturbation := Hop
      domain_eq := hdomain
      perturbation_eq := hperturbation
      gap := δ
      gap_pos := hδ
      gap_U_to_Vperp := hgapUV
      gap_V_to_Uperp := hgapVU }
  exact P.result_every_unitarilyInvariantNorm N hMem

/-- **Proposition 6.1 under the Appendix common-domain relaxation, over `ℂ`,
literal presentation.** -/
theorem proposition6_1_commonDomain_complex
    (N : SymmetricNormingFunction)
    {A B : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace B V)
    (Hop : E →L[ℂ] E)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hU)
      (TauCeti.LinearPMap.reducingRestriction B Vᗮ hV.orthogonal) δ)
    (hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B V hV)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hU.orthogonal) δ)
    (hMem : N.Mem Hop) :
    N.Mem (cfc Real.sin (Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (Angle.angleOperator U V)) ≤ N.gauge Hop := by
  rw [Angle.cfc_sin_angleOperator, Angle.sinAngleOperator_complex]
  exact proposition6_1_commonDomain_sinAngleOperator_complex
    N hA hB hU hV Hop hdomain hperturbation hδ hgapUV hgapVU hMem

/-- **Davis--Kahan 1970, Proposition 6.1 under the Appendix common-domain
relaxation, over `ℝ`.**

The real proof-facing sibling, with the conclusion on the projector difference
`P_V − P_U`.  The canonical `proposition6_1_commonDomain_real` immediately below
transports this to literal `cfc Real.sin (Angle.angleOperator U V)`.  The proof
runs through `crossSineSum` and transports the conclusion off it in two explicit
steps. -/
theorem proposition6_1_commonDomain_projectorDifference_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A B : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℝ Er} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace B V)
    (Hop : Er →L[ℝ] Er)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : Er) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hU)
      (TauCeti.LinearPMap.reducingRestriction B Vᗮ hV.orthogonal) δ)
    (hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B V hV)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hU.orthogonal) δ)
    (hMem : N.Mem Hop) :
    N.Mem (V.starProjection - U.starProjection) ∧
      δ * N.gauge (V.starProjection - U.starProjection) ≤ N.gauge Hop := by
  let P : CommonDomainSymmetricSinThetaProblem (𝕜 := ℝ) (E := Er) U V :=
    { A := A
      B := B
      selfAdjoint_A := hA
      selfAdjoint_B := hB
      reduces_A_U := hU
      reduces_B_V := hV
      perturbation := Hop
      domain_eq := hdomain
      perturbation_eq := hperturbation
      gap := δ
      gap_pos := hδ
      gap_U_to_Vperp := hgapUV
      gap_V_to_Uperp := hgapVU }
  obtain ⟨hmem, hle⟩ := P.result_every_unitarilyInvariantNorm_real N hMem
  obtain ⟨hiff, hgauge⟩ := P.crossSineSum_normingMem_iff_and_gauge_eq N
  refine ⟨hiff.mp hmem, ?_⟩
  rw [hgauge] at hle
  exact hle

/-- **Proposition 6.1 under the Appendix common-domain relaxation, over `ℝ`,
literal presentation.** -/
theorem proposition6_1_commonDomain_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : SymmetricNormingFunction)
    {A B : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℝ Er} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace B V)
    (Hop : Er →L[ℝ] Er)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : Er) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hU)
      (TauCeti.LinearPMap.reducingRestriction B Vᗮ hV.orthogonal) δ)
    (hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B V hV)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hU.orthogonal) δ)
    (hMem : N.Mem Hop) :
    N.Mem (cfc Real.sin (Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (Angle.angleOperator U V)) ≤ N.gauge Hop := by
  obtain ⟨hprojMem, hprojBound⟩ :=
    proposition6_1_commonDomain_projectorDifference_real
      N hA hB hU hV Hop hdomain hperturbation hδ hgapUV hgapVU hMem
  have hseq := Angle.sinAngleOperator_hasSameApproximationNumbers_projectorDifference U V
  have htransport :=
    TauCeti.DavisKahan.ExactSinTheta.SameApproximationSingularSequence.normingMem_iff_and_gauge_eq
      N hseq
  rw [Angle.cfc_sin_angleOperator]
  refine ⟨htransport.1.mpr hprojMem, ?_⟩
  rw [htransport.2]
  exact hprojBound

/-! ### The common-domain relaxation over any `RCLike` field

The two fixed-field statements above are specializations of the same generic
mathematics.  The proof-facing theorem is stated on the projector difference,
while `proposition6_1_commonDomain_presentation_rclike` below is the canonical
source-facing endpoint on `Angle.ambientSinThetaOperator U V`.  That object is
*defined* as the literal functional-calculus expression
`cfc Real.sin (Angle.angleOperator U V)` inside the generic angle module, where
the required real-calculus instances are installed.  Its exact bridge to the
positive sine and the complete approximation-number bridge to the projector
difference make every semantic step explicit. -/

section CommonDomainGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 6.1 under the Appendix common-domain
relaxation, over any `RCLike` field, read on the projector difference.**

The two capability binders are the Sylvester estimate and the min--max lower
bound: both are instances at `ℝ` and at `ℂ`, so at either field they are
discharged by instance search and nothing is assumed that was not already
proved. -/
theorem proposition6_1_commonDomain_projectorDifference
    (N : SymmetricNormingFunction)
    {A B : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace B V)
    (Hop : E →L[𝕜] E)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hU)
      (TauCeti.LinearPMap.reducingRestriction B Vᗮ hV.orthogonal) δ)
    (hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B V hV)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hU.orthogonal) δ)
    (hMem : N.Mem Hop) :
    N.Mem (V.starProjection - U.starProjection) ∧
      δ * N.gauge (V.starProjection - U.starProjection) ≤ N.gauge Hop := by
  let P : CommonDomainSymmetricSinThetaProblem (𝕜 := 𝕜) (E := E) U V :=
    { A := A
      B := B
      selfAdjoint_A := hA
      selfAdjoint_B := hB
      reduces_A_U := hU
      reduces_B_V := hV
      perturbation := Hop
      domain_eq := hdomain
      perturbation_eq := hperturbation
      gap := δ
      gap_pos := hδ
      gap_U_to_Vperp := hgapUV
      gap_V_to_Uperp := hgapVU }
  obtain ⟨hmem, hle⟩ := P.result_every_unitarilyInvariantNorm_crossSineSum N hMem
  obtain ⟨hiff, hgauge⟩ := P.crossSineSum_normingMem_iff_and_gauge_eq N
  refine ⟨hiff.mp hmem, ?_⟩
  rw [hgauge] at hle
  exact hle

/-- **Davis--Kahan 1970, Proposition 6.1 under the Appendix common-domain
relaxation, scalar-generic literal presentation.**

This is the generic source-facing endpoint.  The projector-difference theorem
above remains the proof API; the statement here is on
`Angle.ambientSinThetaOperator U V`, whose definition is literally
`cfc Real.sin (Angle.angleOperator U V)`, and crosses the boundary through the
proved sine/modulus and approximation-number identities. -/
theorem proposition6_1_commonDomain_presentation_rclike
    (N : SymmetricNormingFunction)
    {A B : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace B V)
    (Hop : E →L[𝕜] E)
    (hdomain : A.domain = B.domain)
    (hperturbation : ∀ (x : E) (hxA : x ∈ A.domain) (hxB : x ∈ B.domain),
      B ⟨x, hxB⟩ - A ⟨x, hxA⟩ = Hop x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapUV : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hU)
      (TauCeti.LinearPMap.reducingRestriction B Vᗮ hV.orthogonal) δ)
    (hgapVU : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B V hV)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hU.orthogonal) δ)
    (hMem : N.Mem Hop) :
    N.Mem (Angle.ambientSinThetaOperator U V) ∧
      δ * N.gauge (Angle.ambientSinThetaOperator U V) ≤ N.gauge Hop := by
  obtain ⟨hprojMem, hprojBound⟩ :=
    proposition6_1_commonDomain_projectorDifference
      N hA hB hU hV Hop hdomain hperturbation hδ hgapUV hgapVU hMem
  have hseq := Angle.sinAngleOperator_hasSameApproximationNumbers_projectorDifference U V
  have htransport :=
    TauCeti.DavisKahan.ExactSinTheta.SameApproximationSingularSequence.normingMem_iff_and_gauge_eq
      N hseq
  rw [Angle.ambientSinThetaOperator_eq_sinAngleOperator]
  refine ⟨htransport.1.mpr hprojMem, ?_⟩
  rw [htransport.2]
  exact hprojBound

end CommonDomainGeneric

end CommonDomain

end

end DavisKahan1970
end TauCeti
