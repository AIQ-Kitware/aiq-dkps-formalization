/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric
import DavisKahan.Sources.DavisKahan1970.SineTheta.SymmetricReal
import DavisKahan.Geometry.Angle.PaperOperatorAngle

/-!
# Davis--Kahan 1970, Proposition 6.1, on ordinary mathematical hypotheses

Proposition 6.1 is the whole-space (ambient) sine theorem: two bounded
self-adjoint operators, a subspace reducing each, a separation `δ` between the
two crossed pairs of blocks, and the conclusion `δ · N(sin Θ) ≤ N(B − A)` for
every source unitarily invariant norm.

## What changed, and why

The canonical Proposition 6.1 declarations used to be *methods on a record*:
a caller had to build `PaperSymmetricSinThetaProblem` (or its real sibling) and
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

## The two conclusions, and why they are the same theorem

Over `ℂ` the conclusion is the paper's literal object,
`paperSinAngleOperatorC U V = cfc Real.sin (paperAngleOperatorC U V)`.

Over `ℝ` there is no continuous functional calculus in this development, and
building one would be the wrong response: a unitarily invariant norm sees an
operator only through its complete singular-value sequence.  The real conclusion
is therefore stated on the **projector difference** `P_V − P_U`, whose
approximation numbers are the sines of the principal angles.  That is not a
weaker statement, and it is not a different one:
`paperSinAngleOperatorC_eq` and `sinAngleOperatorC` identify the complex angle
operator with `|P_U − P_V|`, so `proposition6_1_source_projectorDifference_complex`
below states the *same* conclusion over `ℂ`, and the complex and real surfaces
are visibly one theorem.

`paperCrossSineSum` -- the implementation representative `P_Uᗮ P_V + P_U P_Vᗮ` --
does not appear in any statement here.  It remains the object the real proof
computes with, and `PaperRealSymmetricSinThetaProblem.crossSineSum_paperMem_iff_and_gauge_eq`
is the compiled transport from it to the projector difference.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Proposition 6.1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe v

/-! ## Over a complex Hilbert space -/

section Complex

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 6.1, over `ℂ`.**

`A` and `B` are bounded self-adjoint operators, `U` reduces `A`, `V` reduces
`B`, and `δ > 0` separates each selected block from the other's complementary
block.  Then the ambient `sin Θ` between `U` and `V` lies in the ideal of every
source unitarily invariant norm and satisfies `δ · N(sin Θ) ≤ N(B − A)`.

The conclusion is on the paper's literal `sin Θ`,
`cfc Real.sin (paperAngleOperatorC U V)`.  Nothing about the proof's
organisation is visible: no `PaperSymmetricSinThetaProblem`, no
`UnboundedSinThetaData`, no Ky Fan family. -/
theorem proposition6_1_source_complex
    (N : PaperUnitaryInvariantNorm)
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
    N.Mem (paperSinAngleOperatorC U V) ∧
      δ * N.gauge (paperSinAngleOperatorC U V) ≤ N.gauge (B - A) := by
  let P : PaperSymmetricSinThetaProblem (E := E) :=
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
    simpa [P, PaperSymmetricSinThetaProblem.perturbation] using hMem)
  simpa [P, PaperSymmetricSinThetaProblem.perturbation] using hsource

/-- **Proposition 6.1 over `ℂ`, read on the projector difference.**

`paperSinAngleOperatorC U V` is `|P_U − P_V|`
(`paperSinAngleOperatorC_eq`, `sinAngleOperatorC`), and a modulus has the
singular values of its argument, so this is the same estimate on `P_V − P_U`.
It is stated because it is the shape the real theorem below has, which is what
makes the two fields visibly one theorem. -/
theorem proposition6_1_source_projectorDifference_complex
    (N : PaperUnitaryInvariantNorm)
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
    proposition6_1_source_complex N hA hB hU hV hδ hgapUV hgapVU hMem
  have hflip : U.starProjection - V.starProjection
      = -(V.starProjection - U.starProjection) := by abel
  have hext : N.extendedGauge (paperSinAngleOperatorC U V)
      = N.extendedGauge (V.starProjection - U.starProjection) := by
    rw [N.gauge_eq_of_sameApproximationSingularValues
      (paperSin_same_projectionDiff U V), hflip]
    exact N.gauge_eq_of_sameApproximationSingularValues
      (sameApproximationSingularValues_neg _)
  have hmem' : N.Mem (V.starProjection - U.starProjection) := by
    have : N.extendedGauge (V.starProjection - U.starProjection) ≠ ⊤ := by
      rw [← hext]; exact hmem
    exact this
  have hgauge : N.gauge (paperSinAngleOperatorC U V)
      = N.gauge (V.starProjection - U.starProjection) := by
    unfold PaperUnitaryInvariantNorm.gauge
    rw [hext]
  exact ⟨hmem', by rwa [hgauge] at hle⟩

end Complex

/-! ## Over a real Hilbert space -/

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Proposition 6.1, over `ℝ`.**

The same theorem as `proposition6_1_source_projectorDifference_complex`, over a
real Hilbert space, with the same hypotheses and the same conclusion on the
projector difference `P_V − P_U`, whose approximation numbers are the sines of
the principal angles between `U` and `V`.

No functional calculus, no complexification and no representative supplied by
the caller occurs in the statement.  The proof runs through
`paperCrossSineSum`, which the source real development computes with, and
transports the conclusion off it. -/
theorem proposition6_1_source_real
    (N : PaperUnitaryInvariantNorm)
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
  let P : PaperRealSymmetricSinThetaProblem (E := E) :=
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
    simpa [P, PaperRealSymmetricSinThetaProblem.perturbation] using hMem)
  obtain ⟨hiff, hgauge⟩ := P.crossSineSum_paperMem_iff_and_gauge_eq N
  have hmem : N.Mem (V.starProjection - U.starProjection) := by
    have := hiff.mp (by simpa [P] using hsource.1)
    simpa [P] using this
  refine ⟨hmem, ?_⟩
  have hle := hsource.2
  rw [hgauge] at hle
  simpa [P, PaperRealSymmetricSinThetaProblem.perturbation] using hle

end Real

end

end DavisKahan1970
end TauCeti
