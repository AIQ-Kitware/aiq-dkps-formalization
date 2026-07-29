/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.BoundedOperator.Reflection
import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Literal Davis--Kahan 1970 Section 7 sine-double-angle surface

Source anchor: Section 7, equations (7.1)--(7.5), the reflection proof of the
`sin 2Θ` theorem, together with the Section 2 statement `DK-sin2`.

The proof package reflects the perturbed system through the perturbed spectral
subspace `V`: with `J_V = 2P_V - 1`, conjugation fixes `B = A + H` and carries
`A` to a second operator whose distance from `A` is the mirror defect, at most
`2‖H‖` in every source norm.  The cross block between the exact subspace `U`
and the reflected image `J_V U` realizes `sin 2Θ`, and the single-angle sine
theorem applied across the mirror yields the double-angle estimate with the
sharp factor two.

This facade exposes:

* the mirror-defect identities of the proof package (equations (7.1)--(7.3));
* the identification of the reflected cross block with `sin 2Θ`
  (equations (7.4)--(7.5));
* the unbounded bounded-perturbation theorem at operator-norm and
  arbitrary unitary-invariant ideal-gauge scope, in both reflection-residual
  and perturbation forms;
* literal-source forms with the paper's freedom in the choice of the
  `sin 2Θ₀` representative: any operator with the prescribed complete
  singular-value sequence.

The theorems are stated for unbounded self-adjoint closed operators with
genuine spectral subspaces, the paper's most general single-operator setting;
bounded operators are the special case of a bounded closed operator.  The
separate bounded genuine-spectrum modules under
`Experimental/InfiniteDimensional` are not part of the maintained build and
are deliberately not referenced here.

Every declaration below is an alias of, or a thin wrapper around, a compiled
theorem; no new mathematics is introduced in this facade.
-/

namespace TauCeti
namespace DavisKahan1970

open DavisKahan.Experimental.ExactSinTheta
open DavisKahan.Experimental.SpectraBridge

/-! ## The mirror proof package, equations (7.1)--(7.3)

`reflectionDefect V A = J_V A J_V - A` is the mirror defect.  When `V` reduces
the perturbed operator `B`, the defect of the unperturbed operator equals the
reflected perturbation defect and is bounded by twice the perturbation in
every source norm. -/

/-- Equation (7.1): the mirror defect of the exact operator through the
perturbed subspace. -/
alias sinTwoTheta_mirrorDefect := DavisKahan.reflectionDefect

/-- Equation (7.2): when `V` reduces the perturbed operator, the mirror defect
of `A` is the reflected perturbation defect. -/
alias sinTwoTheta_mirrorDefect_eq_perturbationDefect :=
  DavisKahan.reflectionDefect_eq_perturbationDefect

/-- The mirror defect vanishes on reducing subspaces; this is the anchor of
the mirror construction. -/
alias sinTwoTheta_mirrorDefect_eq_zero_of_reduces :=
  DavisKahan.reflectionDefect_eq_zero_of_reduces

/-- Equation (7.3), operator-norm form: the mirror defect costs at most twice
the perturbation. -/
alias sinTwoTheta_mirrorDefect_le_two_mul :=
  DavisKahan.norm_reflectionDefect_le_two_mul

/-- Ideal-gauge form of equation (7.3): the reflected perturbation stays in
every rectangular symmetric ideal with gauge cost at most two. -/
alias sinTwoTheta_mirrorPerturbation_mem_and_gauge_le :=
  DavisKahan.Experimental.SpectraBridge.reflectionPerturbation_mem_and_gauge_le

/-! ## Identification of the double angle, equations (7.4)--(7.5)

The cross block between the exact subspace `U` and the reflected image of its
complement realizes exactly the norm of `sin 2Θ(U, V)`.  This is the geometric
identity that converts the mirrored single-angle estimate into the
double-angle conclusion. -/

/-- Equations (7.4)--(7.5), ambient form: the reflected complementary overlap
block has exactly the norm of `sin 2Θ`. -/
alias sinTwoTheta_reflectedOverlap_norm :=
  DavisKahan.Experimental.SpectraBridge.norm_starProjection_reflectedComplementary_eq_sinTwoAngle

/-- The canonical reflected overlap block whose complete singular-value data
realizes the source's `sin 2Θ₀` in the unbounded ideal theorem. -/
alias sinTwoThetaBlock :=
  DavisKahan.Experimental.SpectraBridge.sinTwoThetaIdealBlock

/-- The canonical block has operator norm exactly `‖sin 2Θ‖`. -/
alias norm_sinTwoThetaBlock :=
  DavisKahan.Experimental.SpectraBridge.norm_sinTwoThetaIdealBlock

/-! ## Unbounded forms

`A` is an unbounded self-adjoint closed operator, `H` a bounded self-adjoint
perturbation, and the subspaces are genuine spectral subspaces of `A` and of
`A + H` for prescribed measurable spectral sets.  The spectral separation is
the source interval/exterior hypothesis. -/

/-- **Davis--Kahan 1970, `sin 2Θ` theorem, unbounded perturbation form at
operator norm.** -/
alias unbounded_sinTwoTheta_opNorm :=
  DavisKahan.Experimental.SpectraBridge.sinTwoTheta_addBounded_of_spectrum_gap

/-- Set-localized interval/exterior form of the unbounded operator-norm
theorem. -/
alias unbounded_sinTwoTheta_intervalExterior_opNorm :=
  DavisKahan.Experimental.SpectraBridge.sinTwoTheta_addBounded_of_intervalExterior

/-- **Reflection-residual form** of the unbounded operator-norm theorem: the
bounded operator `R` implements the mirrored system on the full domain and
controls `sin 2Θ` with constant one. -/
alias unbounded_sinTwoTheta_reflectionResidual_opNorm :=
  DavisKahan.Experimental.SpectraBridge.sinTwoTheta_reflectionResidual_of_spectrum_gap

/-- **Davis--Kahan 1970, `sin 2Θ` theorem, unbounded perturbation form for
every source unitary-invariant ideal family.** -/
alias unbounded_sinTwoTheta_uiNorm :=
  DavisKahan.Experimental.SpectraBridge.sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap

/-- Set-localized interval/exterior form at unitary-invariant ideal scope. -/
alias unbounded_sinTwoTheta_intervalExterior_uiNorm :=
  DavisKahan.Experimental.SpectraBridge.sinTwoTheta_addBounded_unitaryInvariant_of_intervalExterior

/-- Reflection-residual form at rectangular symmetric ideal-gauge scope. -/
alias unbounded_sinTwoTheta_reflectionResidual_gauge :=
  DavisKahan.Experimental.SpectraBridge.sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap

/-! ## Literal source forms with the paper's `sin 2Θ₀` freedom

The paper does not fix a codomain realization of `sin 2Θ₀`; any operator with
the prescribed complete singular-value sequence is admissible.  The theorems
below transport the canonical conclusions along that freedom, exactly as the
literal Theorem 6.1 surface does for the single angle. -/

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open DavisKahan.Experimental.SpectraBridge in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal unbounded perturbation
form.**  The chosen `sin 2Θ₀` may be any operator with the complete
singular-value sequence of the canonical reflected overlap block. -/
theorem unbounded_sinTwoTheta_uiNorm_representative
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (E : H →L[ℂ] H) (hE : DavisKahan.IsSelfAdjointOperator E)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hEmem : N.Mem E)
    (sinTwoTheta₀ : PaperSinThetaRepresentative
      (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (A.addBounded E)
          (addBounded_isSelfAdjoint A hA E hE) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤
        2 * N.gauge E := by
  have hcanonical := sinTwoTheta_addBounded_gauge_of_spectrum_gap
    N.toRectangularSymmetricIdealFamily A hA E hE B S hB hS
      hβα hδ hBlow hBhigh hBcomplSpec hEmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

open DavisKahan.Experimental.SpectraBridge in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal reflection-residual
form.**  The bounded operator `R` implements the mirrored system on the full
domain; the chosen `sin 2Θ₀` may be any operator with the complete
singular-value sequence of the canonical reflected overlap block, and it is
controlled by the residual with constant one. -/
theorem unbounded_sinTwoTheta_residual_uiNorm_representative
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    (R : H →L[ℂ] H) (hR : DavisKahan.IsSelfAdjointOperator R)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBlow : SemiboundedBelow
      (selfAdjointSpectralRestriction A hA B hB) β)
    (hBhigh : SemiboundedAbove
      (selfAdjointSpectralRestriction A hA B hB) α)
    (hBcomplSpec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (selfAdjointSpectralRestriction A hA Bᶜ hB.compl).toLinearPMap)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (A.addBounded R).toLinearMap
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A.toLinearMap x))
    (hRmem : N.Mem R)
    (sinTwoTheta₀ : PaperSinThetaRepresentative
      (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V)) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤
        N.gauge R := by
  have hcanonical := sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap
    N.toRectangularSymmetricIdealFamily A hA R hR B hB V
      hβα hδ hBlow hBhigh hBcomplSpec hJdom hJintertwines hRmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

end DavisKahan1970
end TauCeti