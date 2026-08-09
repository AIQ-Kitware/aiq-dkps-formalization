/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.BoundedOperator.Reflection
import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.DoubleAngle.RealAngleIdentification
import DavisKahan.DoubleAngle.RealUnboundedIdeal
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
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
open DavisKahan.Experimental

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
  DavisKahan.Experimental.reflectionPerturbation_mem_and_gauge_le

/-! ## Identification of the double angle, equations (7.4)--(7.5)

The cross block between the exact subspace `U` and the reflected image of its
complement realizes exactly the norm of `sin 2Θ(U, V)`.  This is the geometric
identity that converts the mirrored single-angle estimate into the
double-angle conclusion. -/

/-- Equations (7.4)--(7.5), ambient form: the reflected complementary overlap
block has exactly the norm of `sin 2Θ`. -/
alias sinTwoTheta_reflectedOverlap_norm :=
  DavisKahan.Experimental.norm_starProjection_reflectedComplementary_eq_sinTwoAngle

/-- The canonical reflected overlap block whose complete singular-value data
realizes the source's `sin 2Θ₀` in the unbounded ideal theorem. -/
alias sinTwoThetaBlock :=
  DavisKahan.Experimental.sinTwoThetaIdealBlock

/-- The canonical block has operator norm exactly `‖sin 2Θ‖`. -/
alias norm_sinTwoThetaBlock :=
  DavisKahan.Experimental.norm_sinTwoThetaIdealBlock

/-- Equations (7.4)--(7.5) over a **real** Hilbert space: the canonical block
has operator norm exactly `‖sin 2Θ‖` of the real pair. -/
alias norm_sinTwoThetaBlock_real :=
  DavisKahan.Experimental.norm_sinTwoThetaIdealBlock_real

/-! ## Unbounded forms

`A` is an unbounded self-adjoint closed operator, `H` a bounded self-adjoint
perturbation, and the subspaces are genuine spectral subspaces of `A` and of
`A + H` for prescribed measurable spectral sets.  The spectral separation is
the source interval/exterior hypothesis. -/

/-- **Davis--Kahan 1970, `sin 2Θ` theorem, unbounded perturbation form at
operator norm.** -/
alias unbounded_sinTwoTheta_opNorm :=
  DavisKahan.Experimental.sinTwoTheta_addBounded_of_spectrum_gap

/-- Set-localized interval/exterior form of the unbounded operator-norm
theorem. -/
alias unbounded_sinTwoTheta_intervalExterior_opNorm :=
  DavisKahan.Experimental.sinTwoTheta_addBounded_of_intervalExterior

/-- **Reflection-residual form** of the unbounded operator-norm theorem: the
bounded operator `R` implements the mirrored system on the full domain and
controls `sin 2Θ` with constant one. -/
alias unbounded_sinTwoTheta_reflectionResidual_opNorm :=
  DavisKahan.Experimental.sinTwoTheta_reflectionResidual_of_spectrum_gap

/-- **Davis--Kahan 1970, `sin 2Θ` theorem, unbounded perturbation form for
every source unitary-invariant ideal family.** -/
alias unbounded_sinTwoTheta_uiNorm :=
  DavisKahan.Experimental.sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap

/-- Set-localized interval/exterior form at unitary-invariant ideal scope. -/
alias unbounded_sinTwoTheta_intervalExterior_uiNorm :=
  DavisKahan.Experimental.sinTwoTheta_addBounded_unitaryInvariant_of_intervalExterior

/-- Reflection-residual form at rectangular symmetric ideal-gauge scope. -/
alias unbounded_sinTwoTheta_reflectionResidual_gauge :=
  DavisKahan.Experimental.sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap

/-! ## Literal source forms with the paper's `sin 2Θ₀` freedom

The paper does not fix a codomain realization of `sin 2Θ₀`; any operator with
the prescribed complete singular-value sequence is admissible.  The theorems
below transport the canonical conclusions along that freedom, exactly as the
literal Theorem 6.1 surface does for the single angle. -/

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open DavisKahan.Experimental in
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
    N.toSymmetricOperatorIdealFamily A hA E hE B S hB hS
      hβα hδ hBlow hBhigh hBcomplSpec hEmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

open DavisKahan.Experimental in
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
    N.toSymmetricOperatorIdealFamily A hA R hR B hB V
      hβα hδ hBlow hBhigh hBcomplSpec hJdom hJintertwines hRmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

/-! ## Real-scalar forms

Standing assumption 1 of the source says the Hilbert space is "real or
complex".  The two theorems below are the real-scalar counterparts of the two
directed statements above, at the same unbounded scope and with the same
`sin 2Θ₀` representative freedom.  The gap is carried by the scalar-generic
form-bounded Sylvester predicate between the two real spectral restrictions,
which is the weaker of this tree's two spellings of spectral separation; the
`ℂ`-only resolvent-set spelling used above has no real counterpart, since
`TauCeti.LinearPMap.spectrum` is defined over `ℂ`.

The ambient (whole-space) half `δ ‖sin 2Θ‖ ≤ 2‖H‖` over the reals is
`TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`. -/

variable {Er : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]

open DavisKahan.Experimental DavisKahan.Experimental.RealSpectralRestriction in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal unbounded perturbation form
over a REAL Hilbert space.**  The chosen `sin 2Θ₀` may be any operator with the
complete singular-value sequence of the canonical reflected overlap block. -/
theorem unbounded_sinTwoTheta_uiNorm_representative_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := Er))
    (hA : A.IsSelfAdjoint)
    (Eop : Er →L[ℝ] Er) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop)
    (sinTwoTheta₀ : PaperSinThetaRepresentative
      (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (A.addBounded Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS))) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ 2 * N.gauge Eop := by
  have hcanonical := sinTwoTheta_addBounded_gauge_real
    A hA Eop hEop N B S hB hS hδ hgap hEmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

open DavisKahan.Experimental DavisKahan.Experimental.RealSpectralRestriction in
/-- **Davis--Kahan 1970, `sin 2Θ` theorem, literal reflection-residual form
over a REAL Hilbert space.**  The bounded operator `R` implements the mirrored
system on the full domain; the chosen `sin 2Θ₀` may be any operator with the
complete singular-value sequence of the canonical reflected overlap block, and
it is controlled by the residual with constant one. -/
theorem unbounded_sinTwoTheta_residual_uiNorm_representative_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := Er))
    (hA : A.IsSelfAdjoint)
    (R : Er →L[ℝ] Er) (hR : DavisKahan.IsSelfAdjointOperator R)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : Er) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (A.addBounded R).toLinearMap
          ⟨V.reflectionOperator (x : Er), hJdom x⟩ =
        V.reflectionOperator (A.toLinearMap x))
    (hRmem : N.Mem R)
    (sinTwoTheta₀ : PaperSinThetaRepresentative
      (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V)) :
    N.Mem sinTwoTheta₀.operator ∧
      δ * N.gauge sinTwoTheta₀.operator ≤ N.gauge R := by
  have hcanonical := sinTwoTheta_reflectionResidual_gauge_real
    A hA B hB N R hR V hδ hgap hJdom hJintertwines hRmem
  obtain ⟨hmem, hgauge⟩ := sinTwoTheta₀.mem_and_gauge_eq N hcanonical.1
  refine ⟨hmem, ?_⟩
  rw [hgauge]
  exact hcanonical.2

/-! ### The real directed forms at the paper's own unitarily invariant norm

`PaperUnitaryInvariantNorm` is the source's symmetric-gauge presentation, and it
is the class the real ambient half `sinTwoTheta_wholeSpace_paperUINorm_real` is
stated over.  Reading the real Ky-Fan-dominant theorems at each finite Ky Fan
family and closing with Fan dominance puts the real directed half at the same
class, so both printed conclusions of the Section 2 `sin 2Θ` theorem are now
available over `ℝ` for the same notion of "every unitarily invariant norm". -/

omit [CompleteSpace Er] in
private theorem kyFanApproximationGauge_zero_real {Fr : Type v}
    [NormedAddCommGroup Fr] [InnerProductSpace ℝ Fr]
    (T : Er →L[ℝ] Fr) : kyFanApproximationGauge 0 T = 0 := by
  simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]

open DavisKahan.Experimental DavisKahan.Experimental.RealSpectralRestriction in
/-- **Davis--Kahan 1970, directed `sin 2Θ` theorem over a REAL Hilbert space,
reflection-residual form, for every source unitarily invariant norm**:
`δ ‖sin 2Θ₀‖ ≤ ‖R‖`. -/
theorem sinTwoTheta_reflectionResidual_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := Er))
    (hA : A.IsSelfAdjoint)
    (R : Er →L[ℝ] Er) (hR : DavisKahan.IsSelfAdjointOperator R)
    (B : Set ℝ) (hB : MeasurableSet B)
    (V : Submodule ℝ Er) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : Er) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (A.addBounded R).toLinearMap
          ⟨V.reflectionOperator (x : Er), hJdom x⟩ =
        V.reflectionOperator (A.toLinearMap x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB) V) ≤ N.gauge R := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hδ hRmem fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge_zero_real, kyFanApproximationGauge_zero_real,
      mul_zero]
  · have h := sinTwoTheta_reflectionResidual_gauge_real A hA B hB
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk) R hR V hδ hgap
      hJdom hJintertwines (KyFanDominantIdealFamily.kyFan_mem k hk R)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

open DavisKahan.Experimental DavisKahan.Experimental.RealSpectralRestriction in
/-- **Davis--Kahan 1970, directed `sin 2Θ` theorem over a REAL Hilbert space,
bounded-perturbation form, for every source unitarily invariant norm**:
`δ ‖sin 2Θ₀‖ ≤ 2‖E‖`, with the paper's sharp factor two. -/
theorem sinTwoTheta_addBounded_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := Er))
    (hA : A.IsSelfAdjoint)
    (Eop : Er →L[ℝ] Er) (hEop : DavisKahan.IsSelfAdjointOperator Eop)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (A.addBounded Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (A.addBounded Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  have hhalf : 0 < δ / 2 := by linarith
  have hmain := N.mul_gauge_le_of_all_mul_kyFan_le hhalf hEmem
    (A := sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA B hB)
        (realSelfAdjointSpectralSubspace (A.addBounded Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) (fun k => ?_)
  · exact ⟨hmain.1, by linarith [hmain.2]⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [kyFanApproximationGauge_zero_real, kyFanApproximationGauge_zero_real,
        mul_zero]
    · have h := sinTwoTheta_addBounded_gauge_real A hA Eop hEop
        (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk) B S hB hS hδ hgap
        (KyFanDominantIdealFamily.kyFan_mem k hk Eop)
      rw [KyFanDominantIdealFamily.kyFan_gauge,
        KyFanDominantIdealFamily.kyFan_gauge] at h
      linarith [h.2]

/-! ### The real directed forms at the operator norm, naming the real angle

The two theorems above conclude about the canonical reflected overlap block.
Reading the real Ky-Fan-dominant statements at the first Ky Fan family and
renaming the block through `norm_sinTwoThetaBlock_real` gives the printed
operator-norm conclusions with `sin 2Θ` itself, over a real Hilbert space. -/

/-- **Davis--Kahan 1970, `sin 2Θ` theorem over a REAL Hilbert space, unbounded
bounded-perturbation form at the operator norm**: `δ ‖sin 2Θ‖ ≤ 2‖E‖`. -/
alias unbounded_sinTwoTheta_opNorm_real :=
  DavisKahan.Experimental.sinTwoTheta_addBounded_opNorm_real

/-- **Davis--Kahan 1970, `sin 2Θ` theorem over a REAL Hilbert space, unbounded
reflection-residual form at the operator norm**: `δ ‖sin 2Θ‖ ≤ ‖R‖`. -/
alias unbounded_sinTwoTheta_reflectionResidual_opNorm_real :=
  DavisKahan.Experimental.sinTwoTheta_reflectionResidual_opNorm_real

end DavisKahan1970
end TauCeti