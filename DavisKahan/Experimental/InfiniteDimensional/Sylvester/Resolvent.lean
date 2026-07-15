/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection

/-!
# Resolvents, Riesz projections, and spectral continuation

Literature writeup: local TeX, Sections 6, 11, and 20.  This module records the
analytic bridge from Banach-algebra resolvents to projection-valued spectral
subspaces and continuation under perturbation.
-/


/-! ## Construction plan

* Replace the total `resolventOperator` interface by mathlib's actual
  Banach-algebra resolvent, or by a bundled inverse parameterized by a proof of
  resolvent-set membership.  Prove inverse uniqueness once and use it in both
  resolvent identities.
* Package `ContourSeparatesSpectrum` with piecewise smoothness, closedness,
  resolvent membership along the path, and the winding-number conditions for
  selected and complementary spectral components.
* Define `rieszProjection` as the Bochner integral of the resolvent with the
  `1/(2*pi*i)` factor.  Prove idempotence by the first resolvent identity and
  Fubini, then prove agreement with the self-adjoint spectral projection by
  functional calculus.
-/


/-! ## Weak-agent execution plan: proof-carrying resolvents and Riesz projections

Refactor the total `resolventOperator` before proving identities.  The elegant
interface is either

`resolventOperator A z (hz : InResolventSet A z)`

or a bundled subtype containing an inverse and its two inverse laws.  If the
public total definition must remain temporarily, define it with an `if hz`
branch and prove an `_eq_of_mem` theorem; every analytic result must rewrite
through that theorem first.

Prove inverse uniqueness once.  Then both resolvent identities are ring
algebra with named inverse equations; use `ContinuousLinearMap.ext` and
`noncomm_ring` only after compositions are reassociated.

Do not define `ContourSeparatesSpectrum` as an opaque proposition.  Replace or
supplement it with a structure containing:

* a piecewise `C1` or rectifiable closed path;
* a proof every contour point is in the resolvent set;
* a uniform resolvent bound;
* winding number one on the selected spectrum and zero on the complement.

Define `rieszProjection` with the repository/mathlib contour-integral API and
include the normalization factor in the definition.  Prove continuity of the
integrand before forming the integral.  Establish agreement with the Borel
spectral projection by functional-calculus extensionality on the spectrum;
then obtain idempotence and self-adjointness from that equality rather than by
a first, difficult double-integral proof.

For continuation, first prove the local estimate from the second resolvent
identity, then pass it through the contour integral.  Keep the finite
continuation theorem separate: it may use a fixed finite contour and needs no
general PVM construction.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Resolvent-set predicate. -/
def InResolventSet (A : E →L[𝕜] E) (z : 𝕜) : Prop :=
  ∃ R : E →L[𝕜] E,
    R ∘L (A - z • ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E ∧
    (A - z • ContinuousLinearMap.id 𝕜 E) ∘L R = ContinuousLinearMap.id 𝕜 E

/-- Resolvent operator `(A - zI)⁻¹`, totalized by zero off the resolvent set. -/
noncomputable def resolventOperator (A : E →L[𝕜] E) (z : 𝕜) : E →L[𝕜] E := by
  classical
  exact if h : InResolventSet A z then Classical.choose h else 0

/-- The selected resolvent has both inverse laws. -/
theorem resolventOperator_spec (A : E →L[𝕜] E) {z : 𝕜}
    (hz : InResolventSet A z) :
    resolventOperator A z ∘L (A - z • ContinuousLinearMap.id 𝕜 E) =
        ContinuousLinearMap.id 𝕜 E ∧
      (A - z • ContinuousLinearMap.id 𝕜 E) ∘L resolventOperator A z =
        ContinuousLinearMap.id 𝕜 E := by
  classical
  unfold resolventOperator
  rw [dif_pos hz]
  exact Classical.choose_spec hz

/-- First resolvent identity. 

Lean proof route for a weaker agent:

1. Obtain the two inverse identities for `A-zI` and `A-wI` from `hz,hw`.
2. Expand `Rz-Rw = Rz((A-wI)-(A-zI))Rw`.
3. Simplify the middle difference to `(z-w)I` and reassociate compositions.


Ext-agent signature audit (GPT 5.6 High): The sign is correct for the convention
`(A-zI)⁻¹`. Ensure `resolventOperator` is chosen from `InResolventSet` and prove inverse
uniqueness once.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem resolvent_identity
    (A : E →L[𝕜] E) {z w : 𝕜}
    (hz : InResolventSet A z) (hw : InResolventSet A w) :
    resolventOperator A z - resolventOperator A w =
      (z - w) • (resolventOperator A z ∘L resolventOperator A w) := by
  classical
  let Rz := resolventOperator A z
  let Rw := resolventOperator A w
  have hzL := (resolventOperator_spec A hz).1
  have hzR := (resolventOperator_spec A hz).2
  have hwL := (resolventOperator_spec A hw).1
  have hwR := (resolventOperator_spec A hw).2
  calc
    Rz - Rw = Rz ∘L ((A - w • 1) - (A - z • 1)) ∘L Rw := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      simp [ContinuousLinearMap.comp_assoc, hzL, hzR, hwL, hwR]
    _ = Rz ∘L ((z-w) • 1) ∘L Rw := by congr 2 <;> module
    _ = (z-w) • (Rz ∘L Rw) := by module

/-- Second resolvent identity. 

Lean proof route for a weaker agent:

1. Use the algebraic inverse-difference formula `Y⁻¹-X⁻¹=Y⁻¹(X-Y)X⁻¹`.
2. Instantiate `X=A-zI` and `Y=B-zI` with the inverses supplied by `hA,hB`.
3. Simplify the scalar identity terms and reassociate compositions.


Ext-agent signature audit (GPT 5.6 High): The order and sign are correct: `R_B-R_A =
R_B(A-B)R_A` for the chosen resolvent convention.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem resolvent_perturbation_identity
    (A B : E →L[𝕜] E) {z : 𝕜}
    (hA : InResolventSet A z) (hB : InResolventSet B z) :
    resolventOperator B z - resolventOperator A z =
      resolventOperator B z ∘L (A - B) ∘L resolventOperator A z := by
  classical
  let RA := resolventOperator A z
  let RB := resolventOperator B z
  have hAL := (resolventOperator_spec A hA).1
  have hAR := (resolventOperator_spec A hA).2
  have hBL := (resolventOperator_spec B hB).1
  have hBR := (resolventOperator_spec B hB).2
  calc
    RB - RA = RB ∘L ((A - z • 1) - (B - z • 1)) ∘L RA := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      simp [ContinuousLinearMap.comp_assoc, hAL, hAR, hBL, hBR]
    _ = RB ∘L (A-B) ∘L RA := by congr 2 <;> module

/-- Self-adjoint resolvent norm bound by spectral distance. 

Lean proof route for a weaker agent:

1. Apply the self-adjoint continuous functional calculus to `f(lam)=1/(lam-z)`.
2. Use `hsep` to bound `|f(lam)|≤delta⁻¹` on the spectrum.
3. Identify the functional-calculus operator with `resolventOperator A z`.
4. Invoke the functional-calculus norm estimate and simplify using `hdelta`.


Ext-agent signature audit (GPT 5.6 High): Correct for self-adjoint `A`. `hsep` also
implies membership in the resolvent set, so the implementation must connect the total
roadmap resolvent to that unique inverse.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem norm_resolvent_le_inv_distance
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (z : 𝕜) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : 𝕜)‖) :
    ‖resolventOperator A z‖ ≤ delta⁻¹ := by
  classical
  have hz : InResolventSet A z :=
    selfAdjoint_inResolventSet_of_positive_distance hA hdelta hsep
  have heq : resolventOperator A z =
      RCLikeContinuousFunctionalCalculus.applyOnSpectrum
        (fun λ : ℝ => ((λ : 𝕜) - z)⁻¹) A hA :=
    resolvent_eq_functionalCalculus hA hz
  rw [heq]
  apply RCLikeContinuousFunctionalCalculus.norm_le
  intro λ hλ
  have h := hsep λ hλ
  simpa [norm_inv, norm_sub_rev] using inv_le_inv₀ hdelta h

/-- The contour lies in the resolvent set and encloses exactly the selected
spectral component, with the intended orientation/winding number. -/
noncomputable def ContourSeparatesSpectrum
    (A : E →L[𝕜] E) (s : Set ℝ) (contour : ℝ → 𝕜) : Prop := by
  classical
  exact
    Contour.IsClosed contour ∧
    Contour.Rectifiable contour ∧
    (∀ t, InResolventSet A (contour t)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖resolventOperator A (contour t)‖ ≤ M) ∧
    (∀ λ ∈ realSpectrum A, λ ∈ s → Contour.index contour (λ : 𝕜) = 1) ∧
    (∀ λ ∈ realSpectrum A, λ ∉ s → Contour.index contour (λ : 𝕜) = 0)

/-- Riesz projection associated with a separating contour. -/
noncomputable def rieszProjection (A : E →L[𝕜] E)
    (contour : ℝ → 𝕜) : E →L[𝕜] E := by
  classical
  exact ((2 : 𝕜) * (Real.pi : 𝕜) * RCLike.I)⁻¹ •
    Contour.integral contour (fun z => resolventOperator A z)

/-- Riesz and Borel spectral projections agree for self-adjoint operators and
separating contours. 

Lean proof route for a weaker agent:

1. Express both operators through the continuous/Borel functional calculus.
2. Use the holomorphic contour formula to show the contour integral equals the indicator of the enclosed spectral component on `realSpectrum A`.
3. Apply functional-calculus extensionality on the spectrum.
4. Use `hcontour` for winding number and resolvent-set obligations.


Ext-agent signature audit (GPT 5.6 High): The explicit measurability premise is
required by the Borel spectral calculus. `ContourSeparatesSpectrum` must additionally
encode a closed rectifiable contour, resolvent-set inclusion, orientation, and winding
numbers. With those contracts, the signature is sound.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem rieszProjection_eq_spectralProjection
    (A : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) (contour : ℝ → 𝕜)
    (hcontour : ContourSeparatesSpectrum A s contour) :
    rieszProjection A contour = spectralProjection A s := by
  classical
  apply boundedBorelFunctionalCalculus_ext hA
  intro λ hλ
  have hscalar := Contour.cauchyIndicatorFormula hcontour λ hλ
  simpa [rieszProjection, spectralProjection,
    resolvent_eq_functionalCalculus hA] using hscalar

/-- Neumann-series stability of the resolvent set. 

Lean proof route for a weaker agent:

1. Factor `A+H-zI = (I + H R_A(z))(A-zI)`.
2. Use the norm hypothesis to invert `I+H R_A(z)` by a Neumann series.
3. Write down the candidate two-sided inverse and verify both compositions by associativity.
4. Package it as an `InResolventSet` witness.


Ext-agent signature audit (GPT 5.6 High): Correct Neumann-series criterion. The product
order in the factorization must match the supplied norm bound, but either left or right
factorization gives the result.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem inResolventSet_add_of_norm_lt
    (A H : E →L[𝕜] E) {z : 𝕜}
    (hz : InResolventSet A z)
    (hsmall : ‖H‖ * ‖resolventOperator A z‖ < 1) :
    InResolventSet (A + H) z := by
  classical
  let R := resolventOperator A z
  have hcomp : ‖H ∘L R‖ < 1 := by
    calc
      ‖H ∘L R‖ ≤ ‖H‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < 1 := hsmall
  let U : (E →L[𝕜] E)ˣ := Units.oneSub (-(H ∘L R)) (by simpa [norm_neg] using hcomp)
  let S : E →L[𝕜] E := R ∘L (U⁻¹ : (E →L[𝕜] E)ˣ)
  refine ⟨S, ?_, ?_⟩
  · rw [show A+H-z•1 = (1+H∘L R) ∘L (A-z•1) by
      rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.one_comp,
        ContinuousLinearMap.comp_assoc, (resolventOperator_spec A hz).2]
      module]
    simp [S, U, ContinuousLinearMap.comp_assoc,
      (resolventOperator_spec A hz).1]
  · rw [show A+H-z•1 = (A-z•1) ∘L (1+R∘L H) by
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_one,
        ← ContinuousLinearMap.comp_assoc, (resolventOperator_spec A hz).2]
      module]
    exact inverse_factorization_right hz hcomp

/-- Norm continuity of Riesz projections along a uniformly separating path. 

Lean proof route for a weaker agent:

1. Prove local norm continuity of the resolvent with the second resolvent identity and a uniform contour bound.
2. Show the contour integrand is jointly continuous in path parameter and contour parameter.
3. Pass continuity through the Bochner contour integral using a uniform integrable domination.
4. Identify the integral with `rieszProjection`.


Ext-agent signature audit (GPT 5.6 High): Correct but deliberately global because both
hypothesis and conclusion quantify over all real `t`. The continuation module supplies
the more useful `[0,1]` specialization.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem continuous_rieszProjection_path
    (A H : E →L[𝕜] E) (s : Set ℝ) (contour : ℝ → 𝕜)
    (hsep : ∀ t : ℝ,
      ContourSeparatesSpectrum (A + (t : 𝕜) • H) s contour) :
    Continuous fun t : ℝ => rieszProjection (A + (t : 𝕜) • H) contour := by
  classical
  unfold rieszProjection
  apply Continuous.const_smul
  apply Contour.continuous_integral_parameter
  · intro t z
    exact (hsep t).2.1.continuous
  · intro t z ht hz
    have hresA := (hsep t).2.2.1 z
    have hresB := (hsep z).2.2.1 z
    rw [resolvent_perturbation_identity]
    exact norm_continuousLinearMap_comp_bound hresA hresB
  · obtain ⟨M, hM0, hM⟩ := (hsep 0).2.2.2.1
    exact ⟨M, contour_integrable_const M, fun t z => hM z⟩

end DavisKahanExt
end ForMathlib
