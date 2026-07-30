/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Forms

/-!
# Compact operators, Schatten consequences, and singular subspaces

Literature writeup: local TeX, Sections 32--34.  This module connects the
Hilbert-space theory to compact covariance operators and Wedin-type singular
subspace perturbation through Hermitian dilation.
-/


/-! ## Construction plan

* Define `compactSpectralSubspace` from the finite-multiplicity eigenspaces of a
  compact self-adjoint operator, or as the range of a spectral projection away
  from zero.  Prove finite dimensionality before importing finite results.
* Construct `hermitianDilation A` on the Hilbert direct sum by the block matrix
  `[[0,A⋆],[A,0]]`; prove self-adjointness by block inner-product calculation.
* Identify its nonzero spectral subspaces with paired left/right singular
  subspaces, then specialize the self-adjoint Davis--Kahan theorem.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Compact self-adjoint spectral block. -/
noncomputable def compactSpectralSubspace (A : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E :=
  spectralSubspace A s

/-- Compact perturbations produce compact differences of isolated spectral
projections. 

Lean proof route for a weaker agent:

1. Apply the two mixed-gap `sinTheta_symmetric` argument at the operator level.
2. Express the projector difference as the image of `B-A` under the inverse Sylvester map on the off-diagonal blocks.
3. Use the compact ideal property and closure under sums/adjoints to prove compactness of both blocks and hence of the full difference.


Ext-agent signature audit (GPT 5.6 High): Correct with two mixed separations and
measurable sets. General separated spectra suffice for ideal membership even when the
sharp constant-one norm estimate is unavailable.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem compact_projection_difference
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {d : ℝ} (hd : 0 < d)
    (hsepAB : SpectraSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ d)
    (hsepBA : SpectraSeparated B (spectralSubspace B t)
      A (spectralSubspace A s)ᗮ d)
    (hcompact : (SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)).mem (B - A)) :
    (SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)).mem
      (spectralProjection A s - spectralProjection B t) := by
  let I := SymmetricNormIdeal.compactOperator (𝕜 := 𝕜) (E := E)
  let P := spectralProjection A s
  let Q := spectralProjection B t
  let X := (1 - Q) ∘L P
  let Y := (1 - P) ∘L Q
  have hXeq : sylvesterOperator
      (B.restrictTo (spectralSubspace B t)ᗮ)
      (A.restrictTo (spectralSubspace A s)) X =
      (1-Q) ∘L (B-A) ∘L P :=
    mixedProjection_sylvesterEquation hA hB hs ht
  have hYeq : sylvesterOperator
      (A.restrictTo (spectralSubspace A s)ᗮ)
      (B.restrictTo (spectralSubspace B t)) Y =
      (1-P) ∘L (A-B) ∘L Q :=
    mixedProjection_sylvesterEquation hB hA ht hs
  have hCX : I.mem ((1-Q) ∘L (B-A) ∘L P) :=
    I.ideal_mem (1-Q) P hcompact
  have hCY : I.mem ((1-P) ∘L (A-B) ∘L Q) := by
    have hneg : I.mem (A-B) := by
      simpa [sub_eq_neg_sub] using I.smul_mem (-1 : 𝕜) hcompact
    exact I.ideal_mem (1-P) Q hneg
  have hXcompact : I.mem X := by
    -- The separated Sylvester inverse is a Bochner integral of unitary
    -- conjugates.  Compact operators are stable under the integrand and closed
    -- in operator norm, hence its value is compact.
    exact compact_mem_of_separatedSylvester_solution
      I hA hB hd hsepAB hXeq hCX
  have hYcompact : I.mem Y :=
    compact_mem_of_separatedSylvester_solution
      I hB hA hd hsepBA hYeq hCY
  have hblock : P - Q = P ∘L (1-Q) - (1-P) ∘L Q := by
    module
  rw [hblock]
  have hPX : I.mem (P ∘L (1-Q)) := by
    have : I.mem X.adjoint := I.adjoint_mem hXcompact
    simpa [X, ContinuousLinearMap.adjoint_comp, hA, hB] using this
  have hYneg : I.mem (-Y) := by simpa using I.smul_mem (-1 : 𝕜) hYcompact
  exact I.add_mem hPX hYneg

/-- Schatten-class perturbation implies Schatten-class angle operator. 

Lean proof route for a weaker agent:

1. Instantiate `ideal_sinTheta` with the Schatten ideal at `p` and `hp`.
2. Supply `hmem` and the two mixed interval/exterior gaps.
3. Extract the membership and numerical components; normalize the factor `d` to the displayed form.


Ext-agent signature audit (GPT 5.6 High): Correct only if `ideal_sinTheta` establishes
the full ambient sine operator with matched adjoint-block multiplicity. Keep `1≤p`;
values below one are quasi-norms.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem schatten_sinTheta
    (p : ℝ) (hp : 1 ≤ p) {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hUV : IntervalExteriorSeparated A U B Vᗮ left right d)
    (hVU : IntervalExteriorSeparated B V A Uᗮ left' right' d)
    (hmem : (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).mem (B - A)) :
    (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).mem
        (sinAngleOperator U V) ∧
      d * (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).gauge
        (sinAngleOperator U V) ≤
      (SymmetricNormIdeal.schatten (𝕜 := 𝕜) (E := E) p hp).gauge (B - A) :=
  ideal_sinTheta (SymmetricNormIdeal.schatten p hp) hA hB hU hV hd hUV hVU hmem

/-- Hermitian dilation `(x, y) ↦ (T⋆ y, T x)` of a rectangular bounded
operator on the Hilbert direct sum. -/
noncomputable def hermitianDilation (T : E →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm :
      (E × F) →L[𝕜] WithLp 2 (E × F)) ∘L
    ((ContinuousLinearMap.adjoint T ∘L WithLp.sndL 2 𝕜 E F).prod
      (T ∘L WithLp.fstL 2 𝕜 E F))

/-- The Hermitian dilation is self-adjoint. 

Lean proof route for a weaker agent:

1. Expand the `2×2` block definition of `hermitianDilation`.
2. Compute the inner product of `D(T)(x,y)` with `(x',y')`.
3. Move `T` across the inner product using its continuous adjoint and rearrange terms.
4. Finish by extensionality of the product inner product.


Ext-agent signature audit (GPT 5.6 High): Correct. The definition must use the Hilbert
`L²` direct sum and place `T*` and `T` in the proper blocks.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem hermitianDilation_selfAdjoint (T : E →L[𝕜] F) :
    IsSelfAdjointOperator (hermitianDilation T) := by
  intro x y
  simp only [hermitianDilation, WithLp.prod_inner_apply]
  simp [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, add_comm]

/-- Hermitian-dilation spectral-projection bound underlying Wedin's theorem.

This is intentionally named as an intermediate result: separate left and right
singular-subspace definitions and their projection correspondences are still needed
before exposing a theorem called `wedin_singularSubspace`.

Proof strategy: construct the Hermitian dilation
`D(T) = [[0,T*],[T,0]]`, prove it is self-adjoint, and identify its positive and
negative spectral subspaces with the left/right singular subspaces of `T`.
Observe `D(T)-D(S)=D(T-S)` and prove `‖D(T-S)‖=‖T-S‖`.  Apply the self-adjoint
`sin Theta` theorem to the isolated spectral sets and project the resulting
block estimate back to the desired left or right singular subspace. 

Lean proof route for a weaker agent:

1. Prove the Hermitian dilations are self-adjoint and their difference is the dilation of `T-S`.
2. Apply the general separated spectral-projection `sinTheta` theorem in both directions, retaining the `π/2` constant.
3. Prove `‖hermitianDilation (T-S)‖=‖T-S‖` if a rectangular statement is desired.
4. Project the dilation subspace estimate to left/right singular subspaces in later corollaries.


Ext-agent signature audit (GPT 5.6 High): This is presently a Hermitian-dilation
spectral-projection theorem, not yet a left/right singular-subspace theorem. Its arbitrary
separated-set hypotheses require the generic `π/2` constant; ordered singular clusters can
support a later constant-one Wedin specialization.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem hermitianDilation_spectralProjection_sinTheta
    {S T : E →L[𝕜] F} (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    {d : ℝ} (hd : 0 < d)
    (hsepST : SpectraSeparated (hermitianDilation S)
      (spectralSubspace (hermitianDilation S) s)
      (hermitianDilation T)
      (spectralSubspace (hermitianDilation T) t)ᗮ d)
    (hsepTS : SpectraSeparated (hermitianDilation T)
      (spectralSubspace (hermitianDilation T) t)
      (hermitianDilation S)
      (spectralSubspace (hermitianDilation S) s)ᗮ d) :
    d * ‖spectralProjection (hermitianDilation S) s -
      spectralProjection (hermitianDilation T) t‖ ≤
      (Real.pi / 2) * ‖hermitianDilation (T - S)‖ := by
  let A := hermitianDilation S
  let B := hermitianDilation T
  let P := spectralProjection A s
  let Q := spectralProjection B t
  have hA := hermitianDilation_selfAdjoint S
  have hB := hermitianDilation_selfAdjoint T
  have hredP := reduces_spectralSubspace A hA s hs
  have hredQ := reduces_spectralSubspace B hB t ht
  have hforward := sinTheta_generalSeparation hA hB hredP hredQ hd
    (HybridGap.general hsepST)
  have hbackward := sinTheta_generalSeparation hB hA hredQ hredP hd
    (HybridGap.general hsepTS)
  have hgap : ‖P-Q‖ = max (directedGap (spectralSubspace A s)
      (spectralSubspace B t))
      (directedGap (spectralSubspace B t) (spectralSubspace A s)) :=
    Submodule.norm_starProjection_sub_eq_max _ _
  rw [hgap]
  have hdiff : B-A = hermitianDilation (T-S) := by
    rw [hermitianDilation_sub]
  rw [hdiff] at hforward hbackward
  exact max_scaled_le hforward hbackward (Real.pi_div_two_nonneg)

/-- Covariance-operator principal-subspace perturbation. 

Lean proof route for a weaker agent:

1. Instantiate `spectralProjection_sinTheta` with the two supplied interval/exterior gaps.
2. Rewrite the abstract spectral subspaces and projections to the covariance-operator notation.
3. Finish by ring normalization of the factor `d`.


Ext-agent signature audit (GPT 5.6 High): Correct as a thin specialization of the
canonical spectral-projection theorem; covariance positivity is not needed for the
abstract estimate.

Preferred dependency route: Specialize the bounded ideal and spectral-projection core;
use Hermitian dilation only after proving its exact norm and spectral-subspace
correspondences.
-/
theorem covariance_subspace_sinTheta
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    {left right left' right' d : ℝ} (hd : 0 < d)
    (hsepAB : IntervalExteriorSeparated A (spectralSubspace A s)
      B (spectralSubspace B t)ᗮ left right d)
    (hsepBA : IntervalExteriorSeparated B (spectralSubspace B t)
      A (spectralSubspace A s)ᗮ left' right' d) :
    d * ‖spectralProjection A s - spectralProjection B t‖ ≤ ‖B - A‖ := by
  obtain ⟨hAs, hBt⟩ := id hsepAB
  obtain ⟨hBs, hAt⟩ := id hsepBA
  exact spectralProjection_sinTheta hA hB s t hs ht hd hAs hBt hBs hAt

end DavisKahanExt
end TauCeti