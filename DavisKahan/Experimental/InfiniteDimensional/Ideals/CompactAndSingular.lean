/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Forms
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.General
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Symmetric

/-!
# Compact operators, Schatten consequences, and singular subspaces

Hermitian dilation turns a rectangular perturbation into a self-adjoint block
perturbation.  Its positive and negative spectral subspaces encode the paired
left/right singular subspaces.  Compact and Schatten consequences are obtained
by applying the corresponding symmetric ideal to the mixed Sylvester blocks.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Spectral subspace notation used for compact self-adjoint operators.  The
compactness and isolation hypotheses enter the finite-dimensionality theorem,
not the definition. -/
noncomputable def compactSpectralSubspace (A : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E :=
  spectralSubspace A s

/-- A compact self-adjoint spectral block away from zero is finite-dimensional. -/
theorem finiteDimensional_compactSpectralSubspace
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (hcompact : IsCompactOperator A) {s : Set ℝ}
    (hs : MeasurableSet s) (haway : 0 ∉ closure s) :
    FiniteDimensional 𝕜 (compactSpectralSubspace A s) := by
  have hfinite := compact_selfAdjoint_spectralProjection_finiteRank
    A hA hcompact s hs haway
  simpa [compactSpectralSubspace, spectralSubspace] using hfinite

/-- Compact perturbations produce compact differences of separated spectral
projections. -/
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

/-- Schatten-class perturbation implies a Schatten-class sine operator with
the sharp interval/exterior constant. -/
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
  ideal_sinTheta (SymmetricNormIdeal.schatten p hp)
    hA hB hU hV hd hUV hVU hmem

/-- Hermitian dilation `[[0,T*],[T,0]]`. -/
noncomputable def hermitianDilation (T : E →L[𝕜] F) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  blockContinuousLinearMap
    (0 : E →L[𝕜] E) T.adjoint T (0 : F →L[𝕜] F)

/-- Pointwise block formula for the Hermitian dilation. -/
theorem hermitianDilation_apply (T : E →L[𝕜] F)
    (x : WithLp 2 (E × F)) :
    WithLp.linearEquiv 2 𝕜 (E × F) (hermitianDilation T x) =
      (T.adjoint (WithLp.linearEquiv 2 𝕜 (E × F) x).2,
       T (WithLp.linearEquiv 2 𝕜 (E × F) x).1) := by
  rfl

/-- The Hermitian dilation is self-adjoint. -/
theorem hermitianDilation_selfAdjoint (T : E →L[𝕜] F) :
    IsSelfAdjointOperator (hermitianDilation T) := by
  intro x y
  rcases WithLp.linearEquiv 2 𝕜 (E × F) x with ⟨x0,x1⟩
  rcases WithLp.linearEquiv 2 𝕜 (E × F) y with ⟨y0,y1⟩
  simp [hermitianDilation, blockContinuousLinearMap,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, add_comm, add_left_comm]

/-- Dilation is linear. -/
theorem hermitianDilation_sub (T S : E →L[𝕜] F) :
    hermitianDilation (T-S) = hermitianDilation T - hermitianDilation S := by
  ext x
  simp [hermitianDilation, blockContinuousLinearMap]

/-- Hermitian dilation preserves operator norm. -/
theorem norm_hermitianDilation (T : E →L[𝕜] F) :
    ‖hermitianDilation T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    rw [WithLp.norm_sq_eq, hermitianDilation_apply]
    have h0 := T.le_opNorm (WithLp.linearEquiv 2 𝕜 (E × F) x).1
    have h1 := T.adjoint.le_opNorm (WithLp.linearEquiv 2 𝕜 (E × F) x).2
    rw [ContinuousLinearMap.norm_adjoint] at h1
    nlinarith [sq_nonneg ‖T‖]
  · let ι : E →L[𝕜] WithLp 2 (E × F) := firstCoordinateIsometry
    let π : WithLp 2 (E × F) →L[𝕜] F := secondCoordinateProjection
    have hfactor : T = π ∘L hermitianDilation T ∘L ι := by
      ext x
      simp [π, ι, hermitianDilation, blockContinuousLinearMap]
    rw [hfactor]
    calc
      ‖π ∘L hermitianDilation T ∘L ι‖
          ≤ ‖π‖ * ‖hermitianDilation T‖ * ‖ι‖ :=
        ContinuousLinearMap.opNorm_comp_comp_le _ _ _
      _ = ‖hermitianDilation T‖ := by
        rw [secondCoordinateProjection_norm, firstCoordinateIsometry_norm,
          one_mul, mul_one]

/-- Hermitian-dilation spectral-projection estimate underlying Wedin's theorem. -/
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

/-- Covariance-operator principal-subspace perturbation. -/
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
  exact spectralProjection_sinTheta hA hB s t hs ht hd
    hsepAB.interval hsepAB.exterior hsepBA.interval hsepBA.exterior

end DavisKahanExt
end ForMathlib
