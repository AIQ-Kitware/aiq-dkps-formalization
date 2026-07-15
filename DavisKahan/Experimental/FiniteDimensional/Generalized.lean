/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.SinTheta.TrialMap
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.TanTheta
import DavisKahan.Experimental.FiniteDimensional.TanTheta.GraphOperator

/-!
# Compatibility surface for unfinished generalized extensions

The completed generalized sine theorem moved to
`DavisKahan.FiniteDimensional.SinTheta.TrialMap`.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators Topology
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Davis--Kahan Theorem 6.2: under arbitrary spectral separation the sharp
all-UI conclusion is replaced by the Hilbert--Schmidt/square-norm estimate.

Lean proof route for a weaker agent:

1. Set `Q := orthonormalizedEmbedding X hX` and rewrite its range using `range_orthonormalizedEmbedding`.
2. Derive the rectangular Sylvester equation for `sinThetaEmbedding U Q` and apply the Frobenius separated-spectrum estimate entrywise.
3. Factor the whitened residual through the Gram inverse square root, use `hframe` to control that factor, and clear `ε` with `hε`.
-/
theorem generalizedSinTheta_frobenius_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectraSeparated M ⊤ A Vᗮ δ) :
    δ * ε * RectangularUnitarilyInvariantNorm.frobenius
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      RectangularUnitarilyInvariantNorm.frobenius
        (generalResidual A X M) := by
  sorry

/-- Trace/nuclear fallback obtained from the square-norm estimate and rank.

Lean proof route for a weaker agent:

1. Apply `generalizedSinTheta_frobenius_le_of_spectralDistance` to obtain the Hilbert--Schmidt bound.
2. Use the finite singular-value inequality `nuclear ≤ sqrt(rank) * frobenius` for the rectangular sine map.
3. Bound its rank by `finrank 𝕜 F`, preserve all nonnegativity side conditions, and simplify the scalar factors.
-/
theorem generalizedSinTheta_nuclear_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectraSeparated M ⊤ A Vᗮ δ) :
    δ * ε * RectangularUnitarilyInvariantNorm.nuclear
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      Real.sqrt (finrank 𝕜 F) *
        RectangularUnitarilyInvariantNorm.frobenius
          (generalResidual A X M) := by
  sorry

/-- Davis--Kahan Theorem 6.3: generalized `tan Θ`, allowing the exact target
subspace to have larger dimension than the trial space.

Signature audit: The theorem now uses the symmetric whitened compression and its matching
whitened residual.  The previous statement mixed whitened coordinates with the unwhitened
trial map.
-/
theorem generalizedTanTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    (_hdim : finrank 𝕜 F ≤ finrank 𝕜 V)
    (_htrans : IsTransverse
      (approximateSubspace (orthonormalizedEmbedding X hX)) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap (generalizedCompression A X hX) ⊤ A Vᗮ δ) :
    δ * N (tanThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (residual A (orthonormalizedEmbedding X hX)
        (generalizedCompression A X hX)) :=
  tanTheta_residual_le N hA hV (orthonormalizedEmbedding X hX)
    (isSymmetric_generalizedCompression hA X hX) rfl hδ hgap

/-- The unequal-dimensional `sin 2Θ` extension mentioned after Theorem 8.2.
-/
theorem generalizedSinTwoTheta_unequalFinrank
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) :=
  sinTwoTheta_residual_le N hA hU X hM hδ hgap

/-- Spectral projectors along the homotopy `A+tH` stay on one isolated branch.

Lean proof route for a weaker agent:

1. Use `hselected` and `houtside` to obtain one fixed interval/exterior contour with clearance
   `δ` for every `t ∈ [0,1]`.
2. Specialize the experimental continuation/Riesz-projection module to the path
   `t ↦ A + t • H` and this fixed contour.
3. Identify the finite Riesz projection with `spectralProjection` by diagonalizing each
   symmetric operator.
4. Transfer continuity through the linear-map/continuous-linear-map coercion.

Signature audit: The fixed interval and uniform exterior buffer prevent eigenvalues from
crossing the selection boundary; the former hypothesis was tautological.
-/
theorem spectralSubspace_path_continuous
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hselected : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) (Set.Icc a b))
        (Set.Icc a b))
    (houtside : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) (Set.Icc a b))ᗮ
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    ContinuousOn (fun t : ℝ =>
      (spectralProjection (A + (t : 𝕜) • H) (Set.Icc a b)).toContinuousLinearMap)
      (Set.Icc 0 1) := by
  sorry

/-- Davis--Kahan Theorem 8.2: a quantitative half-gap bound selects the acute
branch of the `sin 2Θ` conclusion.

Lean proof route for a weaker agent:

1. Use the strengthened continuation theorem to keep the selected projector in the component of `U`, combine the half-gap perturbation bound with `‖P-Q‖ < 1`, and conclude `IsAcute`.
2. This should directly specialize the experimental bounded continuation layer.
-/
theorem sinTwoTheta_acute_of_small_perturbation
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hUcentral : SpectrumIn A U (Set.Icc (a - δ / 2) (b + δ / 2)))
    (hUoutside : SpectrumIn A Uᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)})
    (hsmall : ‖H.toContinuousLinearMap‖ < δ / 2) :
    IsAcute U (spectralSubspace (A + H) (Set.Icc (a - δ / 2) (b + δ / 2))) := by
  sorry

end DavisKahanTheory
end ForMathlib
