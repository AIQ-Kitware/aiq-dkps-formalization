/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Halmos.TwoProjections
public import ForTauCeti.Analysis.InnerProductSpace.Polar.Perturbation
public import ForTauCeti.Analysis.InnerProductSpace.Positive.ModulusLowerBound

/-!
# Quantitative stability of the canonical transport under varying data

With the source fixed, changes in the canonical pre-polar intertwiner
have exactly the norm of the change in target projection. The sharp
cosine lower bound and the classical polar perturbation argument then
control changes in the actual canonical unitary, in arbitrary complex
Hilbert dimension and without compactness assumptions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Moving the target projection changes the canonical intertwiner by
exactly the same operator norm. -/
theorem norm_canonicalIntertwiner_sub_eq_projectionGap
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] :
    ‖spectraCanonicalIntertwiner K L - spectraCanonicalIntertwiner K M‖ = L.projectionGap M := by
  have hfactor : spectraCanonicalIntertwiner K L - spectraCanonicalIntertwiner K M =
      (L.starProjection - M.starProjection) * K.reflectionOperator := by
    calc
      _ = (spectraCanonicalIntertwiner K L - 1) -
          (spectraCanonicalIntertwiner K M - 1) := by abel
      _ = _ := by
        rw [spectraCanonicalIntertwiner_sub_one, spectraCanonicalIntertwiner_sub_one, ← sub_mul]
        congr 1
        abel
  rw [hfactor, Submodule.projectionGap_def]
  have href : K.reflectionOperator = (K.reflection : E →L[ℂ] E) := by
    apply ContinuousLinearMap.ext
    intro x
    exact Submodule.reflectionOperator_apply_eq_reflection K x
  rw [href]
  change ‖(L.starProjection - M.starProjection) * (K.reflection : E →L[ℂ] E)‖ = _
  exact ContinuousLinearMap.opNorm_mul_linearIsometryEquiv _ _

private theorem canonicalIntertwiner_energy (K L : Submodule ℂ E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (x : E) :
    ‖spectraCanonicalIntertwiner K L x‖ ^ 2 +
      ‖(K.starProjection - L.starProjection) x‖ ^ 2 = ‖x‖ ^ 2 := by
  let S := spectraCanonicalIntertwiner K L
  let D := K.starProjection - L.starProjection
  have hsq := spectraCanonicalAbsoluteValue_sq_eq_halmosCosineSq K L
  rw [halmosCosineSq_eq_one_sub_projection_sub_sq] at hsq
  have hgram : S.adjoint ∘L S = 1 - D * D := S.modulus_comp_modulus.symm.trans hsq
  have hS (y : E) : RCLike.re ⟪(S.adjoint ∘L S) y, y⟫_ℂ = ‖S y‖ ^ 2 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hD : D.IsSymmetric := K.starProjection_isSymmetric.sub L.starProjection_isSymmetric
  have hDinner : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
    have heq : ⟪D (D x), x⟫_ℂ = ⟪D x, D x⟫_ℂ := hD (D x) x
    rw [heq]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have h := congrArg (fun T : E →L[ℂ] E => RCLike.re ⟪T x, x⟫_ℂ) hgram
  rw [hS] at h
  change ‖S x‖ ^ 2 = RCLike.re ⟪x - D (D x), x⟫_ℂ at h
  rw [inner_sub_left, map_sub, ← norm_sq_eq_re_inner, hDinner] at h
  change ‖S x‖ ^ 2 + ‖D x‖ ^ 2 = _
  linarith

/-- A projection-gap budget gives the exact cosine coercivity bound
for the full canonical modulus, including fixed ambient directions. -/
theorem canonical_modulus_coercive_of_gap_sq_add_le_one
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (m : ℝ) (hm : 0 ≤ m) (hgap : m ^ 2 + K.projectionGap L ^ 2 ≤ 1) (x : E) :
    m * ‖x‖ ^ 2 ≤ RCLike.re ⟪(spectraCanonicalIntertwiner K L).modulus x, x⟫_ℂ := by
  apply ContinuousLinearMap.mul_norm_sq_le_re_inner_modulus_of_sq_mul_norm_sq_le _ m hm
  intro y
  have he := canonicalIntertwiner_energy K L y
  have hD : ‖(K.starProjection - L.starProjection) y‖ ≤ K.projectionGap L * ‖y‖ := by
    rw [Submodule.projectionGap_def]
    exact (K.starProjection - L.starProjection).le_opNorm y
  have hs := mul_self_le_mul_self (norm_nonneg _) hD
  have hbudget := mul_le_mul_of_nonneg_right hgap (sq_nonneg ‖y‖)
  nlinarith

/-- A two-endpoint cosine bound for the canonical unitary transport.
The source is fixed, while the two target projections are arbitrary.
There is no finite-rank, ideal-membership or separability assumption. -/
theorem add_mul_norm_canonicalPolarFactor_sub_le_two_mul_projectionGap
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hL : a ^ 2 + K.projectionGap L ^ 2 ≤ 1)
    (hM : b ^ 2 + K.projectionGap M ^ 2 ≤ 1) :
    (a + b) * ‖spectraCanonicalPolarFactor K L - spectraCanonicalPolarFactor K M‖ ≤
      2 * L.projectionGap M := by
  have hacuteL : IsUniformlyAcute K L := by
    change K.projectionGap L < 1
    nlinarith [sq_pos_of_pos ha, sq_nonneg (K.projectionGap L - 1)]
  have hacuteM : IsUniformlyAcute K M := by
    change K.projectionGap M < 1
    nlinarith [sq_pos_of_pos hb, sq_nonneg (K.projectionGap M - 1)]
  let U := Unitary.linearIsometryEquiv (spectraCanonicalPolarFactorUnitary K L hacuteL)
  let V := Unitary.linearIsometryEquiv (spectraCanonicalPolarFactorUnitary K M hacuteM)
  let X := spectraCanonicalIntertwiner K L
  let Y := spectraCanonicalIntertwiner K M
  have hX : X = (U : E →L[ℂ] E) * X.modulus :=
    (spectraCanonicalPolarFactor_decomposition K L).symm
  have hY : Y = (V : E →L[ℂ] E) * Y.modulus :=
    (spectraCanonicalPolarFactor_decomposition K M).symm
  have h := ContinuousLinearMap.add_mul_norm_sub_unitary_le_two_mul_norm_sub X Y
    X.modulus Y.modulus U V hX hY X.isPositive_modulus.isSelfAdjoint Y.isPositive_modulus.isSelfAdjoint
    a b (canonical_modulus_coercive_of_gap_sq_add_le_one K L a ha.le hL)
      (canonical_modulus_coercive_of_gap_sq_add_le_one K M b hb.le hM)
  change (a + b) * ‖spectraCanonicalPolarFactor K L - spectraCanonicalPolarFactor K M‖ ≤
    2 * ‖spectraCanonicalIntertwiner K L - spectraCanonicalIntertwiner K M‖ at h
  rwa [norm_canonicalIntertwiner_sub_eq_projectionGap] at h

/-- Uniform Lipschitz bound on a closed projection-gap ball of radius
less than one. It remains valid at any interior Schatten critical cutoff. -/
theorem norm_canonicalPolarFactor_sub_le_of_projectionGap_le
    (K L M : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (gamma : ℝ) (hgamma : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hL : K.projectionGap L ≤ gamma) (hM : K.projectionGap M ≤ gamma) :
    ‖spectraCanonicalPolarFactor K L - spectraCanonicalPolarFactor K M‖ ≤
      L.projectionGap M / Real.sqrt (1 - gamma ^ 2) := by
  have hpos : 0 < 1 - gamma ^ 2 := by nlinarith
  have hcos : 0 < Real.sqrt (1 - gamma ^ 2) := Real.sqrt_pos.mpr hpos
  have hL0 : 0 ≤ K.projectionGap L := by rw [Submodule.projectionGap_def]; positivity
  have hM0 : 0 ≤ K.projectionGap M := by rw [Submodule.projectionGap_def]; positivity
  have hLsq := mul_self_le_mul_self hL0 hL
  have hMsq := mul_self_le_mul_self hM0 hM
  have h := add_mul_norm_canonicalPolarFactor_sub_le_two_mul_projectionGap K L M _ _ hcos hcos
    (by nlinarith [Real.sq_sqrt hpos.le] : Real.sqrt (1 - gamma ^ 2) ^ 2 + K.projectionGap L ^ 2 ≤ 1)
    (by nlinarith [Real.sq_sqrt hpos.le] : Real.sqrt (1 - gamma ^ 2) ^ 2 + K.projectionGap M ^ 2 ≤ 1)
  apply (le_div_iff₀ hcos).mpr
  nlinarith

end TauCeti.DavisKahan
