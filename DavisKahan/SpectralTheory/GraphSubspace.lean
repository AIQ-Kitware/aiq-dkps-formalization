/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import DavisKahan.SpectralTheory.OperatorAngle
public import ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import TauCeti.Analysis.InnerProductSpace.Projection.GraphSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

public section

open TauCeti.DavisKahan.Angle


/-!
# Graph subspaces and angular operators

Acute pairs admit a unique angular graph representation. The resulting operator
norm is the tangent of the maximal angle. We use TauCeti's graph, projection
formula, and exact projection gap.
-/

namespace TauCeti

open TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The ambient parametrization of a native graph first projects onto its base. -/
theorem graphSubspace_eq_range_starProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) :
    U.graphSubspace X =
      LinearMap.range (U.starProjection + X ∘L U.starProjection).toLinearMap := by
  ext y
  rw [Submodule.mem_graphSubspace, LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, ?_⟩
    change U.starProjection u + X (U.starProjection u) = u + X u
    rw [Submodule.starProjection_eq_self_iff.mpr hu]
  · rintro ⟨x, hx⟩
    exact ⟨U.starProjection x, U.starProjection_apply_mem x, hx⟩

/-- In a complete ambient space, the graph of an angular operator admits an
orthogonal projection. -/
theorem hasOrthogonalProjection_graphSubspace
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] {X : E →L[𝕜] E}
    (hX : U.IsAngularOperator X) : (U.graphSubspace X).HasOrthogonalProjection := by
  let : CompleteSpace U := U.completeSpace_coe_of_hasOrthogonalProjection
  let : CompleteSpace (U.graphSubspace X) := hX.completeSpace_graphSubspace
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace E] in
/-- The coordinate projection from an acute subspace onto the base is
injective.  The estimate is the elementary gap argument
`norm v <= norm(P_U-P_V) * norm v`. -/
private theorem acute_coordinate_injective
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    ∀ v, v ∈ V → U.starProjection v = 0 → v = 0 := by
  intro v hv hPv
  have hQv : V.starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  have hgap : ‖U.starProjection - V.starProjection‖ < 1 := by
    simpa only [IsUniformlyAcute, Submodule.projectionGap_def] using hacute
  have hpoint : ‖v‖ ≤ ‖U.starProjection - V.starProjection‖ * ‖v‖ := by
    have heq : (U.starProjection - V.starProjection) v = -v := by
      rw [sub_apply, hPv, hQv, zero_sub]
    calc ‖v‖ = ‖(U.starProjection - V.starProjection) v‖ := by rw [heq, norm_neg]
      _ ≤ ‖U.starProjection - V.starProjection‖ * ‖v‖ :=
        (U.starProjection - V.starProjection).le_opNorm v
  by_contra hv0
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  nlinarith

/-- Construct the angular graph operator from an acute pair by inverting the
near-identity compression `P_U P_V P_U + P_{U^perp}`. -/
private noncomputable def acuteAngularOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (_hacute : IsUniformlyAcute U V) : E →L[𝕜] E :=
  (1 - U.starProjection) * V.starProjection *
    Ring.inverse (U.starProjection * V.starProjection * U.starProjection + (1 - U.starProjection)) *
    U.starProjection

/-- Algebraic properties of the acute angular operator. -/
private theorem acuteAngularOperator_spec
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    U.IsAngularOperator (acuteAngularOperator U V hacute) ∧
      V = LinearMap.range
        (U.starProjection + acuteAngularOperator U V hacute ∘L U.starProjection).toLinearMap := by
  set P : E →L[𝕜] E := U.starProjection with hPdef
  set Q : E →L[𝕜] E := V.starProjection with hQdef
  have hPP : P * P = P := (U.isIdempotentElem_starProjection).eq
  set T : E →L[𝕜] E := P * Q * P + (1 - P) with hTdef
  set R : E →L[𝕜] E := Ring.inverse T with hRdef
  have hXdef : acuteAngularOperator U V hacute = (1 - P) * Q * R * P := rfl
  have hP1P : P * (1 - P) = 0 := by rw [mul_one_sub, hPP, sub_self]
  have h1PP : (1 - P) * P = 0 := by rw [one_sub_mul, hPP, sub_self]
  -- the compression is a unit: it is within distance `< 1` of the identity
  have hgap : ‖P - Q‖ < 1 := by
    simpa only [IsUniformlyAcute, Submodule.projectionGap_def, P, Q] using hacute
  have hPnorm : ‖P‖ ≤ 1 := U.starProjection_norm_le
  have hfact : P * (P - Q) * P = P - P * Q * P := by
    rw [mul_sub, sub_mul, hPP, hPP]
  have hnorm : ‖P - P * Q * P‖ < 1 := by
    rw [← hfact]
    have h1 : ‖P * (P - Q) * P‖ ≤ ‖P - Q‖ := by
      calc ‖P * (P - Q) * P‖ ≤ ‖P * (P - Q)‖ * ‖P‖ := norm_mul_le _ _
        _ ≤ ‖P‖ * ‖P - Q‖ * ‖P‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ 1 * ‖P - Q‖ * 1 := by
            have h1 : ‖P‖ * ‖P - Q‖ ≤ 1 * ‖P - Q‖ :=
              mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
            exact mul_le_mul h1 hPnorm (norm_nonneg _) (by positivity)
        _ = ‖P - Q‖ := by ring
    linarith
  have hone : T = 1 - (P - P * Q * P) := by rw [hTdef]; abel
  have hTunit : IsUnit T := by
    rw [hone]
    exact (Units.oneSub _ hnorm).isUnit
  have hTR : T * R = 1 := Ring.mul_inverse_cancel T hTunit
  have hRT : R * T = 1 := Ring.inverse_mul_cancel T hTunit
  -- `P` commutes with `T`, hence with `R`
  have hPPQP : P * (P * Q * P) = P * Q * P := by
    rw [← mul_assoc, ← mul_assoc, hPP]
  have hPQPP : P * Q * P * P = P * Q * P := by
    rw [mul_assoc, hPP]
  have hPT : P * T = T * P := by
    simp only [hTdef, mul_add, add_mul, hPPQP, hPQPP, hP1P, h1PP, add_zero]
  have hPR : P * R = R * P := by
    calc P * R = (R * T) * (P * R) := by rw [hRT, one_mul]
      _ = R * ((T * P) * R) := by rw [mul_assoc R T (P * R), ← mul_assoc T P R]
      _ = R * ((P * T) * R) := by rw [← hPT]
      _ = (R * P) * (T * R) := by rw [mul_assoc P T R, ← mul_assoc R P (T * R)]
      _ = R * P := by rw [hTR, mul_one]
  -- `R` is the identity on `Uᗮ`, and the compressed inverse satisfies `PQRP = P`
  have h1PT : (1 - P) * T = 1 - P := by
    have e1 : (1 - P) * (P * Q * P) = 0 := by
      rw [← mul_assoc, ← mul_assoc, h1PP, zero_mul, zero_mul]
    have e2 : (1 - P) * (1 - P) = 1 - P := by
      rw [mul_one_sub, h1PP, sub_zero]
    rw [hTdef, mul_add, e1, e2, zero_add]
  have h1PR : (1 - P) * R = 1 - P := by
    calc (1 - P) * R = ((1 - P) * T) * R := by rw [h1PT]
      _ = (1 - P) * (T * R) := by rw [mul_assoc]
      _ = 1 - P := by rw [hTR, mul_one]
  have hPQPR : P * Q * P * R = P := by
    have h := hTR
    rw [hTdef, add_mul, h1PR] at h
    have h2 : P * Q * P * R = 1 - (1 - P) := eq_sub_of_add_eq h
    rwa [sub_sub_cancel] at h2
  have hPQRP : P * Q * R * P = P := by
    calc P * Q * R * P = P * Q * (R * P) := by rw [mul_assoc]
      _ = P * Q * (P * R) := by rw [← hPR]
      _ = P * Q * P * R := by rw [← mul_assoc]
      _ = P := hPQPR
  -- angularity of the constructed operator
  have hXP : ((1 - P) * Q * R * P) * P = (1 - P) * Q * R * P := by
    rw [mul_assoc, hPP]
  have hPX : P * ((1 - P) * Q * R * P) = 0 := by
    simp only [← mul_assoc, hP1P, zero_mul]
  -- the parametrized graph map collapses to `Q R P`
  have hsum : P + (1 - P) * Q * R * P = Q * R * P := by
    rw [one_sub_mul, sub_mul, sub_mul, hPQRP]
    abel
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hXdef]
    exact hXP
  · rw [hXdef]
    exact hPX
  · have hop : P + acuteAngularOperator U V hacute ∘L P = Q * R * P := by
      have h1 : acuteAngularOperator U V hacute ∘L P = (1 - P) * Q * R * P := by
        rw [hXdef]
        exact hXP
      rw [h1]
      exact hsum
    rw [hop]
    refine le_antisymm ?_ ?_
    · intro v hv
      have hPv : P ((Q * R * P) v - v) = 0 := by
        have h : P (Q (R (P v))) = P v :=
          congrArg (fun S : E →L[𝕜] E => S v) hPQRP
        rw [map_sub]
        show P (Q (R (P v))) - P v = 0
        rw [h, sub_self]
      have hmem : (Q * R * P) v - v ∈ V := by
        refine V.sub_mem ?_ hv
        show Q (R (P v)) ∈ V
        exact V.starProjection_apply_mem _
      have hzero := acute_coordinate_injective U V hacute _ hmem hPv
      exact ⟨v, sub_eq_zero.mp hzero⟩
    · rintro x ⟨y, rfl⟩
      show Q (R (P y)) ∈ V
      exact V.starProjection_apply_mem _

/-- A pair is acute exactly when it is the graph of a bounded angular operator. -/
theorem acute_iff_exists_bounded_angularOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsUniformlyAcute U V ↔
      ∃ X : E →L[𝕜] E, U.IsAngularOperator X ∧
        V = LinearMap.range (U.starProjection + X ∘L U.starProjection).toLinearMap := by
  constructor
  · intro hacute
    obtain ⟨hang, hrange⟩ := acuteAngularOperator_spec U V hacute
    exact ⟨acuteAngularOperator U V hacute, hang, hrange⟩
  · rintro ⟨X, hXang, hV⟩
    have hgraph : U.graphSubspace X = V :=
      (graphSubspace_eq_range_starProjection U X).trans hV.symm
    have : (U.graphSubspace X).HasOrthogonalProjection :=
      hgraph.symm ▸ inferInstanceAs V.HasOrthogonalProjection
    change U.projectionGap V < 1
    simpa only [hgraph] using hXang.projectionGap_graphSubspace_lt_one

/-- Every acute subspace is the graph of a unique bounded angular operator. -/
theorem existsUnique_angularOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsUniformlyAcute U V) :
    ∃! X : E →L[𝕜] E,
      U.IsAngularOperator X ∧ U.graphSubspace X = V := by
  obtain ⟨X, hXang, hXrange⟩ :=
    (acute_iff_exists_bounded_angularOperator U V).mp hacute
  have hXgraph : U.graphSubspace X = V :=
    (graphSubspace_eq_range_starProjection U X).trans hXrange.symm
  refine ⟨X, ⟨hXang, hXgraph⟩, ?_⟩
  rintro Y ⟨hYang, hYgraph⟩
  ext x
  have hu : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hmem : U.starProjection x + Y (U.starProjection x) ∈ U.graphSubspace X := by
    rw [hXgraph, ← hYgraph]
    exact Submodule.add_apply_mem_graphSubspace hu
  have hcoord := hXang.mem_graphSubspace_iff.mp hmem
  rw [hYang.starProjection_orthogonal_add_apply hu, map_add,
    hXang.apply_eq_zero_of_mem_orthogonal (hYang.apply_mem_orthogonal _), add_zero,
    hYang.apply_starProjection, hXang.apply_starProjection] at hcoord
  exact hcoord

/-- Tangent of the maximal angle is the angular-operator norm.  The gap to
the graph is `‖X‖ / √(1 + ‖X‖ ^ 2)`, and `tan ∘ arcsin` recovers `‖X‖`. -/
theorem tan_maximalAngle_eq_norm_angularOperator
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : U.IsAngularOperator X) :
    have := hasOrthogonalProjection_graphSubspace hX
    Real.tan (maximalAngle U (U.graphSubspace X)) = ‖X‖ := by
  have := hasOrthogonalProjection_graphSubspace hX
  have hgap := hX.projectionGap_graphSubspace
  have hpos : (0 : ℝ) < 1 + ‖X‖ ^ 2 := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt (1 + ‖X‖ ^ 2) := Real.sqrt_pos.mpr hpos
  change Real.tan (Real.arcsin (U.projectionGap (U.graphSubspace X))) = ‖X‖
  rw [hgap, Real.tan_arcsin]
  have h2 : (‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2)) ^ 2 = ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) := by
    rw [div_pow, Real.sq_sqrt hpos.le]
  have h3 : 1 - ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) = 1 / (1 + ‖X‖ ^ 2) := by
    field_simp
    ring
  rw [h2, h3, one_div, Real.sqrt_inv]
  field_simp

/-- Contractive angular operators correspond to maximal angles below
`π / 4`. -/
theorem norm_angularOperator_lt_one_iff
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : U.IsAngularOperator X) :
    have := hasOrthogonalProjection_graphSubspace hX
    ‖X‖ < 1 ↔ maximalAngle U (U.graphSubspace X) < Real.pi / 4 := by
  have := hasOrthogonalProjection_graphSubspace hX
  have hgap := hX.projectionGap_graphSubspace
  have hpos : (0 : ℝ) < 1 + ‖X‖ ^ 2 := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt (1 + ‖X‖ ^ 2) := Real.sqrt_pos.mpr hpos
  change ‖X‖ < 1 ↔ Real.arcsin (U.projectionGap (U.graphSubspace X)) < Real.pi / 4
  rw [hgap]
  have hpi4 : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
    rw [← Real.sin_pi_div_four]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [← hpi4]
  have hg0 : (0 : ℝ) ≤ ‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2) := by positivity
  have hgsq : (‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2)) ^ 2 = ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) := by
    rw [div_pow, Real.sq_sqrt hpos.le]
  have hmem1 : ‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · linarith
    · rw [div_le_one hs0]
      have h := Real.sqrt_le_sqrt (show ‖X‖ ^ 2 ≤ 1 + ‖X‖ ^ 2 by linarith)
      rwa [Real.sqrt_sq (norm_nonneg X)] at h
  have hmem2 : Real.sqrt 2 / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    constructor
    · linarith
    · nlinarith
  rw [Real.strictMonoOn_arcsin.lt_iff_lt hmem1 hmem2]
  have hhalf : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs20 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  constructor
  · intro h
    have hsq : (‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2)) ^ 2 < (Real.sqrt 2 / 2) ^ 2 := by
      rw [hgsq, hhalf, div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [norm_nonneg X]
    nlinarith [hg0, hs20, hsq]
  · intro h
    have hsq : (‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2)) ^ 2 < (Real.sqrt 2 / 2) ^ 2 := by
      nlinarith [hg0, hs20, h]
    rw [hgsq, hhalf, div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)] at hsq
    nlinarith [norm_nonneg X]

end DavisKahanExt
end TauCeti
