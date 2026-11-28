/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T06.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`PrincipalAngles.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

The canonical principal-angle API: the cosines of the principal angles between
two subspaces (given by orthonormal families) are the singular values of the
accepted overlap operator `TauCeti.overlapOperator`.  This packages the
`cos Θ`/`sin Θ` vectors, their basic order/range properties, the symmetry in the
two families (which needs `singularValues_adjoint`, W0.1(d)), and the bridge
`‖sin Θ‖²_F = d − overlap` to the flat overlap sum.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AlignedBasis
public import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import ForTauCeti.Analysis.InnerProductSpace.KyFan


/-! # Principal-angle consequences on the accepted overlap API

Coordinate synthesis, overlap operators, principal cosines, their basic bounds
and squared Frobenius sine are supplied by TauCeti's `Orthonormal.Overlap`.
The former local definitions and duplicate basic proofs are retired.

The eigenblock squared-sine formula uses TauCeti's coordinate-subtype API.
This module retains the selected-polar alignment consequence and the
largest-angle norm identification. Paper callers obtain the cosine
dictionary from `Orthonormal.principalCosines_eq_cosPrincipalAngles`.

Historical donor source is preserved at
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/PrincipalAngles.lean`;
original authorship, Kitware copyright and Apache-2.0 attribution remain above.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {d : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- **Aligned-basis bound in principal-angle form.**  The Yu–Wang–Samworth
Procrustes-rotated basis `wⱼ = (hv.synthesisMapIsometry)(O⁻¹ eⱼ)` obeys
`∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`. -/
theorem sum_sq_norm_aligned_le_sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ j, ‖hv.synthesisMapIsometry ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm
          (EuclideanSpace.single j 1)) - u j‖ ^ 2
      ≤ 2 * sinThetaSq hu hv := by
  rw [sinThetaSq_eq_card_sub_sum_norm_inner_sq, Fintype.card_fin]
  exact sum_sq_norm_aligned_le hu hv

/-! ### The operator-norm identification `‖Q̂ ∘L P‖ = sin θ_max`

The operator norm of "project onto `U`, then onto `Wᗮ`" is exactly the sine of
the largest principal angle between `U` and `W`.  This certifies that the
operator-norm Davis–Kahan theorem (`SinThetaOpNorm.lean`) bounds a principal
angle. -/

private theorem norm_sq_euclidean (z : EuclideanSpace 𝕜 (Fin d)) :
    ‖z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- **The key Pythagoras computation**: for `x = ι_u y ∈ U = span u`,
`‖P_{Wᗮ} x‖² = ‖y‖² − ‖(overlapOperator 𝕜 w u) y‖²`. -/
private theorem norm_sq_orthogonal_starProjection_familyIsometry
    {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w)
    (y : EuclideanSpace 𝕜 (Fin d)) :
    ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (hu.synthesisMapIsometry y)‖ ^ 2
      = ‖y‖ ^ 2 - ‖overlapOperator 𝕜 w u y‖ ^ 2 := by
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (hu.synthesisMapIsometry y)
    (Submodule.span 𝕜 (Set.range w))
  have hWproj : ‖(Submodule.span 𝕜 (Set.range w)).starProjection (hu.synthesisMapIsometry y)‖ ^ 2
      = ‖overlapOperator 𝕜 w u y‖ ^ 2 := by
    rw [hw.norm_starProjection_sq_eq_sum rfl, norm_sq_euclidean]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [overlapOperator_def, LinearMap.comp_apply, analysisMap_apply,
      ← hu.synthesisMapIsometry_toLinearMap, LinearIsometry.coe_toLinearMap]
  have hiso : ‖hu.synthesisMapIsometry y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [(hu.synthesisMapIsometry).norm_map]
  linarith

/-- **Operator-norm principal-angle identification.**  For orthonormal families
`u, w : Fin d → E` spanning `U` and `W`, the operator norm of
`P_{Wᗮ} ∘L P_U` equals the sine of the largest principal angle between `U` and
`W`:

`‖P_{Wᗮ} ∘L P_U‖ = √(1 − cos²θ_max)`,

`cos θ_max` being the smallest principal-angle cosine
`cosPrincipalAngles hw hu (d − 1)`.  This certifies that the operator-norm
Davis–Kahan theorem (`norm_starProjection_comp_starProjection_le`) bounds
`sin θ_max`. -/
theorem norm_orthogonal_starProjection_comp_starProjection
    {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w) (hd : 0 < d) :
    ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection‖
      = Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) := by
  have hσ0 : 0 ≤ cosPrincipalAngles hw hu (d - 1) := cosPrincipalAngles_nonneg hw hu _
  have hσ1 : cosPrincipalAngles hw hu (d - 1) ≤ 1 := by
    have := cosPrincipalAngles_le_one hw hu (⟨d - 1, by omega⟩ : Fin d)
    simpa using this
  have h1σ : 0 ≤ 1 - cosPrincipalAngles hw hu (d - 1) ^ 2 := by nlinarith
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun z => ?_) ?_
  · -- upper bound: pull the projected vector back to coordinates via the
    -- adjoint of the coordinate isometry.
    set y : EuclideanSpace 𝕜 (Fin d) :=
      (hu.synthesisMapIsometry).toLinearMap.adjoint
        ((Submodule.span 𝕜 (Set.range u)).starProjection z) with hy
    have hcoord : ∀ i, y i
        = ⟪u i, (Submodule.span 𝕜 (Set.range u)).starProjection z⟫_𝕜 := fun i => by
      rw [hy, hu.synthesisMapIsometry_toLinearMap, adjoint_synthesisMap, analysisMap_apply]
    have hxy : hu.synthesisMapIsometry y
        = (Submodule.span 𝕜 (Set.range u)).starProjection z := by
      have hsum : hu.synthesisMapIsometry y
          = ∑ i, ⟪u i, (Submodule.span 𝕜 (Set.range u)).starProjection z⟫_𝕜 • u i := by
        rw [Orthonormal.synthesisMapIsometry_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [hcoord]
      rw [hsum, ← hu.starProjection_apply_eq_sum rfl]
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ z)
    have hyz : ‖y‖ ≤ ‖z‖ := by
      have h1 : ‖y‖ = ‖(Submodule.span 𝕜 (Set.range u)).starProjection z‖ := by
        rw [← hxy, (hu.synthesisMapIsometry).norm_map]
      rw [h1]
      exact Submodule.norm_starProjection_apply_le _ z
    have hmin : cosPrincipalAngles hw hu (d - 1) * ‖y‖ ≤ ‖overlapOperator 𝕜 w u y‖ := by
      rw [cosPrincipalAngles_def]
      apply (overlapOperator 𝕜 w u).singularValues_mul_norm_le_norm_apply
      rw [OrthonormalBasis.mem_spanIndices_iff]
      intro i hi
      have hi' : (i : ℕ) < d := by
        simpa only [finrank_euclideanSpace_fin] using i.isLt
      exact (hi (show (i : ℕ) ≤ d - 1 from by omega)).elim
    have h2 : ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection
          ((Submodule.span 𝕜 (Set.range u)).starProjection z)‖ ^ 2
        ≤ (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ ^ 2 := by
      rw [← hxy, norm_sq_orthogonal_starProjection_familyIsometry hu hw y]
      have p1 : cosPrincipalAngles hw hu (d - 1) ^ 2 * ‖y‖ ^ 2
          ≤ ‖overlapOperator 𝕜 w u y‖ ^ 2 := by
        have h := mul_self_le_mul_self (mul_nonneg hσ0 (norm_nonneg y)) hmin
        nlinarith [h]
      have hyz2 : ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        have h := mul_self_le_mul_self (norm_nonneg y) hyz
        nlinarith [h]
      linarith [mul_le_mul_of_nonneg_left hyz2 h1σ, p1]
    calc ‖((Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection) z‖
        = ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection
            ((Submodule.span 𝕜 (Set.range u)).starProjection z)‖ := rfl
      _ ≤ Real.sqrt ((1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ ^ 2) := by
          rw [← Real.sqrt_sq (norm_nonneg _)]
          exact Real.sqrt_le_sqrt h2
      _ = Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ := by
          rw [Real.sqrt_mul h1σ, Real.sqrt_sq (norm_nonneg z)]
  · -- lower bound: the minimizing singular vector attains the angle.
    let i₀ : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin d))) :=
      ⟨d - 1, by rw [finrank_euclideanSpace_fin]; omega⟩
    let y₀ := (overlapOperator 𝕜 w u).rightSingularBasis i₀
    have hy₀n : ‖y₀‖ = 1 :=
      (overlapOperator 𝕜 w u).rightSingularBasis.orthonormal.norm_eq_one i₀
    have hy₀ : ‖overlapOperator 𝕜 w u y₀‖ = (overlapOperator 𝕜 w u).singularValues (d - 1) :=
      (overlapOperator 𝕜 w u).norm_apply_rightSingularBasis i₀
    have hx₀U : hu.synthesisMapIsometry y₀ ∈ Submodule.span 𝕜 (Set.range u) :=
      (hu.range_synthesisMapIsometry.le ⟨y₀, rfl⟩)
    have hx₀n : ‖hu.synthesisMapIsometry y₀‖ = 1 := by
      rw [(hu.synthesisMapIsometry).norm_map]; exact hy₀n
    have hPx₀ : (Submodule.span 𝕜 (Set.range u)).starProjection (hu.synthesisMapIsometry y₀)
        = hu.synthesisMapIsometry y₀ := Submodule.starProjection_eq_self_iff.mpr hx₀U
    have hval : ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (hu.synthesisMapIsometry y₀)‖ ^ 2
        = 1 - cosPrincipalAngles hw hu (d - 1) ^ 2 := by
      rw [norm_sq_orthogonal_starProjection_familyIsometry hu hw y₀, hy₀n, hy₀,
        cosPrincipalAngles_def, one_pow]
    calc Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2)
        = ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (hu.synthesisMapIsometry y₀)‖ := by
          rw [← hval, Real.sqrt_sq (norm_nonneg _)]
      _ = ‖((Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection) (hu.synthesisMapIsometry y₀)‖ := by
          rw [ContinuousLinearMap.comp_apply, hPx₀]
      _ ≤ ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection‖ * ‖hu.synthesisMapIsometry y₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hx₀n, mul_one]

end TauCeti
