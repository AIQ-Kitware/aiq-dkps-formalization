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

This module retains Fin-indexed eigenblock enumeration, the selected-polar
alignment consequence and the largest-angle norm identification. Equal-rank
directed-sine symmetry comes directly from TauCeti. The cosine dictionary is consumed directly
from `Orthonormal.principalCosines_eq_cosPrincipalAngles` at its paper callers.

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

/-! ### Eigenblock families and the encoding-coherence bridges

The `sinThetaSq` of two eigenblock families equals the cross-block overlap sum
used throughout `DavisKahan.lean`, and (for equal blocks) half the squared
Frobenius distance of the two spectral projections.  All the `sin Θ` encodings in
this development are therefore provably the same quantity. -/

section Block

variable {n : ℕ}

/-- The orthonormal family enumerating the `s`-selected vectors of an
orthonormal basis. -/
noncomputable def blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Fin d → E := fun i => b (s.orderIsoOfFin hd i)

omit [FiniteDimensional 𝕜 E] in
/-- Selecting a subset of an orthonormal basis leaves an orthonormal family. -/
theorem orthonormal_blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Orthonormal 𝕜 (blockFamily b s hd) :=
  b.orthonormal.comp _ (Subtype.coe_injective.comp (s.orderIsoOfFin hd).injective)

omit [FiniteDimensional 𝕜 E] in
/-- The selected family enumerates exactly the basis vectors indexed by `s`; this is what lets a
block be described either by its index set or by its span. -/
theorem range_blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Set.range (blockFamily b s hd) = b '' ↑s := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, (s.orderIsoOfFin hd i).2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(s.orderIsoOfFin hd).symm ⟨j, hj⟩, ?_⟩
    simp [blockFamily]

private theorem sum_blockFamily {s : Finset (Fin n)} (hd : s.card = d) (g : Fin n → ℝ) :
    ∑ i : Fin d, g ((s.orderIsoOfFin hd i : Fin n)) = ∑ i ∈ s, g i := by
  rw [← Finset.sum_coe_sort s g]
  exact Fintype.sum_equiv (s.orderIsoOfFin hd).toEquiv _ _ fun i => rfl

omit [FiniteDimensional 𝕜 E] in
/-- **`sinThetaSq` of two eigenblocks is the cross-block overlap sum** — the
bridge from the principal-angle encoding to the `DavisKahan.lean` encoding. -/
theorem sinThetaSq_blockFamily_eq_sum_cross (bT bS : OrthonormalBasis (Fin n) 𝕜 E)
    {s s' : Finset (Fin n)} (hsd : s.card = d) (hs'd : s'.card = d) :
    sinThetaSq (orthonormal_blockFamily bT s hsd) (orthonormal_blockFamily bS s' hs'd)
      = ∑ j ∈ s', ∑ i ∈ sᶜ, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := by
  rw [sinThetaSq_eq_card_sub_sum_norm_inner_sq, Fintype.card_fin]
  have hrow : ∀ j : Fin n, ∑ i : Fin d, ‖⟪blockFamily bT s hsd i, bS j⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := fun j =>
    sum_blockFamily hsd fun i => ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
  have houter : ∑ k : Fin d, ∑ i : Fin d,
        ‖⟪blockFamily bT s hsd i, blockFamily bS s' hs'd k⟫_𝕜‖ ^ 2
      = ∑ j ∈ s', ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := by
    rw [show (fun k : Fin d => ∑ i : Fin d,
          ‖⟪blockFamily bT s hsd i, blockFamily bS s' hs'd k⟫_𝕜‖ ^ 2)
        = fun k : Fin d => ∑ i ∈ s,
          ‖⟪bT i, bS ((s'.orderIsoOfFin hs'd k : Fin n))⟫_𝕜‖ ^ 2 from
      funext fun k => hrow _]
    exact sum_blockFamily hs'd fun j => ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
  rw [houter]
  have hpars : ∀ j : Fin n, ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
      + ∑ i ∈ sᶜ, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 = 1 := fun j => by
    rw [Finset.sum_add_sum_compl, bT.sum_sq_norm_inner_right (bS j),
      bS.orthonormal.norm_eq_one j, one_pow]
  have hcard : (d : ℝ) = ∑ _j ∈ s', (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hs'd]
  rw [hcard, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by linarith [hpars j]

/-- **`sinThetaSq` is half the squared Frobenius projector distance**: for two
eigenblocks selected by the same `s`,
`∑ₖ ‖(P̂ − P)(bT k)‖² = 2 sinThetaSq`. -/
theorem sum_norm_sub_starProjection_sq_eq_two_mul_sinThetaSq
    (bT bS : OrthonormalBasis (Fin n) 𝕜 E) {s : Finset (Fin n)} (hsd : s.card = d) :
    ∑ k, ‖((Submodule.span 𝕜 (bS '' ↑s)).starProjection
        - (Submodule.span 𝕜 (bT '' ↑s)).starProjection) (bT k)‖ ^ 2
      = 2 * sinThetaSq (orthonormal_blockFamily bT s hsd)
          (orthonormal_blockFamily bS s hsd) := by
  rw [sum_norm_sub_starProjection_span_sq_eq bT bS s,
    sinThetaSq_comm, sinThetaSq_blockFamily_eq_sum_cross bS bT hsd hsd]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← norm_inner_symm]

end Block

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
      rw [hsum, ← Orthonormal.starProjection_span_image_apply hu Finset.univ]
      apply Submodule.starProjection_eq_self_iff.mpr
      rw [Finset.coe_univ, Set.image_univ]
      exact Submodule.starProjection_apply_mem _ z
    have hyz : ‖y‖ ≤ ‖z‖ := by
      have h1 : ‖y‖ = ‖(Submodule.span 𝕜 (Set.range u)).starProjection z‖ := by
        rw [← hxy, (hu.synthesisMapIsometry).norm_map]
      rw [h1]
      exact Submodule.norm_starProjection_apply_le _ z
    have hmin : cosPrincipalAngles hw hu (d - 1) * ‖y‖ ≤ ‖overlapOperator 𝕜 w u y‖ := by
      rw [cosPrincipalAngles_def]
      exact singularValues_last_mul_norm_le (overlapOperator 𝕜 w u) finrank_euclideanSpace_fin hd y
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
    obtain ⟨y₀, hy₀n, hy₀⟩ := exists_norm_apply_eq_singularValues_last (overlapOperator 𝕜 w u)
      finrank_euclideanSpace_fin hd
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
