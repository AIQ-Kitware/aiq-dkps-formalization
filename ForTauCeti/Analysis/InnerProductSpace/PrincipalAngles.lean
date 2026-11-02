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
alignment consequence, the largest-angle norm identification and equal-rank
directed-sine spectrum arguments. The cosine dictionary is consumed directly
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

/-! ### Symmetry of the directed sine spectrum in equal dimensions

The cosine symmetry above is immediate from adjoints.  The corresponding sine
symmetry is subtler: the two coordinate sine maps have Gram operators
`I - M⋆M` and `I - MM⋆`, where `M` is the overlap operator.  The polar unitary
of `M` conjugates those complementary Gram operators, so the coordinate maps
have identical singular values.  Coisometry padding then transports the result
to the ambient cross projections.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.PrincipalAngles`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `34319dc`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**. Canonical synthesis and overlap now come from TauCeti.
-/

/-- **The Gram operator of the coordinate sine map is `1 - M⋆M`,**
where `M = overlapOperator 𝕜 v u`.

Stated once for the same reason `comp_starProjection_span_range_factor` is: the theorem below
needs it at `(u, v)` and again at `(v, u)`, and the two instances were written out in full --
forty lines each, identical under the swap. -/
private theorem adjoint_comp_starProjection_orthogonal_comp_familyIsometry
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    LinearMap.adjoint
        ((((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ (hu.synthesisMapIsometry).toLinearMap)
        ∘ₗ ((((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ (hu.synthesisMapIsometry).toLinearMap) =
      LinearMap.id - LinearMap.adjoint (overlapOperator 𝕜 v u) ∘ₗ overlapOperator 𝕜 v u := by
  apply LinearMap.ext
  intro x
  refine ext_inner_right 𝕜 fun y => ?_
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [LinearMap.adjoint_inner_left, inner_sub_left, LinearMap.adjoint_inner_left]
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change
    ⟪(Submodule.span 𝕜 (Set.range v))ᗮ.starProjection (hu.synthesisMapIsometry x),
        (Submodule.span 𝕜 (Set.range v))ᗮ.starProjection (hu.synthesisMapIsometry y)⟫_𝕜 =
      ⟪x, y⟫_𝕜 - ⟪overlapOperator 𝕜 v u x, overlapOperator 𝕜 v u y⟫_𝕜
  rw [← (Submodule.span 𝕜 (Set.range v))ᗮ.inner_starProjection_left_eq_right,
    (Submodule.span 𝕜 (Set.range v))ᗮ.starProjection_eq_self_iff.mpr
      ((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection_apply_mem _)]
  have hperp :
      (Submodule.span 𝕜 (Set.range v))ᗮ.starProjection (hu.synthesisMapIsometry x) =
        hu.synthesisMapIsometry x -
          (Submodule.span 𝕜 (Set.range v)).starProjection (hu.synthesisMapIsometry x) := by
    have h := congrArg
      (fun T : E →L[𝕜] E => T (hu.synthesisMapIsometry x))
      (Submodule.starProjection_orthogonal' (Submodule.span 𝕜 (Set.range v)))
    simpa only [sub_apply, one_apply_eq_self] using h
  have hproj (z : E) : (Submodule.span 𝕜 (Set.range v)).starProjection z =
      hv.synthesisMapIsometry (hv.synthesisMapIsometry.toLinearMap.adjoint z) := by
    rw [hv.synthesisMapIsometry_toLinearMap, adjoint_synthesisMap,
      Orthonormal.synthesisMapIsometry_apply, hv.starProjection_apply_eq_sum rfl]
    simp only [analysisMap_apply]
  rw [hperp, inner_sub_left, (hu.synthesisMapIsometry).inner_map_map, hproj]
  congr 1
  calc
    ⟪hv.synthesisMapIsometry
        ((hv.synthesisMapIsometry).toLinearMap.adjoint (hu.synthesisMapIsometry x)),
        hu.synthesisMapIsometry y⟫_𝕜 =
        ⟪(hv.synthesisMapIsometry).toLinearMap.adjoint (hu.synthesisMapIsometry x),
          (hv.synthesisMapIsometry).toLinearMap.adjoint (hu.synthesisMapIsometry y)⟫_𝕜 :=
      (LinearMap.adjoint_inner_right (hv.synthesisMapIsometry).toLinearMap
        ((hv.synthesisMapIsometry).toLinearMap.adjoint (hu.synthesisMapIsometry x))
        (hu.synthesisMapIsometry y)).symm
    _ = ⟪overlapOperator 𝕜 v u x, overlapOperator 𝕜 v u y⟫_𝕜 := by
      simp only [← LinearIsometry.coe_toLinearMap, hv.synthesisMapIsometry_toLinearMap,
        hu.synthesisMapIsometry_toLinearMap, adjoint_synthesisMap,
        overlapOperator_def, LinearMap.comp_apply]

/-- The coordinate sine maps associated with two equal-length orthonormal
families have the same singular values in the two directions. -/
theorem singularValues_orthogonal_familyIsometry_comm
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ((((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
        ∘ₗ (hu.synthesisMapIsometry).toLinearMap).singularValues =
      ((((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
        ∘ₗ (hv.synthesisMapIsometry).toLinearMap).singularValues := by
  let Iu := (hu.synthesisMapIsometry).toLinearMap
  let Iv := (hv.synthesisMapIsometry).toLinearMap
  let PuPerp : E →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
  let PvPerp : E →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
  let Suv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E := PvPerp ∘ₗ Iu
  let Svu : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E := PuPerp ∘ₗ Iv
  let M : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) := overlapOperator 𝕜 v u
  have hgramUV : LinearMap.adjoint Suv ∘ₗ Suv =
      LinearMap.id - LinearMap.adjoint M ∘ₗ M :=
    adjoint_comp_starProjection_orthogonal_comp_familyIsometry hu hv
  have hgramVU : LinearMap.adjoint Svu ∘ₗ Svu =
      LinearMap.id - LinearMap.adjoint (overlapOperator 𝕜 u v) ∘ₗ overlapOperator 𝕜 u v :=
    adjoint_comp_starProjection_orthogonal_comp_familyIsometry hv hu
  have hMadj : LinearMap.adjoint M = overlapOperator 𝕜 u v := by
    simpa only [M] using adjoint_overlapOperator v u
  have hgramVU' : LinearMap.adjoint Svu ∘ₗ Svu =
      LinearMap.id - M ∘ₗ LinearMap.adjoint M := by
    rw [hgramVU, ← hMadj, LinearMap.adjoint_adjoint]
  let O := choosePolarUnitary M
  have hconj : M ∘ₗ LinearMap.adjoint M =
      O.toLinearMap ∘ₗ (LinearMap.adjoint M ∘ₗ M) ∘ₗ O.symm.toLinearMap := by
    simpa only [O] using comp_adjoint_eq_conj_adjoint_comp M
  have hrotGram : LinearMap.adjoint Suv ∘ₗ Suv =
      LinearMap.adjoint (Svu ∘ₗ O.toLinearMap) ∘ₗ (Svu ∘ₗ O.toLinearMap) := by
    rw [hgramUV, LinearMap.adjoint_comp, O.adjoint_toLinearMap_eq_symm]
    rw [show (O.symm.toLinearMap ∘ₗ LinearMap.adjoint Svu) ∘ₗ
          (Svu ∘ₗ O.toLinearMap) =
        O.symm.toLinearMap ∘ₗ (LinearMap.adjoint Svu ∘ₗ Svu) ∘ₗ
          O.toLinearMap from by simp only [LinearMap.comp_assoc]]
    rw [hgramVU', hconj]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_apply_apply]
  calc
    Suv.singularValues = (Svu ∘ₗ O.toLinearMap).singularValues :=
      singularValues_eq_of_gram_eq hrotGram
    _ = Svu.singularValues := LinearMap.singularValues_comp_linearIsometryEquiv Svu O

/-- **Factor a projection composite through the coordinate isometry.**  `starProjection`
onto `span (range u)` is `ι_u ∘ ι_u⋆`, so any operator postcomposed with it factors as
"restrict to coordinates, act, and pad back" -- the shape
`LinearMap.singularValues_comp_adjoint_linearIsometry` consumes.

Stated once because the two halves of the symmetry below used it with `u` and `v` and were
otherwise identical; each was twelve lines of `change` and one rewrite. -/
private theorem comp_starProjection_span_range_factor {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (T : E →L[𝕜] E) :
    ((T ∘L (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = (((T : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ (hu.synthesisMapIsometry).toLinearMap)
          ∘ₗ LinearMap.adjoint (hu.synthesisMapIsometry).toLinearMap := by
  rw [ContinuousLinearMap.toLinearMap_comp,
    hu.toLinearMap_starProjection_eq_frameOperator rfl, frameOperator_def,
    ← adjoint_synthesisMap, ← hu.synthesisMapIsometry_toLinearMap, LinearMap.comp_assoc]

/-- The two ambient directed sine cross projections associated with equal-length
orthonormal families have identical singular-value sequences. -/
theorem singularValues_orthogonal_starProjection_comp_starProjection_comm
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) :
          E →ₗ[𝕜] E).singularValues =
      (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range v)).starProjection : E →L[𝕜] E) :
          E →ₗ[𝕜] E).singularValues := by
  let Suv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ∘ₗ (hu.synthesisMapIsometry).toLinearMap
  let Svu : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ∘ₗ (hv.synthesisMapIsometry).toLinearMap
  have hfactorUV :
      (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) =
        Suv ∘ₗ LinearMap.adjoint (hu.synthesisMapIsometry).toLinearMap :=
    comp_starProjection_span_range_factor hu _
  have hfactorVU :
      (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range v)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) =
        Svu ∘ₗ LinearMap.adjoint (hv.synthesisMapIsometry).toLinearMap :=
    comp_starProjection_span_range_factor hv _
  calc
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E).singularValues =
        Suv.singularValues := by
      rw [hfactorUV,
        LinearMap.singularValues_comp_adjoint_linearIsometry Suv (hu.synthesisMapIsometry)]
    _ = Svu.singularValues := by
      simpa only [Suv, Svu] using singularValues_orthogonal_familyIsometry_comm hu hv
    _ = (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range v)).starProjection : E →L[𝕜] E) :
            E →ₗ[𝕜] E).singularValues := by
      rw [hfactorVU,
        LinearMap.singularValues_comp_adjoint_linearIsometry Svu (hv.synthesisMapIsometry)]

end TauCeti
