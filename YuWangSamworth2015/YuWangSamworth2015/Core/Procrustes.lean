/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import YuWangSamworth2015.Core.Statistics

/-! # The one-sided Procrustes alignment `V̂ Ô`

Yu, Wang and Samworth's second conclusion compares the *sample* frame, rotated
inside its own span, against the population frame left where it is:

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`, with `Ô ∈ O(d)`.

`YuWangSamworth2015.exists_aligned_orthonormalBasis` records the weaker existential in which
*both* frames are replaced by new ones spanning the same subspaces.  That is
enough to derive the numerical bound and nothing else: a reader cannot tell from
it that the population frame is untouched, nor recover the `d × d` alignment.
The alignment is not lost, only hidden — `sum_sq_norm_aligned_le_sinThetaSq`
rotates `v` by the polar unitary of the overlap operator and leaves `u` alone —
so this file names it.

`frameComp hv O` is the paper's matrix product `V̂ Ô`: its `i`-th column is
`∑ⱼ Ôⱼᵢ v̂ⱼ`.  `O` is a bundled `EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜
(Fin d)`, which over `ℝ` is exactly an element of `O(d)`; `adjoint_comp_self_eq_id`
spells that out as `Ôᵀ Ô = I`.

## Main results

* `YuWangSamworth2015.frameComp`: the rotated frame `V̂ Ô`, with its expansion, orthonormality
  and span.
* `YuWangSamworth2015.exists_unitary_sum_sq_norm_frameComp_sub_le`: the Procrustes step
  `‖V̂ Ô − V‖²_F ≤ 2 ‖sin Θ‖²_F` with the alignment exhibited.
* `YuWangSamworth2015.yuWangSamworth_alignedFrame_le` and
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_le_residual`: Theorem 2's second
  conclusion and its sharper residual form, both with an explicit `Ô`.
* `YuWangSamworth2015.frameAlignMatrix` and
  `YuWangSamworth2015.yuWangSamworth_alignedFrame_real_le`: over `ℝ`, the same conclusion
  with `Ô` an honest element of `Matrix.orthogonalGroup (Fin d) ℝ` and the
  columns of `V̂Ô` written as the matrix products `∑ⱼ Ôⱼᵢ v̂ⱼ`.
-/

public section

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {d : ℕ}

/-- **`Ôᵀ Ô = I`.**  A bundled linear isometry equivalence of the coordinate space
is an orthogonal (unitary) matrix; this is that statement in the form a reader of
the paper expects, so that `Ô ∈ O(d)` needs no interpretation. -/
theorem adjoint_comp_self_eq_id
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    LinearMap.adjoint (O.toLinearEquiv.toLinearMap) ∘ₗ O.toLinearEquiv.toLinearMap =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  refine ext_inner_left 𝕜 fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.id_apply]
  exact O.inner_map_map y x

/-- **The rotated frame `V̂ Ô`.**  Column `i` of the product of the frame `v` with
the coordinate isometry `O`; see `frameComp_apply` for the expansion. -/
noncomputable def frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) : Fin d → E :=
  fun i => familyIsometry hv (O (EuclideanSpace.single i 1))

omit [FiniteDimensional 𝕜 E] in
/-- **The characteristic lemma.**  `(V̂ Ô)ᵢ = ∑ⱼ Ôⱼᵢ v̂ⱼ`: the definition is a
matrix product, written through the coordinate isometry. -/
theorem frameComp_apply {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) (i : Fin d) :
    frameComp hv O i = ∑ j, O (EuclideanSpace.single i 1) j • v j := by
  rw [frameComp, familyIsometry_apply]

omit [FiniteDimensional 𝕜 E] in
/-- The rotated frame is again orthonormal: both `O` and the coordinate isometry
of `v` preserve inner products. -/
theorem orthonormal_frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    Orthonormal 𝕜 (frameComp hv O) := by
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪familyIsometry hv (O (EuclideanSpace.single i (1 : 𝕜))),
      familyIsometry hv (O (EuclideanSpace.single j (1 : 𝕜)))⟫_𝕜 = if i = j then 1 else 0
  rw [(familyIsometry hv).inner_map_map, O.inner_map_map]
  exact orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j

/-- Rotating a frame does not move its span — `V̂ Ô` and `V̂` are frames of the
same subspace, which is why the alignment costs nothing on the sine side. -/
theorem span_range_frameComp {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    Submodule.span 𝕜 (Set.range (frameComp hv O)) = Submodule.span 𝕜 (Set.range v) :=
  span_range_eq_of_orthonormal_of_mem (orthonormal_frameComp hv O)
    (fun i => by rw [frameComp_apply]
                 exact Submodule.sum_smul_mem _ _ fun j _ =>
                   Submodule.subset_span (Set.mem_range_self j))
    (by rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin])

/-- **The Procrustes step, with the alignment exhibited.**

`‖V̂ Ô − V‖²_F ≤ 2 ‖sin Θ(V̂, V)‖²_F` for an orthogonal `Ô` acting on the
coordinate space of the frames, with the population frame `u` held fixed.  `Ô` is
the polar unitary of the overlap operator, so no minimization is left implicit. -/
theorem exists_unitary_sum_sq_norm_frameComp_sub_le {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        ∑ i, ‖frameComp hv O i - u i‖ ^ 2 ≤
          2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
            (Submodule.span 𝕜 (Set.range v)) ^ 2 := by
  refine ⟨(choosePolarUnitary (overlapOp hu hv)).symm,
    fun x y => LinearIsometryEquiv.inner_map_map _ x y, ?_⟩
  have h := sum_sq_norm_aligned_le_sinThetaSq hu hv
  rwa [sinThetaSq_eq_sinThetaFrobenius_sq_of_spans hu hv rfl rfl] at h

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, with an explicit `Ô`.**

For arbitrary ordered eigenframes `V`, `V̂` at a common index block and a
population-only gap `Δ`, there is an orthogonal `Ô` on the `d`-dimensional
coordinate space with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`.

Unlike `yuWangSamworth_alignedBasis_frame_le` the population frame is the one
supplied, not a new frame of the same span. -/
theorem yuWangSamworth_alignedFrame_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
              (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ := by
  obtain ⟨O, hO, hsum⟩ :=
    exists_unitary_sum_sq_norm_frameComp_sub_le hu.orthonormal hv.orthonormal
  refine ⟨O, hO, ?_⟩
  have hsine := yuWangSamworth_sinTheta_frame_le hu hv hΔ hgap
  have hsnn : (0 : ℝ) ≤ sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) :=
    by rw [sinThetaFrobenius_eq]; exact (UnitarilyInvariantSeminorm.frobenius 𝕜 E).nonneg _
  calc Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 * (2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = 2 * Real.sqrt 2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ := by ring

/-- **The residual form of the aligned conclusion, with an explicit `Ô`.**
`‖V̂ Ô − V‖_F ≤ 2^{1/2} ‖V̂ Λ − Σ V̂‖_F / Δ`, the inequality Yu, Wang and Samworth
record as available from their proof before the residual is discarded. -/
theorem yuWangSamworth_alignedFrame_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          Real.sqrt 2 *
            Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
  obtain ⟨O, hO, hsum⟩ :=
    exists_unitary_sum_sq_norm_frameComp_sub_le hu.orthonormal hv.orthonormal
  refine ⟨O, hO, ?_⟩
  have hsine := yuWangSamworth_sinTheta_le_residual hu hv hΔ hgap
  have hsnn : (0 : ℝ) ≤ sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) :=
    by rw [sinThetaFrobenius_eq]; exact (UnitarilyInvariantSeminorm.frobenius 𝕜 E).nonneg _
  calc Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 *
          (Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 *
          Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
        ring

/-! ## Over `ℝ`: `Ô` as an element of `O(d)`

The source is a real-matrix paper, and its `Ô` is an orthogonal matrix.  A
bundled `EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)` is exactly
that, but a reader should not have to know it, so the real statement below
produces the matrix itself, together with its membership in
`Matrix.orthogonalGroup (Fin d) ℝ`. -/

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **The matrix of a coordinate isometry** in the standard basis:
`Ôⱼᵢ = (Ô eᵢ)ⱼ`.  Over `ℝ` this is the paper's orthogonal matrix. -/
@[expose]
noncomputable def frameAlignMatrix
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j i => O (EuclideanSpace.single i 1) j

@[simp] theorem frameAlignMatrix_apply
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (j i : Fin d) :
    frameAlignMatrix O j i = O (EuclideanSpace.single i 1) j := rfl

/-- **`Ô ∈ O(d)`.**  The columns of `frameAlignMatrix O` are the images of an
orthonormal basis under an isometry, so `ÔᵀÔ = I`. -/
theorem frameAlignMatrix_mem_orthogonalGroup
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    frameAlignMatrix O ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
  refine (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mpr ?_
  ext i k
  have hO := O.inner_map_map (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single k (1 : ℝ))
  have hsingle : ⟪(EuclideanSpace.single i (1 : ℝ)),
      (EuclideanSpace.single k (1 : ℝ))⟫_ℝ = if i = k then 1 else 0 :=
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i k
  rw [Matrix.mul_apply, Matrix.one_apply, ← hsingle, ← hO, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [Matrix.transpose_apply, RCLike.inner_apply, mul_comm]

omit [FiniteDimensional ℝ F] in
/-- The columns of `V̂Ô` in matrix notation. -/
theorem frameComp_eq_sum_frameAlignMatrix {v : Fin d → F} (hv : Orthonormal ℝ v)
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    frameComp hv O i = ∑ j, frameAlignMatrix O j i • v j :=
  frameComp_apply hv O i

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, over `ℝ` with `Ô ∈ O(d)`.**

The literal printed statement: there is an orthogonal `d × d` matrix `Ô` with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`,

where the `i`-th column of `V̂ Ô` is `∑ⱼ Ôⱼᵢ v̂ⱼ` and `V` is the supplied
population frame.  This is `yuWangSamworth_alignedFrame_le` at `𝕜 = ℝ`, with the
coordinate isometry replaced by its matrix. -/
theorem yuWangSamworth_alignedFrame_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank ℝ F = n} {e : Fin d ↪ Fin n} {u v : Fin d → F}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • v j) - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius ℝ F (B - A)) / Δ := by
  obtain ⟨O, -, hbound⟩ := yuWangSamworth_alignedFrame_le hu hv hΔ hgap
  refine ⟨frameAlignMatrix O, frameAlignMatrix_mem_orthogonalGroup O, ?_⟩
  have hcols : ∀ i, (∑ j, frameAlignMatrix O j i • v j) = frameComp hv.orthonormal O i :=
    fun i => (frameComp_eq_sum_frameAlignMatrix hv.orthonormal O i).symm
  simpa only [hcols] using hbound

end Real

end YuWangSamworth2015
