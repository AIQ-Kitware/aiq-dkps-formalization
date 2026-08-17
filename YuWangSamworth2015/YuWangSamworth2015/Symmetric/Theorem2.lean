/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import YuWangSamworth2015.Core.ConsecutiveBlock
public import YuWangSamworth2015.Core.Procrustes

/-! # Yu--Wang--Samworth Theorem 2

This module is the source-facing surface for the paper's headline population-gap
result.  The reusable sine-distance notion remains in `ForTauCeti`; the
population-gap residual argument, source indexing, and alignment statement are
owned by the application package.
-/

public section

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## Theorem 2 with the source's indexing

The four statements below fix `r ≤ s` and `d = s − r + 1`, written `r + d = s + 1`
to avoid truncated subtraction, and take the gap in the printed form
`Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.  The paper's `r ≤ s` is exactly `1 ≤ d`
here and is not needed for the conclusion: at `d = 0` the frames are empty and
the bound is trivial, so it is not imposed. -/

/-- **Yu--Wang--Samworth Theorem 2, first conclusion, as printed.**

`r ≤ s`, `d = s − r + 1`, `V` and `V̂` arbitrary orthonormal eigenframes at the
indices `r, …, s`, no sample separation whatever, and only the two-sided
*population* boundary gap `Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.  Then

`‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`.

Indices are `0`-based, so `s + 1 ≤ n` is the paper's `s ≤ p`. -/
theorem yuWangSamworth_sinTheta_block_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ :=
  yuWangSamworth_sinTheta_frame_le hu hv hΔ (hgap.indexGap _ hd)

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, as printed.**
With the same hypotheses there is an orthogonal `Ô` on the block's coordinate
space with `‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`. -/
theorem yuWangSamworth_alignedFrame_block_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          2 * Real.sqrt 2 *
            min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
              (UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A)) / Δ :=
  yuWangSamworth_alignedFrame_le hu hv hΔ (hgap.indexGap _ hd)

/-- **The residual form of Theorem 2 with the source's indexing.**
`Δ ‖sin Θ(V̂, V)‖_F ≤ ‖V̂ Λ − Σ V̂‖_F`, with `Λ = diag(λ_r, …, λ_s)` the
*population* eigenvalues of the block. -/
theorem yuWangSamworth_sinTheta_block_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      Real.sqrt (∑ i,
        ‖(hA.eigenvalues hn (consecutiveEmb (hd.trans_le hsn) i) : 𝕜) • v i - A (v i)‖ ^ 2)
        / Δ :=
  yuWangSamworth_sinTheta_le_residual hu hv hΔ (hgap.indexGap _ hd)

/-- **The residual form of the aligned conclusion with the source's indexing.**
`‖V̂ Ô − V‖_F ≤ 2^{1/2} ‖V̂ Λ − Σ V̂‖_F / Δ`. -/
theorem yuWangSamworth_alignedFrame_block_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank 𝕜 E = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    ∃ O : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d),
      (∀ x y, ⟪O x, O y⟫_𝕜 = ⟪x, y⟫_𝕜) ∧
        Real.sqrt (∑ i, ‖frameComp hv.orthonormal O i - u i‖ ^ 2) ≤
          Real.sqrt 2 *
            Real.sqrt (∑ i,
              ‖(hA.eigenvalues hn (consecutiveEmb (hd.trans_le hsn) i) : 𝕜) • v i
                - A (v i)‖ ^ 2) / Δ :=
  yuWangSamworth_alignedFrame_le_residual hu hv hΔ (hgap.indexGap _ hd)

/-! ## The fully literal real statement -/

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, exactly as printed.**

Real symmetric `Σ`, `Σ̂`; a block `r, …, s` with `d = s − r + 1`; arbitrary
orthonormal eigenframes `V`, `V̂` at those indices with no sample separation; and
the two-sided population boundary gap `Δ ≤ min(λ_{r-1} − λ_r, λ_s − λ_{s+1})`.
Then there is an orthogonal matrix `Ô ∈ O(d)` with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`,

the `i`-th column of `V̂ Ô` being `∑ⱼ Ôⱼᵢ v̂ⱼ`.  Every symbol of the printed
conclusion appears here; the `RCLike` forms above are its generalizations. -/
theorem yuWangSamworth_alignedFrame_block_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n d r s : ℕ} {hn : finrank ℝ F = n} (hsn : s + 1 ≤ n) (hd : r + d = s + 1)
    {u v : Fin d → F}
    (hu : IsOrderedEigenframe hA hn (consecutiveEmb (hd.trans_le hsn)) u)
    (hv : IsOrderedEigenframe hB hn (consecutiveEmb (hd.trans_le hsn)) v)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : OrderedBlockBoundaryGap hA hn r s Δ) :
    ∃ O : Matrix (Fin d) (Fin d) ℝ, O ∈ Matrix.orthogonalGroup (Fin d) ℝ ∧
      Real.sqrt (∑ i, ‖(∑ j, O j i • v j) - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius ℝ F (B - A)) / Δ :=
  yuWangSamworth_alignedFrame_real_le hu hv hΔ (hgap.indexGap _ hd)

end Real

end YuWangSamworth2015
