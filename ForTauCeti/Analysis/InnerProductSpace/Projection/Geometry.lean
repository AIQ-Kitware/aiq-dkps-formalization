/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.SpanProjection


/-!
# Projector distance between arbitrary orthonormal bases

The squared Frobenius distance between selected basis projections equals twice
the cross-overlap sum. Elementary projection formulas are consumed upstream.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-!
The elementary projection and finite-family Parseval formulas are supplied by
Mathlib and Tau Ceti. The retained identity compares two arbitrary orthonormal
bases; it is distinct from the canonical-family Frobenius sine formula.

## Provenance

Original module `ForMathlib.Analysis.InnerProductSpace.ProjectionGeometry`,
introduced at DKPS `f44d966`; authors Jon Crall, Claude Fable 5, Claude Opus 4.8,
Kitware copyright, Apache-2.0. Native finite-family formulas were independently
implemented in Tau Ceti #16089; its integration explicitly disclaims DKPS #13864
proof descent. The complementary selected-span formula consumes the accepted
BasisSpan construction and family Parseval theorem.
-/

variable [FiniteDimensional 𝕜 F] {m : ℕ}

omit [FiniteDimensional 𝕜 F] in
/-- Symmetric block-counting identity for two orthonormal bases `u`, `v` and an
index set `s`: the squared overlaps summed over the `(sᶜ, s)` block equal those
summed over the `(s, sᶜ)` block.  Both equal `s.card` minus the leading–leading
overlap sum, by Parseval (each row of overlaps sums to `1`). -/
private theorem sum_inner_sq_compl_block_eq (u v : OrthonormalBasis (Fin m) 𝕜 F)
    (s : Finset (Fin m)) :
    ∑ k ∈ sᶜ, ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [Finset.sum_comm]
  -- For a unit vector `w` and orthonormal basis `b`, the overlaps split as
  -- `∑_{sᶜ} = 1 − ∑_s` by Parseval.
  have key : ∀ (b : OrthonormalBasis (Fin m) 𝕜 F) (w : F), ‖w‖ = 1 →
      ∑ k ∈ sᶜ, ‖⟪w, b k⟫_𝕜‖ ^ 2 = 1 - ∑ k ∈ s, ‖⟪w, b k⟫_𝕜‖ ^ 2 := by
    intro b w hw
    have hpar : ∑ k, ‖⟪w, b k⟫_𝕜‖ ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun k _ => by rw [norm_inner_symm],
        b.sum_sq_norm_inner_right w, hw, one_pow]
    linarith [Finset.sum_add_sum_compl s fun k => ‖⟪w, b k⟫_𝕜‖ ^ 2]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ s) => key u (v j) (v.orthonormal.1 j),
    Finset.sum_congr rfl fun i (_ : i ∈ s) => key v (u i) (u.orthonormal.1 i),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm])

/--
**Projector form of the Davis–Kahan identity.** For two orthonormal bases `u`,
`v` of a finite-dimensional inner product space over `𝕜 = ℝ, ℂ` and an index set
`s`, the squared Frobenius distance (computed in the basis `u`) between the
orthogonal projections onto `span (v '' s)` and `span (u '' s)` is twice the
cross overlap sum:
`∑ₖ ‖(P_v − P_u) uₖ‖² = 2 ∑_{i ∈ s} ∑_{j ∉ s} ‖⟪uᵢ, vⱼ⟫‖²`.
-/
theorem sum_norm_sub_starProjection_span_sq_eq (u v : OrthonormalBasis (Fin m) 𝕜 F)
    (s : Finset (Fin m)) :
    ∑ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = 2 * ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  -- Per-`k` reduction: the `k`-th term is a single cross-overlap row.
  have hQnorm : ∀ k, ‖(Submodule.span 𝕜 (v '' ↑s)).starProjection (u k)‖ ^ 2
      = ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 :=
    fun k => by
      have hr : Set.range (v ∘ fun i : s => (i : Fin m)) = v '' (s : Set (Fin m)) := by
        ext; simp
      have hf := (v.orthonormal.comp _ Subtype.val_injective).norm_starProjection_sq_eq_sum
        (U := Submodule.span 𝕜 (v '' ↑s)) (by rw [hr]) (u k)
      simpa only [Function.comp_apply] using hf.trans
        (Finset.sum_coe_sort s (fun j => ‖⟪v j, u k⟫_𝕜‖ ^ 2))
  have hterm : ∀ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = if k ∈ s then ∑ j ∈ sᶜ, ‖⟪v j, u k⟫_𝕜‖ ^ 2 else ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 := by
    intro k
    have hproj : (Submodule.span 𝕜 (u '' ↑s)).starProjection (u k) =
        if k ∈ s then u k else 0 := by
      have hr : Set.range (u ∘ fun i : s => (i : Fin m)) = u '' (s : Set (Fin m)) := by
        ext; simp
      rw [(u.orthonormal.comp _ Subtype.val_injective).starProjection_apply_eq_sum
        (U := Submodule.span 𝕜 (u '' ↑s)) (by rw [hr])]
      simp only [Function.comp_apply]
      rw [Finset.sum_coe_sort s (fun i => ⟪u i, u k⟫_𝕜 • u i)]
      simp only [orthonormal_iff_ite.mp u.orthonormal, ite_smul,
        one_smul, zero_smul]
      exact Finset.sum_ite_eq' s k fun i => u i
    rw [show (((Submodule.span 𝕜 (v '' ↑s)).starProjection
          - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k))
        = (Submodule.span 𝕜 (v '' ↑s)).starProjection (u k)
          - (Submodule.span 𝕜 (u '' ↑s)).starProjection (u k) from rfl,
      hproj]
    split <;> rename_i hk
    · -- `k ∈ s`: `P_u` keeps `uₖ`, so the term is the residual of `uₖ` against the `v`-span,
      -- which is the complementary Parseval sum.
      rw [norm_sub_rev]
      rw [← Submodule.starProjection_orthogonal_val]
      simpa only [OrthonormalBasis.spanIndices_eq_span] using
        v.norm_starProjection_orthogonal_spanIndices_sq s (u k)
    · -- `k ∉ s`: the `u`-projection vanishes; the term is the `v`-projection norm.
      rw [sub_zero, hQnorm k]
  -- Sum the per-`k` formula and swap the two cross blocks into each other.
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_add_sum_compl s]
  rw [Finset.sum_congr rfl fun k (hk : k ∈ s) => ite_eq_left hk,
    Finset.sum_congr rfl fun k (hk : k ∈ sᶜ) => ite_eq_right (Finset.mem_compl.mp hk)]
  -- First block is the target cross sum (after swapping the inner-product slots).
  have hswap : ∀ (i j : Fin m), ‖⟪v j, u i⟫_𝕜‖ = ‖⟪u i, v j⟫_𝕜‖ := fun i j =>
    norm_inner_symm (v j) (u i)
  have hA : ∑ k ∈ s, ∑ j ∈ sᶜ, ‖⟪v j, u k⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hswap i j]
  -- Second block equals the first by the symmetric block-counting identity.
  have hB : ∑ k ∈ sᶜ, ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := sum_inner_sq_compl_block_eq u v s
  rw [hA, hB]
  ring

end TauCeti
