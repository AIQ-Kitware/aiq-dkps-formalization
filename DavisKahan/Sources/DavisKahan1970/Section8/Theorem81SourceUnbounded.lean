/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Section8.Theorem81UnboundedReal

/-!
# Theorem 8.1 on the source's own objects, at unbounded ambient scope

The unbounded results of `Theorem81UnboundedBranch`, `…Compression`,
`…Converse` and `…Real` are stated the way they are proved: the placements as
form inequalities over the ambient domain, part (i) for an arbitrary partial map
`B` and reducing subspace `Q`.  Those are the right shapes for the mathematics
and the wrong shapes for a source boundary.

This module restates them on the objects Davis and Kahan write.  `Λ₀` and `Λ₁`
are the two reducing blocks of `A + H`, so they are
`reducingRestriction (A + H) Q` and its complement, and `Λ₀ ≤ α`, `Λ₁ ≥ α + δ`
are `SemiboundedAbove` and `SemiboundedBelow` on those blocks.  `A₀`, `A₁` are
the blocks of `A` on `P` and `Pᗮ`.  `C₁` is the cosine block `P_{Qᗮ}` read on
`Pᗮ`.

Everything here is a façade.  No proof below does anything a reader would call
mathematics: the block/ambient bridge `semiboundedAbove_reducingRestriction_iff`
is unfolding, and part (i) uses only that `H` is fully off-diagonal, so its form
vanishes on `P` and on `Pᗮ` and the ambient form of `A + H` there is the form of
`A`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan

noncomputable section

universe v

/-! ### The block/ambient bridge -/

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **`Λ ≤ c` on a reducing block is the ambient form bound on that block.**

Unfolding, in both directions: a restricted-domain vector is an ambient domain
vector lying in the subspace, and the subspace carries the restricted inner
product and norm. -/
theorem semiboundedAbove_reducingRestriction_iff
    {B : H →ₗ.[𝕜] H} {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B U) (c : ℝ) :
    TauCeti.LinearPMap.SemiboundedAbove
        (TauCeti.LinearPMap.reducingRestriction B U hred) c ↔
      ∀ x : B.domain, (x : H) ∈ U →
        RCLike.re ⟪B x, (x : H)⟫_𝕜 ≤ c * ‖(x : H)‖ ^ 2 := by
  constructor
  · intro h x hx
    have hy : (⟨(x : H), hx⟩ : U) ∈
        (TauCeti.LinearPMap.reducingRestriction B U hred).domain :=
      (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff B U hred _).mpr x.2
    have := h ⟨⟨(x : H), hx⟩, hy⟩
    rwa [show (TauCeti.LinearPMap.reducingRestriction B U hred ⟨⟨(x : H), hx⟩, hy⟩ : U)
        = ⟨B ⟨(x : H), x.2⟩, hred.invariant _ hx⟩ from
          Subtype.ext (TauCeti.LinearPMap.coe_reducingRestriction_apply B U hred _ x.2),
      Submodule.coe_inner] at this
  · intro h y
    have hmem : ((y : U) : H) ∈ B.domain :=
      (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff B U hred _).mp y.2
    have := h ⟨((y : U) : H), hmem⟩ (y : U).2
    rwa [show (TauCeti.LinearPMap.reducingRestriction B U hred y : U)
        = ⟨B ⟨((y : U) : H), hmem⟩, hred.invariant _ (y : U).2⟩ from
          Subtype.ext (TauCeti.LinearPMap.coe_reducingRestriction_apply B U hred _ hmem),
      Submodule.coe_inner]

omit [CompleteSpace H] in
/-- **`Λ ≥ c` on a reducing block is the ambient form bound on that block.** -/
theorem semiboundedBelow_reducingRestriction_iff
    {B : H →ₗ.[𝕜] H} {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B U) (c : ℝ) :
    TauCeti.LinearPMap.SemiboundedBelow
        (TauCeti.LinearPMap.reducingRestriction B U hred) c ↔
      ∀ x : B.domain, (x : H) ∈ U →
        c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪B x, (x : H)⟫_𝕜 := by
  constructor
  · intro h x hx
    have hy : (⟨(x : H), hx⟩ : U) ∈
        (TauCeti.LinearPMap.reducingRestriction B U hred).domain :=
      (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff B U hred _).mpr x.2
    have := h ⟨⟨(x : H), hx⟩, hy⟩
    rwa [show (TauCeti.LinearPMap.reducingRestriction B U hred ⟨⟨(x : H), hx⟩, hy⟩ : U)
        = ⟨B ⟨(x : H), x.2⟩, hred.invariant _ hx⟩ from
          Subtype.ext (TauCeti.LinearPMap.coe_reducingRestriction_apply B U hred _ x.2),
      Submodule.coe_inner] at this
  · intro h y
    have hmem : ((y : U) : H) ∈ B.domain :=
      (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff B U hred _).mp y.2
    have := h ⟨((y : U) : H), hmem⟩ (y : U).2
    rwa [show (TauCeti.LinearPMap.reducingRestriction B U hred y : U)
        = ⟨B ⟨((y : U) : H), hmem⟩, hred.invariant _ (y : U).2⟩ from
          Subtype.ext (TauCeti.LinearPMap.coe_reducingRestriction_apply B U hred _ hmem),
      Submodule.coe_inner]

/-! ### Theorem 8.1 on the source's own objects, over `ℂ` -/

section Complex

variable {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
  [CompleteSpace Hc]
variable {A : Hc →ₗ.[ℂ] Hc} {Hop : Hc →L[ℂ] Hc} {P : Submodule ℂ Hc}
  [P.HasOrthogonalProjection] {alpha delta : ℝ}

/-- **Davis--Kahan 1970, Theorem 8.1's printed characterization, on the source's
own blocks, at unbounded ambient scope over `ℂ`.**

`Θ ≤ π/4` if and only if the chosen reducing blocks of `A + H` satisfy
`Λ₀ ≤ α` and `Λ₁ ≥ α + δ`.  `Λ₀` and `Λ₁` are the two reducing restrictions of
`A + H`, and the two relations are operator inequalities on them, which is how
the source writes them.  The hypotheses are the `tan 2θ` theorem's, likewise on
the blocks `A₀`, `A₁`. -/
theorem theorem8_1_maximalAngle_le_iff_blockPlacement_unbounded_complex
    (hA : IsSelfAdjoint A) (hH : DavisKahan.IsSelfAdjointOperator Hop)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hPlow : TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.reducingRestriction A P hPred) alpha)
    (hPhigh : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction A Pᗮ hPred.orthogonal) (alpha + delta))
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta)
    (Q : Submodule ℂ Hc) [Q.HasOrthogonalProjection]
    (hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Q) :
    TauCeti.DavisKahanExt.maximalAngle P Q ≤ Real.pi / 4 ↔
      (TauCeti.LinearPMap.SemiboundedAbove
          (TauCeti.LinearPMap.reducingRestriction
            (TauCeti.LinearPMap.addBounded A Hop) Q hQred) alpha ∧
        TauCeti.LinearPMap.SemiboundedBelow
          (TauCeti.LinearPMap.reducingRestriction
            (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal)
          (alpha + delta)) := by
  rw [semiboundedAbove_reducingRestriction_iff, semiboundedBelow_reducingRestriction_iff]
  exact theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded hA hH hPred.orthogonal
    ((semiboundedAbove_reducingRestriction_iff hPred alpha).mp hPlow)
    ((semiboundedBelow_reducingRestriction_iff hPred.orthogonal (alpha + delta)).mp hPhigh)
    hHP hHPperp hdelta Q hQred

/-- **Davis--Kahan 1970, Theorem 8.1's existence clause, on the source's own
blocks, at unbounded ambient scope over `ℂ`.**

"For fixed `A`, `P`, `H` there exists a reducing projector `Q` with these
properties."  The witness is the spectral projector of `A + H` on the side of
`α`, but the statement is the existential the source asserts. -/
theorem theorem8_1_exists_branch_blockPlacement_unbounded_complex
    (hA : IsSelfAdjoint A) (hH : DavisKahan.IsSelfAdjointOperator Hop)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hPlow : TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.reducingRestriction A P hPred) alpha)
    (hPhigh : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction A Pᗮ hPred.orthogonal) (alpha + delta))
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    ∃ (Q : Submodule ℂ Hc) (hQinst : Q.HasOrthogonalProjection),
      haveI := hQinst
      ∃ hQred : TauCeti.LinearPMap.ReducesSubspace
          (TauCeti.LinearPMap.addBounded A Hop) Q,
        TauCeti.LinearPMap.SemiboundedAbove
            (TauCeti.LinearPMap.reducingRestriction
              (TauCeti.LinearPMap.addBounded A Hop) Q hQred) alpha ∧
          TauCeti.LinearPMap.SemiboundedBelow
            (TauCeti.LinearPMap.reducingRestriction
              (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal)
            (alpha + delta) ∧
          TauCeti.DavisKahanExt.maximalAngle P Q ≤ Real.pi / 4 := by
  obtain ⟨hred, hlow, hhigh, hangle⟩ :=
    theorem8_1_canonicalBranchUnbounded_printed (A := A) (Hop := Hop) (P := P)
      (alpha := alpha) (delta := delta) hA hH hPred.orthogonal
      ((semiboundedAbove_reducingRestriction_iff hPred alpha).mp hPlow)
      ((semiboundedBelow_reducingRestriction_iff hPred.orthogonal (alpha + delta)).mp hPhigh)
      hHP hHPperp hdelta
  refine ⟨canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha, _, hred,
    ?_, ?_, hangle⟩
  · exact (semiboundedAbove_reducingRestriction_iff hred alpha).mpr hlow
  · exact (semiboundedBelow_reducingRestriction_iff hred.orthogonal (alpha + delta)).mpr hhigh

omit [CompleteSpace Hc] [P.HasOrthogonalProjection] in
/-- **Davis--Kahan 1970, Theorem 8.1 part (i), upper block, on the source's own
objects, at unbounded ambient scope over `ℂ`.**

`A₁ − α ≤ C₁(Λ₁ − α)C₁` as a form inequality, read where the source reads it: on
`Pᗮ`, with `C₁` the cosine block `P_{Qᗮ}`.  The left side is the form of `A`,
not of `A + H`, because `H` is fully off-diagonal and so has no form on `Pᗮ`. -/
theorem theorem8_1_upperCompressionRepulsion_sourceExact_unbounded_complex
    (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (Q : Submodule ℂ Hc) [Q.HasOrthogonalProjection]
    (hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQlow : TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred) alpha)
    (x : (TauCeti.LinearPMap.addBounded A Hop).domain) (hx : (x : Hc) ∈ Pᗮ) :
    RCLike.re ⟪A ⟨(x : Hc), x.2⟩, (x : Hc)⟫_ℂ - alpha * ‖(x : Hc)‖ ^ 2 ≤
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop
          ⟨Qᗮ.starProjection (x : Hc), hQred.orthogonalProjection_mem_domain x⟩,
        Qᗮ.starProjection (x : Hc)⟫_ℂ
        - alpha * ‖Qᗮ.starProjection (x : Hc)‖ ^ 2 := by
  have hmain : RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Hc)⟫_ℂ
      - alpha * ‖(x : Hc)‖ ^ 2 ≤
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop
          ⟨Qᗮ.starProjection (x : Hc), hQred.orthogonalProjection_mem_domain x⟩,
        Qᗮ.starProjection (x : Hc)⟫_ℂ
        - alpha * ‖Qᗮ.starProjection (x : Hc)‖ ^ 2 :=
    theorem8_1_upperCompressionRepulsion_unbounded hQred
      ((semiboundedAbove_reducingRestriction_iff hQred alpha).mp hQlow) x
  have hzero : ⟪Hop (x : Hc), (x : Hc)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal P (x : Hc)).mp hx _ (hHPperp _ hx)
  have hform : RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Hc)⟫_ℂ
      = RCLike.re ⟪A ⟨(x : Hc), x.2⟩, (x : Hc)⟫_ℂ := by
    rw [TauCeti.LinearPMap.addBounded_apply, inner_add_left, map_add, hzero]
    simp only [map_zero, add_zero]
    rfl
  linarith [hmain, hform]

omit [CompleteSpace Hc] in
/-- **Davis--Kahan 1970, Theorem 8.1 part (i), lower block, on the source's own
objects, at unbounded ambient scope over `ℂ`.**

The analogous lower-block inequality, read on `P` with the cosine block
`P_Q`. -/
theorem theorem8_1_lowerCompressionRepulsion_sourceExact_unbounded_complex
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ)
    (Q : Submodule ℂ Hc) [Q.HasOrthogonalProjection]
    (hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQhigh : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) (alpha + delta))
    (x : (TauCeti.LinearPMap.addBounded A Hop).domain) (hx : (x : Hc) ∈ P) :
    (alpha + delta) * ‖(x : Hc)‖ ^ 2 - RCLike.re ⟪A ⟨(x : Hc), x.2⟩, (x : Hc)⟫_ℂ ≤
      (alpha + delta) * ‖Q.starProjection (x : Hc)‖ ^ 2
        - RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop
            ⟨Q.starProjection (x : Hc), hQred.projection_mem_domain x⟩,
          Q.starProjection (x : Hc)⟫_ℂ := by
  have hmain : (alpha + delta) * ‖(x : Hc)‖ ^ 2
      - RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Hc)⟫_ℂ ≤
      (alpha + delta) * ‖Q.starProjection (x : Hc)‖ ^ 2
        - RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop
            ⟨Q.starProjection (x : Hc), hQred.projection_mem_domain x⟩,
          Q.starProjection (x : Hc)⟫_ℂ :=
    theorem8_1_lowerCompressionRepulsion_unbounded hQred
      ((semiboundedBelow_reducingRestriction_iff hQred.orthogonal (alpha + delta)).mp hQhigh) x
  have hzero : ⟪Hop (x : Hc), (x : Hc)⟫_ℂ = 0 := by
    have hxperp : (x : Hc) ∈ (Pᗮ)ᗮ := by
      rw [Submodule.orthogonal_orthogonal]; exact hx
    exact (Submodule.mem_orthogonal Pᗮ (x : Hc)).mp hxperp _ (hHP _ hx)
  have hform : RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Hc)⟫_ℂ
      = RCLike.re ⟪A ⟨(x : Hc), x.2⟩, (x : Hc)⟫_ℂ := by
    rw [TauCeti.LinearPMap.addBounded_apply, inner_add_left, map_add, hzero]
    simp only [map_zero, add_zero]
    rfl
  linarith [hmain, hform]

end Complex

/-! ### Theorem 8.1 on the source's own objects, over `ℝ` -/

section Real

variable {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er]
  [CompleteSpace Er]
variable {A : Er →ₗ.[ℝ] Er} {Hop : Er →L[ℝ] Er} {P : Submodule ℝ Er}
  [P.HasOrthogonalProjection] {alpha delta : ℝ}

omit [CompleteSpace Er] [P.HasOrthogonalProjection] in
/-- The block/ambient bridge over `ℝ`, with the real inner product rather than
its real part. -/
theorem semiboundedAbove_reducingRestriction_real_iff
    {B : Er →ₗ.[ℝ] Er} {U : Submodule ℝ Er} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B U) (c : ℝ) :
    TauCeti.LinearPMap.SemiboundedAbove
        (TauCeti.LinearPMap.reducingRestriction B U hred) c ↔
      ∀ x : B.domain, (x : Er) ∈ U → ⟪B x, (x : Er)⟫_ℝ ≤ c * ‖(x : Er)‖ ^ 2 := by
  rw [semiboundedAbove_reducingRestriction_iff]
  simp only [RCLike.re_to_real]

omit [CompleteSpace Er] [P.HasOrthogonalProjection] in
/-- The block/ambient bridge over `ℝ`, lower form. -/
theorem semiboundedBelow_reducingRestriction_real_iff
    {B : Er →ₗ.[ℝ] Er} {U : Submodule ℝ Er} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B U) (c : ℝ) :
    TauCeti.LinearPMap.SemiboundedBelow
        (TauCeti.LinearPMap.reducingRestriction B U hred) c ↔
      ∀ x : B.domain, (x : Er) ∈ U → c * ‖(x : Er)‖ ^ 2 ≤ ⟪B x, (x : Er)⟫_ℝ := by
  rw [semiboundedBelow_reducingRestriction_iff]
  simp only [RCLike.re_to_real]

/-- **Davis--Kahan 1970, Theorem 8.1's printed characterization, on the source's
own blocks, at unbounded ambient scope over `ℝ`.** -/
theorem theorem8_1_maximalAngle_le_iff_blockPlacement_unbounded_real
    (hA : IsSelfAdjoint A) (hH : DavisKahan.IsSelfAdjointOperator Hop)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hPlow : TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.reducingRestriction A P hPred) alpha)
    (hPhigh : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction A Pᗮ hPred.orthogonal) (alpha + delta))
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta)
    (Q : Submodule ℝ Er) [Q.HasOrthogonalProjection]
    (hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Q) :
    TauCeti.DavisKahanExt.maximalAngle P Q ≤ Real.pi / 4 ↔
      (TauCeti.LinearPMap.SemiboundedAbove
          (TauCeti.LinearPMap.reducingRestriction
            (TauCeti.LinearPMap.addBounded A Hop) Q hQred) alpha ∧
        TauCeti.LinearPMap.SemiboundedBelow
          (TauCeti.LinearPMap.reducingRestriction
            (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal)
          (alpha + delta)) := by
  rw [semiboundedAbove_reducingRestriction_real_iff,
    semiboundedBelow_reducingRestriction_real_iff]
  exact theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded_real hA hH hPred.orthogonal
    ((semiboundedAbove_reducingRestriction_real_iff hPred alpha).mp hPlow)
    ((semiboundedBelow_reducingRestriction_real_iff hPred.orthogonal (alpha + delta)).mp hPhigh)
    hHP hHPperp hdelta Q hQred

/-- **Davis--Kahan 1970, Theorem 8.1's existence clause, on the source's own
blocks, at unbounded ambient scope over `ℝ`.** -/
theorem theorem8_1_exists_branch_blockPlacement_unbounded_real
    (hA : IsSelfAdjoint A) (hH : DavisKahan.IsSelfAdjointOperator Hop)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hPlow : TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.reducingRestriction A P hPred) alpha)
    (hPhigh : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction A Pᗮ hPred.orthogonal) (alpha + delta))
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    ∃ (Q : Submodule ℝ Er) (hQinst : Q.HasOrthogonalProjection),
      haveI := hQinst
      ∃ hQred : TauCeti.LinearPMap.ReducesSubspace
          (TauCeti.LinearPMap.addBounded A Hop) Q,
        TauCeti.LinearPMap.SemiboundedAbove
            (TauCeti.LinearPMap.reducingRestriction
              (TauCeti.LinearPMap.addBounded A Hop) Q hQred) alpha ∧
          TauCeti.LinearPMap.SemiboundedBelow
            (TauCeti.LinearPMap.reducingRestriction
              (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal)
            (alpha + delta) ∧
          TauCeti.DavisKahanExt.maximalAngle P Q ≤ Real.pi / 4 := by
  obtain ⟨hred, hlow, hhigh, hangle⟩ :=
    theorem8_1_canonicalBranchUnbounded_printed_real (A := A) (Hop := Hop) (P := P)
      (alpha := alpha) (delta := delta) hA hH hPred.orthogonal
      ((semiboundedAbove_reducingRestriction_real_iff hPred alpha).mp hPlow)
      ((semiboundedBelow_reducingRestriction_real_iff hPred.orthogonal (alpha + delta)).mp
        hPhigh)
      hHP hHPperp hdelta
  refine ⟨canonicalLowBranchUnboundedReal
    (DavisKahan.addBounded_isSelfAdjoint A hA Hop hH) alpha, _, hred, ?_, ?_, hangle⟩
  · exact (semiboundedAbove_reducingRestriction_real_iff hred alpha).mpr hlow
  · exact (semiboundedBelow_reducingRestriction_real_iff hred.orthogonal (alpha + delta)).mpr
      hhigh

omit [CompleteSpace Er] [P.HasOrthogonalProjection] in
/-- **Davis--Kahan 1970, Theorem 8.1 part (i), upper block, on the source's own
objects, at unbounded ambient scope over `ℝ`.** -/
theorem theorem8_1_upperCompressionRepulsion_sourceExact_unbounded_real
    (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (Q : Submodule ℝ Er) [Q.HasOrthogonalProjection]
    (hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQlow : TauCeti.LinearPMap.SemiboundedAbove
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred) alpha)
    (x : (TauCeti.LinearPMap.addBounded A Hop).domain) (hx : (x : Er) ∈ Pᗮ) :
    ⟪A ⟨(x : Er), x.2⟩, (x : Er)⟫_ℝ - alpha * ‖(x : Er)‖ ^ 2 ≤
      ⟪TauCeti.LinearPMap.addBounded A Hop
          ⟨Qᗮ.starProjection (x : Er), hQred.orthogonalProjection_mem_domain x⟩,
        Qᗮ.starProjection (x : Er)⟫_ℝ
        - alpha * ‖Qᗮ.starProjection (x : Er)‖ ^ 2 := by
  have hmain : ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ
      - alpha * ‖(x : Er)‖ ^ 2 ≤
      ⟪TauCeti.LinearPMap.addBounded A Hop
          ⟨Qᗮ.starProjection (x : Er), hQred.orthogonalProjection_mem_domain x⟩,
        Qᗮ.starProjection (x : Er)⟫_ℝ
        - alpha * ‖Qᗮ.starProjection (x : Er)‖ ^ 2 :=
    theorem8_1_upperCompressionRepulsion_unbounded_real hQred
      ((semiboundedAbove_reducingRestriction_real_iff hQred alpha).mp hQlow) x
  have hzero : ⟪Hop (x : Er), (x : Er)⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal P (x : Er)).mp hx _ (hHPperp _ hx)
  have hform : ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ
      = ⟪A ⟨(x : Er), x.2⟩, (x : Er)⟫_ℝ := by
    rw [TauCeti.LinearPMap.addBounded_apply, inner_add_left, hzero]
    simp only [add_zero]
    rfl
  linarith [hmain, hform]

omit [CompleteSpace Er] in
/-- **Davis--Kahan 1970, Theorem 8.1 part (i), lower block, on the source's own
objects, at unbounded ambient scope over `ℝ`.** -/
theorem theorem8_1_lowerCompressionRepulsion_sourceExact_unbounded_real
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ)
    (Q : Submodule ℝ Er) [Q.HasOrthogonalProjection]
    (hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQhigh : TauCeti.LinearPMap.SemiboundedBelow
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) (alpha + delta))
    (x : (TauCeti.LinearPMap.addBounded A Hop).domain) (hx : (x : Er) ∈ P) :
    (alpha + delta) * ‖(x : Er)‖ ^ 2 - ⟪A ⟨(x : Er), x.2⟩, (x : Er)⟫_ℝ ≤
      (alpha + delta) * ‖Q.starProjection (x : Er)‖ ^ 2
        - ⟪TauCeti.LinearPMap.addBounded A Hop
            ⟨Q.starProjection (x : Er), hQred.projection_mem_domain x⟩,
          Q.starProjection (x : Er)⟫_ℝ := by
  have hmain : (alpha + delta) * ‖(x : Er)‖ ^ 2
      - ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ ≤
      (alpha + delta) * ‖Q.starProjection (x : Er)‖ ^ 2
        - ⟪TauCeti.LinearPMap.addBounded A Hop
            ⟨Q.starProjection (x : Er), hQred.projection_mem_domain x⟩,
          Q.starProjection (x : Er)⟫_ℝ :=
    theorem8_1_lowerCompressionRepulsion_unbounded_real hQred
      ((semiboundedBelow_reducingRestriction_real_iff hQred.orthogonal (alpha + delta)).mp
        hQhigh) x
  have hzero : ⟪Hop (x : Er), (x : Er)⟫_ℝ = 0 := by
    have hxperp : (x : Er) ∈ (Pᗮ)ᗮ := by
      rw [Submodule.orthogonal_orthogonal]; exact hx
    exact (Submodule.mem_orthogonal Pᗮ (x : Er)).mp hxperp _ (hHP _ hx)
  have hform : ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ
      = ⟪A ⟨(x : Er), x.2⟩, (x : Er)⟫_ℝ := by
    rw [TauCeti.LinearPMap.addBounded_apply, inner_add_left, hzero]
    simp only [add_zero]
    rfl
  linarith [hmain, hform]

end Real

end

end Section8
end DavisKahan1970
end TauCeti
