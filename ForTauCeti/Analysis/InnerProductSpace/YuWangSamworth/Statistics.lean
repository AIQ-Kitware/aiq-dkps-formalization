/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
import ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Residual
import ForTauCeti.Analysis.InnerProductSpace.AlignedBasis

/-!
# Population-gap and statistical Davis--Kahan variants

Literature map:

* `prose/core-arguments/Yu-Wang-Samworth-2014-core-arguments.tex`, all sections.
* `papers/DavisKahan-formalized-vs-literature.tex`, paragraphs
  "Hoffman--Wielandt and the exact YWS theorem" and
  "The aligned-basis (Procrustes) bound".

This file gives the existing YWS results a canonical subspace-facing API and
records the full interval-block, aligned-basis, and single-vector surfaces.

## Provenance

*Moved, not restated.*  This file was `DavisKahan/Specialized/Statistics.lean`
before the last three `DavisKahan` modules of
the Yu--Wang--Samworth payload into the staging layer, finishing Y3.  Statements,
proofs, signatures and namespaces are unchanged; the declarations already lived
in `TauCeti.*`.

Y3(b2)/(b3)/(b4) are what made it possible: they took the sin-Θ perturbation
closure this file rests on out of `ForMathlib` and `DavisKahan` entirely, so the
last edge to sever was this one.

-/

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

/-- Population-only gap around a selected spectral set. -/
def PopulationGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Δ : ℝ) : Prop :=
  InternalGap A U Δ

/-- `U` and `V` are spectral blocks with the same ordered eigenvalue indices
for `A` and `B`.  This is the finite branch-selection datum used by the
Yu--Wang--Samworth population-gap theorem. -/
def CorrespondingEigenblock {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ (n : ℕ) (hn : finrank 𝕜 E = n) (s : Finset (Fin n)),
    U = (hA.eigenvectorBasis hn).spanIndices ↑s ∧
      V = (hB.eigenvectorBasis hn).spanIndices ↑s

/-- Frobenius sine distance in canonical subspace notation. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  UnitarilyInvariantNorm.frobenius 𝕜 E (sinThetaMap U V)

/-- **The complement identity.**  The canonical Frobenius sine of two equally
indexed eigenblocks is exactly the square root of the cross-block overlap sum
used by Yu--Wang--Samworth: in the paper's matrix notation,
`‖V₁ᵀ V̂‖_F = ‖sin Θ(V̂, V)‖_F`.

Public, and deliberately so.  It was `private` until 2026-07-29, which made this
the one Yu--Wang--Samworth result the repository proved and no reader could
cite — recorded as item `YWS-S1-complement-identity`.  Every bound in that paper
is proved as a statement about cross-block energy and read back as an angle, so
this is the bridge the whole development turns on and it belongs in the API. -/
theorem sinThetaFrobenius_eq_sqrt_sum_cross {n : ℕ}
    (bT bS : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n)) :
    sinThetaFrobenius
        (Submodule.span 𝕜 (bT '' (↑s : Set (Fin n))))
        (Submodule.span 𝕜 (bS '' (↑s : Set (Fin n)))) =
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bT k, bS j⟫_𝕜‖ ^ 2) := by
  classical
  let U : Submodule 𝕜 E := Submodule.span 𝕜 (bT '' (↑s : Set (Fin n)))
  let V : Submodule 𝕜 E := Submodule.span 𝕜 (bS '' (↑s : Set (Fin n)))
  have hn : finrank 𝕜 E = n := by
    rw [Module.finrank_eq_card_basis bT.toBasis, Fintype.card_fin]
  rw [sinThetaFrobenius, UnitarilyInvariantNorm.frobenius_apply 𝕜 E _ hn bT]
  congr 1
  have hcol : ∀ i : Fin n,
      ‖sinThetaMap U V (bT i)‖ ^ 2 =
        if i ∈ s then ∑ k ∈ sᶜ, ‖⟪bS k, bT i⟫_𝕜‖ ^ 2 else 0 := by
    intro i
    rw [sinThetaMap, LinearMap.comp_apply]
    -- `rw [sinThetaMap, LinearMap.comp_apply]` leaves the composition applied but
    -- not in the two-projection form the `hproj` rewrite below matches.
    change ‖Vᗮ.starProjection (U.starProjection (bT i))‖ ^ 2 = _
    have hproj : U.starProjection (bT i) = if i ∈ s then bT i else 0 := by
      simpa [U] using
        Orthonormal.starProjection_span_image_apply_self bT.orthonormal s i
    rw [hproj]
    split_ifs with hi
    · rw [Submodule.starProjection_orthogonal_val]
      simpa [V] using
        OrthonormalBasis.norm_sq_sub_starProjection_span_image bS s (bT i)
    · simp
  calc
    ∑ i, ‖sinThetaMap U V (bT i)‖ ^ 2
        = ∑ i, if i ∈ s then ∑ k ∈ sᶜ, ‖⟪bS k, bT i⟫_𝕜‖ ^ 2 else 0 :=
          Finset.sum_congr rfl fun i _ => hcol i
    _ = ∑ i ∈ s, ∑ k ∈ sᶜ, ‖⟪bS k, bT i⟫_𝕜‖ ^ 2 := by simp
    _ = ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bT k, bS j⟫_𝕜‖ ^ 2 := by
      rw [← sinThetaSq_blockFamily_eq_sum_cross bS bT rfl rfl,
        sinThetaSq_comm,
        sinThetaSq_blockFamily_eq_sum_cross bT bS rfl rfl]

/-- Exact Yu--Wang--Samworth population-gap theorem.

Signature audit: `hcorr` now fixes the perturbed block by the same ordered eigenvalue indices;
this excludes arbitrary reducing subspaces when `B=A`.

Related Lean work: `YuanheZ/lean-stat-learning-theory` proves operator-norm
eigenvector and spectral-projection DK endpoints in `SLT/MatrixInfra/Perturb.lean`.
Those results provide an independent check of the gap/perturbation mechanism but
do not include the YWS Frobenius minimum, population-gap residual sandwich, or
aligned-basis conclusion proved here.
-/
theorem yuWangSamworth_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (_hU : IsInvariant A U) (_hV : IsInvariant B V)
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  classical
  obtain ⟨n, hn, s, rfl, rfl⟩ := hcorr
  have hcard : s.card = d := by
    rw [← hrank, (hA.eigenvectorBasis hn).finrank_spanIndices]
  have hindexGap : ∀ j ∈ s, ∀ k ∉ s,
      Δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k| := by
    intro j hj k hk
    apply hgap (hA.eigenvalues hn j) (hA.eigenvalues hn k)
    · refine ⟨hA.eigenvectorBasis hn j, ?_, ?_, hA.apply_eigenvectorBasis hn j⟩
      · rw [OrthonormalBasis.spanIndices]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      · exact (hA.eigenvectorBasis hn).orthonormal.ne_zero j
    · refine ⟨hA.eigenvectorBasis hn k, ?_, ?_, hA.apply_eigenvectorBasis hn k⟩
      · rw [OrthonormalBasis.orthogonal_spanIndices, OrthonormalBasis.spanIndices]
        apply Submodule.subset_span
        refine ⟨k, ?_, rfl⟩
        simpa using hk
      · exact (hA.eigenvectorBasis hn).orthonormal.ne_zero k
  have hsine : sinThetaFrobenius
      ((hA.eigenvectorBasis hn).spanIndices ↑s)
      ((hB.eigenvectorBasis hn).spanIndices ↑s) =
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2) := by
    simpa only [OrthonormalBasis.spanIndices] using
      (sinThetaFrobenius_eq_sqrt_sum_cross
        (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn) s)
  rw [hsine]
  have hopBound :
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
        ≤ 2 * (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖) / Δ := by
    have hop := sq_gap_mul_sum_cross_le_of_population_gap_opNorm
      hA hB hn s hΔ.le hindexGap
      (ε := ‖(B - A).toContinuousLinearMap‖)
      (fun x => by
        have hx := (B - A).toContinuousLinearMap.le_opNorm x
        rwa [LinearMap.coe_toContinuousLinearMap'] at hx)
    have hover0 : 0 ≤ ∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
    have hsq :
        (Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
          ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2) * Δ) ^ 2
          ≤ (2 * Real.sqrt d * ‖(B - A).toContinuousLinearMap‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hover0, mul_pow, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg d)]
      rw [hcard] at hop
      nlinarith
    rw [le_div_iff₀ hΔ]
    have hleft : 0 ≤ Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2) * Δ := by
      positivity
    have hright : 0 ≤ 2 * (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖) := by
      positivity
    nlinarith [hsq]
  have hfrobBound :
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2)
        ≤ 2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) / Δ := by
    have hfrob := sqrt_sum_cross_le_of_population_gap hA hB hn s hΔ hindexGap
    rw [UnitarilyInvariantNorm.frobenius_apply 𝕜 E (B - A) hn
      (hA.eigenvectorBasis hn)]
    exact hfrob
  rcases le_total (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
      (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) with hle | hle
  · rw [min_eq_left hle]
    exact hopBound
  · rw [min_eq_right hle]
    exact hfrobBound

/-- A spectral subspace of an eigenbasis reduces the operator: it is spanned by
eigenvectors, each of which maps to a scalar multiple of itself. -/
theorem reduces_spanIndices {n : ℕ} {B : E →ₗ[𝕜] E} (hB : B.IsSymmetric)
    (hn : finrank 𝕜 E = n) (s : Set (Fin n)) :
    IsInvariant B ((hB.eigenvectorBasis hn).spanIndices s) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, hip, rfl⟩
    rw [hB.apply_eigenvectorBasis hn i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hip, rfl⟩)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Arbitrary contiguous population eigenblock.

Signature audit: `hUeq` records the population interval while `hcorr` selects the perturbed
block by ordered indices, so eigenvalue drift across the numerical interval does not change the
branch.
-/
theorem yuWangSamworth_intervalBlock_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    {a b Δ : ℝ} (hΔ : 0 < Δ)
    (hUeq : U = spectralSubspace A (Set.Icc a b))
    (hcorr : CorrespondingEigenblock hA hB U V)
    (hgap : InternalGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt (finrank 𝕜 U) * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  obtain ⟨n, hn, s, -, hVp⟩ := id hcorr
  refine yuWangSamworth_sinTheta_le hA hB ?_ ?_ hcorr rfl hΔ hgap
  · rw [hUeq]; exact isInvariant_spectralSubspace A (Set.Icc a b)
  · rw [hVp]; exact reduces_spanIndices hB hn ↑s

/-- The family-level squared sine agrees with the canonical Frobenius
sine whenever the two orthonormal families span the supplied subspaces. -/
theorem sinThetaSq_eq_sinThetaFrobenius_sq_of_spans
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hspanU : Submodule.span 𝕜 (Set.range u) = U)
    (hspanV : Submodule.span 𝕜 (Set.range v) = V) :
    sinThetaSq hu hv = sinThetaFrobenius U V ^ 2 := by
  classical
  subst U
  subst V
  let n := finrank 𝕜 E
  have hspanrank : finrank 𝕜 (Submodule.span 𝕜 (Set.range u)) = d := by
    rw [finrank_span_eq_card hu.linearIndependent, Fintype.card_fin]
  have hdn : d ≤ n := by
    have hle := Submodule.finrank_le (Submodule.span 𝕜 (Set.range u))
    rw [hspanrank] at hle
    simpa only [n] using hle
  let e : Fin d ↪ Fin n := Fin.castLEEmb hdn
  let S : Set (Fin n) := Set.range e
  let uExt : Fin n → E := Function.extend e u (fun _ => 0)
  let vExt : Fin n → E := Function.extend e v (fun _ => 0)
  have huS : Orthonormal 𝕜 (S.restrict uExt) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    rcases hi with ⟨i', rfl⟩
    rcases hj with ⟨j', rfl⟩
    -- After `orthonormal_iff_ite` the goal is phrased through the subtype (or
    -- `Fin.cast`) coercion; `orthonormal_iff_ite.mp` is stated for the underlying
    -- vectors, so the coercion has to be discharged before it can apply.
    change ⟪uExt (e i'), uExt (e j')⟫_𝕜 =
      if (⟨e i', ⟨i', rfl⟩⟩ : S) = ⟨e j', ⟨j', rfl⟩⟩ then 1 else 0
    have hui : uExt (e i') = u i' :=
      e.injective.extend_apply u (fun _ => 0) i'
    have huj : uExt (e j') = u j' :=
      e.injective.extend_apply u (fun _ => 0) j'
    rw [hui, huj, orthonormal_iff_ite.mp hu i' j']
    simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
  have hvS : Orthonormal 𝕜 (S.restrict vExt) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    rcases hi with ⟨i', rfl⟩
    rcases hj with ⟨j', rfl⟩
    -- After `orthonormal_iff_ite` the goal is phrased through the subtype (or
    -- `Fin.cast`) coercion; `orthonormal_iff_ite.mp` is stated for the underlying
    -- vectors, so the coercion has to be discharged before it can apply.
    change ⟪vExt (e i'), vExt (e j')⟫_𝕜 =
      if (⟨e i', ⟨i', rfl⟩⟩ : S) = ⟨e j', ⟨j', rfl⟩⟩ then 1 else 0
    have hvi : vExt (e i') = v i' :=
      e.injective.extend_apply v (fun _ => 0) i'
    have hvj : vExt (e j') = v j' :=
      e.injective.extend_apply v (fun _ => 0) j'
    rw [hvi, hvj, orthonormal_iff_ite.mp hv i' j']
    simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
  have hncard : finrank 𝕜 E = Fintype.card (Fin n) := by simp [n]
  obtain ⟨bU, hbU⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq hncard huS
  obtain ⟨bV, hbV⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq hncard hvS
  let s : Finset (Fin n) := Finset.univ.map e
  have hscard : s.card = d := by simp [s]
  have hbUe (i : Fin d) : bU (e i) = u i := by
    rw [hbU (e i) ⟨i, rfl⟩]
    exact e.injective.extend_apply u (fun _ => 0) i
  have hbVe (i : Fin d) : bV (e i) = v i := by
    rw [hbV (e i) ⟨i, rfl⟩]
    exact e.injective.extend_apply v (fun _ => 0) i
  have himageU : bU '' (↑s : Set (Fin n)) = Set.range u := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_coe, Finset.mem_map] at hj
      obtain ⟨i, -, rfl⟩ := hj
      exact ⟨i, (hbUe i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [s], hbUe i⟩
  have himageV : bV '' (↑s : Set (Fin n)) = Set.range v := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_coe, Finset.mem_map] at hj
      obtain ⟨i, -, rfl⟩ := hj
      exact ⟨i, (hbVe i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp [s], hbVe i⟩
  let uBlock : Fin d → E := blockFamily bU s hscard
  let vBlock : Fin d → E := blockFamily bV s hscard
  have huBlock : Orthonormal 𝕜 uBlock := orthonormal_blockFamily bU s hscard
  have hvBlock : Orthonormal 𝕜 vBlock := orthonormal_blockFamily bV s hscard
  have hspanUBlock : Submodule.span 𝕜 (Set.range uBlock) =
      Submodule.span 𝕜 (Set.range u) := by
    have hrangeU : Set.range uBlock = bU '' (↑s : Set (Fin n)) :=
      range_blockFamily bU s hscard
    rw [hrangeU, himageU]
  have hspanVBlock : Submodule.span 𝕜 (Set.range vBlock) =
      Submodule.span 𝕜 (Set.range v) := by
    have hrangeV : Set.range vBlock = bV '' (↑s : Set (Fin n)) :=
      range_blockFamily bV s hscard
    rw [hrangeV, himageV]
  have hcosUV := principalCosines_span_eq_cosPrincipalAngles hu hv
  have hcosBlock := principalCosines_span_eq_cosPrincipalAngles huBlock hvBlock
  have hcosBlock' :
      principalCosines (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) =
        cosPrincipalAngles huBlock hvBlock := by
    simpa only [hspanUBlock, hspanVBlock] using hcosBlock
  have hcos : cosPrincipalAngles hu hv = cosPrincipalAngles huBlock hvBlock :=
    hcosUV.symm.trans hcosBlock'
  have hsq : sinThetaSq hu hv =
      ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bU k, bV j⟫_𝕜‖ ^ 2 := by
    calc
      sinThetaSq hu hv = sinThetaSq huBlock hvBlock := by
        unfold sinThetaSq
        rw [hcos]
      _ = ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bU k, bV j⟫_𝕜‖ ^ 2 :=
        sinThetaSq_blockFamily_eq_sum_cross bU bV hscard hscard
  have hfrob :
      sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) =
        Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bU k, bV j⟫_𝕜‖ ^ 2) := by
    simpa only [himageU, himageV] using
      (sinThetaFrobenius_eq_sqrt_sum_cross bU bV s)
  have hnonneg : 0 ≤ ∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bU k, bV j⟫_𝕜‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hfrob, Real.sq_sqrt hnonneg, hsq]

/-- Procrustes-aligned orthonormal bases. -/
theorem exists_aligned_orthonormalBasis
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {d : ℕ}
    (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      ∑ i, ‖v i - u i‖ ^ 2 ≤ 2 * sinThetaFrobenius U V ^ 2 := by
  classical
  let bU := stdOrthonormalBasis 𝕜 U
  let bV := stdOrthonormalBasis 𝕜 V
  let u : Fin d → E := fun i => ((bU (Fin.cast hrankU.symm i) : U) : E)
  let v0 : Fin d → E := fun i => ((bV (Fin.cast hrankV.symm i) : V) : E)
  have hu : Orthonormal 𝕜 u := by
    rw [orthonormal_iff_ite]
    intro i j
    -- After `orthonormal_iff_ite` the goal is phrased through the subtype (or
    -- `Fin.cast`) coercion; `orthonormal_iff_ite.mp` is stated for the underlying
    -- vectors, so the coercion has to be discharged before it can apply.
    change ⟪bU (Fin.cast hrankU.symm i), bU (Fin.cast hrankU.symm j)⟫_𝕜 =
      if i = j then 1 else 0
    rw [orthonormal_iff_ite.mp bU.orthonormal]
    simp only [Fin.cast_inj]
  have hv0 : Orthonormal 𝕜 v0 := by
    rw [orthonormal_iff_ite]
    intro i j
    -- After `orthonormal_iff_ite` the goal is phrased through the subtype (or
    -- `Fin.cast`) coercion; `orthonormal_iff_ite.mp` is stated for the underlying
    -- vectors, so the coercion has to be discharged before it can apply.
    change ⟪bV (Fin.cast hrankV.symm i), bV (Fin.cast hrankV.symm j)⟫_𝕜 =
      if i = j then 1 else 0
    rw [orthonormal_iff_ite.mp bV.orthonormal]
    simp only [Fin.cast_inj]
  have hspanU : Submodule.span 𝕜 (Set.range u) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (bU (Fin.cast hrankU.symm i)).2
    · rw [finrank_span_eq_card hu.linearIndependent, Fintype.card_fin, hrankU]
  have hspanV0 : Submodule.span 𝕜 (Set.range v0) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (bV (Fin.cast hrankV.symm i)).2
    · rw [finrank_span_eq_card hv0.linearIndependent, Fintype.card_fin, hrankV]
  let O := choosePolarUnitary (overlapOp hu hv0)
  let v : Fin d → E := fun i =>
    familyIsometry hv0 (O.symm (EuclideanSpace.single i 1))
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change
      ⟪familyIsometry hv0 (O.symm (EuclideanSpace.single i (1 : 𝕜))),
        familyIsometry hv0 (O.symm (EuclideanSpace.single j (1 : 𝕜)))⟫_𝕜 =
          if i = j then 1 else 0
    rw [(familyIsometry hv0).inner_map_map, O.symm.inner_map_map]
    exact orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j
  have hspanV : Submodule.span 𝕜 (Set.range v) = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi := familyIsometry_mem_span hv0
        (O.symm (EuclideanSpace.single i 1))
      rw [hspanV0] at hi
      exact hi
    · rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin, hrankV]
  have hsum := sum_sq_norm_aligned_le_sinThetaSq hu hv0
  have hbridge := sinThetaSq_eq_sinThetaFrobenius_sq_of_spans
    hu hv0 hspanU hspanV0
  refine ⟨u, v, hu, hv, hspanU, hspanV, ?_⟩
  simpa only [v, O, hbridge] using hsum

/-- YWS aligned-basis perturbation bound.

Signature audit: The aligned-basis theorem now inherits the same `hcorr` branch selection as
the sine-distance theorem.
-/
theorem yuWangSamworth_alignedBasis_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : PopulationGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  obtain ⟨u, v, hu, hv, hspanU, hspanV, hsum⟩ :=
    exists_aligned_orthonormalBasis hrankU hrankV
  refine ⟨u, v, hu, hv, hspanU, hspanV, ?_⟩
  have hsine := yuWangSamworth_sinTheta_le hA hB hU hV hcorr hrankU hΔ hgap
  have hsnn : (0 : ℝ) ≤ sinThetaFrobenius U V :=
    (UnitarilyInvariantNorm.frobenius 𝕜 E).nonneg _
  calc Real.sqrt (∑ i, ‖v i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * sinThetaFrobenius U V ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * sinThetaFrobenius U V := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 * (2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = 2 * Real.sqrt 2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by ring

omit [FiniteDimensional 𝕜 E] in
/-- **The span of an eigenvector is invariant.**  If `A u = lam • u` then every
scalar multiple of `u` is sent to a scalar multiple of `u`. -/
private theorem isInvariant_span_singleton_of_apply_eq_smul
    {A : E →ₗ[𝕜] E} {u : E} {lam : ℝ} (hAu : A u = (lam : 𝕜) • u) :
    IsInvariant A (Submodule.span 𝕜 {u}) := by
  intro x hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [map_smul, hAu]
  exact Submodule.smul_mem _ _
    (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))

omit [FiniteDimensional 𝕜 E] in
/-- **A unit vector spanning the same line as an orthonormal vector differs from
it by a unit scalar.**  If `f` is orthonormal, `f 0` lies in `span {u}` and
`‖u‖ = 1`, the scalar `α` with `α • u = f 0` satisfies `‖α‖ = 1`. -/
private theorem exists_unit_smul_eq_of_mem_span_singleton
    {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hmem : w ∈ Submodule.span 𝕜 {u}) :
    ∃ α : 𝕜, ‖α‖ = 1 ∧ α • u = w := by
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨α, hα⟩ := hmem
  refine ⟨α, ?_, hα⟩
  have h := hw
  rw [← hα, norm_smul, hu, mul_one] at h
  exact h

/-- Rank-one/sign-aligned eigenvector corollary.

Signature audit: The rank-one `hcorr` premise selects `v` from the corresponding ordered
perturbed eigenline rather than an arbitrary eigenvector of `B`.

Related formalization: `facebookresearch/atlas-lean`,
`Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean`, contains a
real-matrix leading-eigenvector DK endpoint for a spiked covariance model, and
`Cor_4_9.lean` applies it to PCA.  That source is recorded only for statement
comparison because its repository terms are not compatible with vendoring here.
-/
theorem yuWangSamworth_eigenvector_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {lam μ Δ : ℝ} (hAu : A u = (lam : 𝕜) • u)
    (hBv : B v = (μ : 𝕜) • v)
    (hcorr : CorrespondingEigenblock hA hB
      (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}))
    (hΔ : 0 < Δ)
    (hgap : ∀ ν ∈ restrictedSpectrum A (Submodule.span 𝕜 {u})ᗮ,
      Δ ≤ |lam - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  have hu0 : u ≠ 0 := by rw [← norm_ne_zero_iff, hu]; norm_num
  have hv0 : v ≠ 0 := by rw [← norm_ne_zero_iff, hv]; norm_num
  -- The eigenlines reduce the operators.
  have hU : IsInvariant A (Submodule.span 𝕜 {u}) :=
    isInvariant_span_singleton_of_apply_eq_smul hAu
  have hV : IsInvariant B (Submodule.span 𝕜 {v}) :=
    isInvariant_span_singleton_of_apply_eq_smul hBv
  have hrankU : finrank 𝕜 (Submodule.span 𝕜 {u}) = 1 := finrank_span_singleton hu0
  have hrankV : finrank 𝕜 (Submodule.span 𝕜 {v}) = 1 := finrank_span_singleton hv0
  -- The restricted spectrum of `A` on the eigenline is exactly `{lam}`, so the internal
  -- gap follows from `hgap`.
  have hgap' : PopulationGap A (Submodule.span 𝕜 {u}) Δ := by
    intro l ν hl hν
    obtain ⟨x, hxU, hx0, hAx⟩ := hl
    rw [Submodule.mem_span_singleton] at hxU
    obtain ⟨a, rfl⟩ := hxU
    have heq : (lam : 𝕜) • (a • u) = (l : 𝕜) • (a • u) := by
      rw [smul_comm, ← hAu, ← map_smul]; exact hAx
    have hll : lam = l := by
      by_contra hne
      have hz : ((lam : 𝕜) - (l : 𝕜)) • (a • u) = 0 := by rw [sub_smul, heq, sub_self]
      rcases smul_eq_zero.mp hz with h | h
      · exact hne (by exact_mod_cast sub_eq_zero.mp h)
      · exact hx0 h
    rw [← hll]; exact hgap ν hν
  obtain ⟨u', v', hu'on, hv'on, hspanU, hspanV, hbound⟩ :=
    yuWangSamworth_alignedBasis_le hA hB hU hV hcorr hrankU hrankV hΔ hgap'
  -- Extract the unit scalars relating the aligned basis vectors to `u`, `v`.
  have hu'mem : u' 0 ∈ Submodule.span 𝕜 {u} := hspanU ▸ Submodule.subset_span ⟨0, rfl⟩
  have hv'mem : v' 0 ∈ Submodule.span 𝕜 {v} := hspanV ▸ Submodule.subset_span ⟨0, rfl⟩
  obtain ⟨α, hαnorm, hα⟩ :=
    exists_unit_smul_eq_of_mem_span_singleton hu (hu'on.norm_eq_one 0) hu'mem
  obtain ⟨β, hβnorm, hβ⟩ :=
    exists_unit_smul_eq_of_mem_span_singleton hv (hv'on.norm_eq_one 0) hv'mem
  have hα0 : α ≠ 0 := by rw [← norm_ne_zero_iff, hαnorm]; norm_num
  refine ⟨β * α⁻¹, by rw [norm_mul, norm_inv, hαnorm, hβnorm]; norm_num, ?_⟩
  -- `‖(βα⁻¹) v - u‖ = ‖v' 0 - u' 0‖`, then use the aligned-basis bound.
  have hαv : α • ((β * α⁻¹) • v) = v' 0 := by
    rw [smul_smul, mul_comm β α⁻¹, ← mul_assoc, mul_inv_cancel₀ hα0, one_mul, hβ]
  have key : ‖(β * α⁻¹) • v - u‖ = ‖v' 0 - u' 0‖ := by
    have hsub : α • ((β * α⁻¹) • v - u) = v' 0 - u' 0 := by rw [smul_sub, hαv, hα]
    calc ‖(β * α⁻¹) • v - u‖
        = ‖α‖ * ‖(β * α⁻¹) • v - u‖ := by rw [hαnorm, one_mul]
      _ = ‖α • ((β * α⁻¹) • v - u)‖ := by rw [norm_smul]
      _ = ‖v' 0 - u' 0‖ := by rw [hsub]
  have hsum1 : Real.sqrt (∑ i : Fin 1, ‖v' i - u' i‖ ^ 2) = ‖v' 0 - u' 0‖ := by
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
  rw [key, ← hsum1]
  refine hbound.trans ?_
  have hmin : min (Real.sqrt (↑(1 : ℕ)) * ‖(B - A).toContinuousLinearMap‖)
      (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A))
      ≤ ‖(B - A).toContinuousLinearMap‖ :=
    (min_le_left _ _).trans_eq (by rw [Nat.cast_one, Real.sqrt_one, one_mul])
  gcongr

end TauCeti
