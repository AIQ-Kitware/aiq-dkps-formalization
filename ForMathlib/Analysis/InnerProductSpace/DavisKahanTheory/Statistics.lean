/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.SinTheta
import ForMathlib.Analysis.InnerProductSpace.YuWangSamworth
import ForMathlib.Analysis.InnerProductSpace.AlignedBasis

/-!
# Population-gap and statistical Davis--Kahan variants

Literature map:

* `ForMathlib/prose/Yu-Wang-Samworth-2014-core-arguments.tex`, all sections.
* `papers/DavisKahan-formalized-vs-literature.tex`, paragraphs
  "Hoffman--Wielandt and the exact YWS theorem" and
  "The aligned-basis (Procrustes) bound".

This file gives the existing YWS results a canonical subspace-facing API and
records the full interval-block, aligned-basis, and single-vector surfaces.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Population-only gap around a selected spectral set. -/
def PopulationGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Δ : ℝ) : Prop :=
  InternalGap A U Δ

/-- `U` and `V` are spectral blocks with the same ordered eigenvalue indices
for `A` and `B`.  This is the finite branch-selection datum used by the
Yu--Wang--Samworth population-gap theorem. -/
def CorrespondingEigenblock {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ (n : ℕ) (hn : finrank 𝕜 E = n) (p : Fin n → Prop),
    U = specSubspace (hA.eigenvectorBasis hn) p ∧
      V = specSubspace (hB.eigenvectorBasis hn) p

/-- Frobenius sine distance in canonical subspace notation. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  UnitarilyInvariantNorm.frobenius 𝕜 E (sinThetaMap U V)

private theorem specSubspace_eq_span_filter {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) [DecidablePred p] :
    specSubspace b p =
      Submodule.span 𝕜 (b '' (↑(Finset.univ.filter p) : Set (Fin n))) := by
  unfold specSubspace
  congr 1
  ext x
  simp

/-- The canonical Frobenius sine of two equally indexed eigenblocks is exactly
    the square root of the cross-block overlap sum used by Yu--Wang--Samworth. -/
private theorem sinThetaFrobenius_eq_sqrt_sum_cross {n : ℕ}
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
    change ‖Vᗮ.starProjection (U.starProjection (bT i))‖ ^ 2 = _
    rw [show U.starProjection (bT i) = if i ∈ s then bT i else 0 by
      simpa [U] using
        Orthonormal.starProjection_span_image_apply_self bT.orthonormal s i]
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

Lean proof route for a weaker agent:

1. After replacing arbitrary `V` by the corresponding ordered eigenblock of `B`, reuse the existing `YuWangSamworth.lean` theorem and bridge its eigenbasis/block notation to `sinThetaFrobenius`.
2. Unpack `hcorr` to obtain one eigenbasis index predicate shared by `A` and `B`.
3. Apply the existing YWS theorem and rewrite its block Frobenius quantity as `sinThetaFrobenius`.

Signature audit: `hcorr` now fixes the perturbed block by the same ordered eigenvalue indices;
this excludes arbitrary reducing subspaces when `B=A`.
-/
theorem yuWangSamworth_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (_hU : Reduces A U) (_hV : Reduces B V)
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : PopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantNorm.frobenius 𝕜 E (B - A)) / Δ := by
  classical
  obtain ⟨n, hn, p, rfl, rfl⟩ := hcorr
  let s : Finset (Fin n) := Finset.univ.filter p
  have hcard : s.card = d := by
    rw [← hrank, finrank_specSubspace]
  have hindexGap : ∀ j ∈ s, ∀ k ∉ s,
      Δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k| := by
    intro j hj k hk
    apply hgap (hA.eigenvalues hn j) (hA.eigenvalues hn k)
    · refine ⟨hA.eigenvectorBasis hn j, ?_, ?_, hA.apply_eigenvectorBasis hn j⟩
      · rw [specSubspace_eq_span_filter]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      · exact (hA.eigenvectorBasis hn).orthonormal.ne_zero j
    · refine ⟨hA.eigenvectorBasis hn k, ?_, ?_, hA.apply_eigenvectorBasis hn k⟩
      · rw [orthogonal_specSubspace, specSubspace_eq_span_filter]
        apply Submodule.subset_span
        refine ⟨k, ?_, rfl⟩
        simpa [s] using hk
      · exact (hA.eigenvectorBasis hn).orthonormal.ne_zero k
  have hsine : sinThetaFrobenius
      (specSubspace (hA.eigenvectorBasis hn) p)
      (specSubspace (hB.eigenvectorBasis hn) p) =
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ,
        ‖⟪hA.eigenvectorBasis hn k, hB.eigenvectorBasis hn j⟫_𝕜‖ ^ 2) := by
    simpa only [specSubspace_eq_span_filter] using
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
theorem reduces_specSubspace {n : ℕ} {B : E →ₗ[𝕜] E} (hB : B.IsSymmetric)
    (hn : finrank 𝕜 E = n) (p : Fin n → Prop) :
    Reduces B (specSubspace (hB.eigenvectorBasis hn) p) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    rw [hB.apply_eigenvectorBasis hn (i : Fin n)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Arbitrary contiguous population eigenblock.

Lean proof route for a weaker agent:

1. Restate using contiguous eigenvalue indices (or a continued contour-selected branch), then apply the preceding YWS theorem with the population gap formed by the adjacent eigenvalues.
2. Rewrite `U` using `hUeq` and unpack `hcorr` to identify the corresponding perturbed block.
3. Apply `yuWangSamworth_sinTheta_le` with `d = finrank 𝕜 U`.

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
  obtain ⟨n, hn, p, -, hVp⟩ := id hcorr
  refine yuWangSamworth_sinTheta_le hA hB ?_ ?_ hcorr rfl hΔ hgap
  · rw [hUeq]; exact reduces_spectralSubspace A (Set.Icc a b)
  · rw [hVp]; exact reduces_specSubspace hB hn p

/-- Procrustes-aligned orthonormal bases.

Lean proof route for a weaker agent:

1. Choose principal vector bases and the polar/Procrustes alignment of the overlap matrix
2. sum `‖v_i-u_i‖² = 2(1-cos θ_i)` and use `1-cos θ ≤ sin² θ`.
-/
theorem exists_aligned_orthonormalBasis
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {d : ℕ}
    (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      ∑ i, ‖v i - u i‖ ^ 2 ≤ 2 * sinThetaFrobenius U V ^ 2 := by
  sorry

/-- YWS aligned-basis perturbation bound.

Lean proof route for a weaker agent:

1. Combine the corrected YWS sine bound with `exists_aligned_orthonormalBasis`, take square roots, and simplify constants.
2. Use `hcorr` in `yuWangSamworth_sinTheta_le`, then obtain aligned bases from `exists_aligned_orthonormalBasis`.
3. Take square roots with explicit nonnegativity facts and simplify the constant to `2 * sqrt 2`.

Signature audit: The aligned-basis theorem now inherits the same `hcorr` branch selection as
the sine-distance theorem.
-/
theorem yuWangSamworth_alignedBasis_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
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

/-- Rank-one/sign-aligned eigenvector corollary.

Lean proof route for a weaker agent:

1. After selecting the corresponding isolated eigenvector branch, specialize the aligned-basis theorem to rank one and take the unit scalar supplied by complex/real Procrustes alignment.
2. Convert the rank-one `hcorr` statement into the corresponding block premise for the aligned-basis theorem.
3. Extract the unique basis vectors and convert the one-dimensional unitary alignment into a scalar `c` of norm one.

Signature audit: The rank-one `hcorr` premise selects `v` from the corresponding ordered
perturbed eigenline rather than an arbitrary eigenvector of `B`.
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
  have hU : Reduces A (Submodule.span 𝕜 {u}) := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_smul, hAu]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hV : Reduces B (Submodule.span 𝕜 {v}) := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_smul, hBv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
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
  have hu'0 : u' 0 ∈ Submodule.span 𝕜 {u} := hspanU ▸ Submodule.subset_span ⟨0, rfl⟩
  rw [Submodule.mem_span_singleton] at hu'0
  obtain ⟨α, hα⟩ := hu'0
  have hv'0 : v' 0 ∈ Submodule.span 𝕜 {v} := hspanV ▸ Submodule.subset_span ⟨0, rfl⟩
  rw [Submodule.mem_span_singleton] at hv'0
  obtain ⟨β, hβ⟩ := hv'0
  have hαnorm : ‖α‖ = 1 := by
    have h := hu'on.norm_eq_one 0
    rw [← hα, norm_smul, hu, mul_one] at h; exact h
  have hβnorm : ‖β‖ = 1 := by
    have h := hv'on.norm_eq_one 0
    rw [← hβ, norm_smul, hv, mul_one] at h; exact h
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

end DavisKahanTheory
end ForMathlib
