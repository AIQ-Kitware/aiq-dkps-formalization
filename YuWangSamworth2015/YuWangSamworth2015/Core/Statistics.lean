/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation
public import TauCeti.Analysis.InnerProductSpace.Projection.FrobeniusSine
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Overlap
public import YuWangSamworth2015.Core.Residual
public import ForTauCeti.Analysis.InnerProductSpace.AlignedBasis

/-!
# Population-gap and statistical Davis--Kahan variants

Literature map:

* `prose/core-arguments/Yu-Wang-Samworth-2014-core-arguments.tex`, all sections.
* `papers/old/formalization_comparisons/DavisKahan-formalized-vs-literature.tex`, paragraphs
  "Hoffman--Wielandt and the exact YWS theorem" and
  "The aligned-basis (Procrustes) bound".

This file gives the existing YWS results a canonical subspace-facing API and
records the full interval-block, aligned-basis, and single-vector surfaces.

## Provenance

This theorem layer was previously staged under
`ForTauCeti/Analysis/InnerProductSpace/YuWangSamworth/Statistics.lean`.  On
2026-08-17 the YWS-specific population-gap statements moved downstream into
`YuWangSamworth2015.Core`.  The reusable Frobenius sine distance was separated
from them as `TauCeti.sinThetaFrobenius` in
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean`. That donor is
now retired in favor of accepted `Submodule.sinThetaFrobenius`; foundation
clients do not depend on this application package.

-/

public section

namespace YuWangSamworth2015
open TauCeti

open LinearMap.IsSymmetric (IsOrderedEigenframe isOrderedEigenframe_iff)
open LinearMap.IsSymmetric (isOrderedEigenframe_eigenvectorBasis)
open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

/-- `U` and `V` are spectral blocks with the same ordered eigenvalue indices
for `A` and `B`.  This is the finite branch-selection datum used by the
Yu--Wang--Samworth population-gap theorem. -/
def CorrespondingEigenblock {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (U V : Submodule 𝕜 E) : Prop :=
  ∃ (n : ℕ) (hn : finrank 𝕜 E = n) (s : Finset (Fin n)),
    U = (hA.eigenvectorBasis hn).spanIndices ↑s ∧
      V = (hB.eigenvectorBasis hn).spanIndices ↑s

/-- **The introduction rule for `CorrespondingEigenblock`.**

The index-selected YWS specializations consume this datum. Its internal
representation is deliberately hidden from other modules; the constructors in
`Core/TopEigenblock.lean` make it usable for concrete spectral blocks.

This introduction rule retains the chosen-eigenbasis semantics. The separate
`CorrespondingEigenblock.toCorrespondingEigenblocks` lemma forgets that choice
and supplies TauCeti's more general frame-based witness. The implication only
goes one way: it must not be used to narrow a source-facing arbitrary-frame
theorem to a chosen-eigenbasis statement. -/
theorem correspondingEigenblock_of_spanIndices {A B : E →ₗ[𝕜] E}
    {hA : A.IsSymmetric} {hB : B.IsSymmetric} {U V : Submodule 𝕜 E}
    {n : ℕ} (hn : finrank 𝕜 E = n) (s : Finset (Fin n))
    (hU : U = (hA.eigenvectorBasis hn).spanIndices ↑s)
    (hV : V = (hB.eigenvectorBasis hn).spanIndices ↑s) :
    CorrespondingEigenblock hA hB U V :=
  ⟨n, hn, s, hU, hV⟩

omit [FiniteDimensional 𝕜 E] in
/-- **Every ordered eigenframe of the canonical eigenbasis spans its block.**
The bridge from the index-set formulation `CorrespondingEigenblock` to the frame
formulation: selecting the indices `s` by their increasing enumeration gives an
ordered eigenframe whose span is `spanIndices ↑s`. -/
theorem span_range_eigenvectorBasis_orderEmbOfFin {n d : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E) {s : Finset (Fin n)} (hcard : s.card = d) :
    Submodule.span 𝕜 (Set.range fun i => b ((s.orderEmbOfFin hcard).toEmbedding i)) =
      b.spanIndices (↑s : Set (Fin n)) := by
  rw [OrthonormalBasis.spanIndices_eq_span,
    show (fun i => b ((s.orderEmbOfFin hcard).toEmbedding i))
      = ⇑b ∘ ⇑(s.orderEmbOfFin hcard).toEmbedding from rfl,
    Set.range_comp]
  congr 1
  simp

/-- A pair of canonical eigenbasis-selected blocks is a pair of corresponding
ordered eigenblocks in TauCeti's more general, frame-independent interface.
The converse does not hold: an upstream frame may select an arbitrary subspace
inside a repeated eigenspace, rather than Mathlib's chosen eigenbasis span. -/
theorem CorrespondingEigenblock.toCorrespondingEigenblocks {A B : E →ₗ[𝕜] E}
    {hA : A.IsSymmetric} {hB : B.IsSymmetric} {U V : Submodule 𝕜 E}
    (hcorr : CorrespondingEigenblock hA hB U V) :
    ∃ (n d : ℕ) (hn : finrank 𝕜 E = n) (e : Fin d ↪ Fin n),
      LinearMap.IsSymmetric.CorrespondingEigenblocks hA hB hn e U V := by
  classical
  obtain ⟨n, hn, s, hU, hV⟩ := hcorr
  let e : Fin s.card ↪ Fin n := (s.orderEmbOfFin rfl).toEmbedding
  refine ⟨n, s.card, hn, e, ?_⟩
  apply LinearMap.IsSymmetric.correspondingEigenblocks_iff.mpr
  refine ⟨(fun i => hA.eigenvectorBasis hn (e i)),
    (fun i => hB.eigenvectorBasis hn (e i)),
    isOrderedEigenframe_eigenvectorBasis hA hn e,
    isOrderedEigenframe_eigenvectorBasis hB hn e, ?_, ?_⟩
  · exact hU.trans ((span_range_eigenvectorBasis_orderEmbOfFin
      (hA.eigenvectorBasis hn) (s := s) rfl).symm)
  · exact hV.trans ((span_range_eigenvectorBasis_orderEmbOfFin
      (hB.eigenvectorBasis hn) (s := s) rfl).symm)


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
    Submodule.sinThetaFrobenius
        (Submodule.span 𝕜 (bT '' (↑s : Set (Fin n))))
        (Submodule.span 𝕜 (bS '' (↑s : Set (Fin n)))) =
      Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bT k, bS j⟫_𝕜‖ ^ 2) := by
  classical
  have hresult : (bT.spanIndices (↑s : Set (Fin n))).sinThetaFrobenius
      (bS.spanIndices (↑s : Set (Fin n))) =
        Real.sqrt (∑ j ∈ s, ∑ k ∈ sᶜ, ‖⟪bT k, bS j⟫_𝕜‖ ^ 2) := by
    have hrank : finrank 𝕜 (bT.spanIndices (↑s : Set (Fin n))) =
        finrank 𝕜 (bS.spanIndices (↑s : Set (Fin n))) := by
      rw [bT.finrank_spanIndices, bS.finrank_spanIndices]
    rw [Submodule.sinThetaFrobenius_comm _ _ hrank,
      ← bT.sq_sinThetaFrobenius_spanIndices bS s s,
      Real.sqrt_sq (Submodule.sinThetaFrobenius_nonneg _ _)]
  simpa only [OrthonormalBasis.spanIndices_eq_span] using hresult

/-- The family-level squared sine agrees with the canonical Frobenius
sine whenever the two orthonormal families span the supplied subspaces. -/
theorem sinThetaSq_eq_sinThetaFrobenius_sq_of_spans
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {d : ℕ}
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hspanU : Submodule.span 𝕜 (Set.range u) = U)
    (hspanV : Submodule.span 𝕜 (Set.range v) = V) :
    sinThetaSq hu hv = Submodule.sinThetaFrobenius U V ^ 2 := by
  rw [Submodule.sq_sinThetaFrobenius_eq_sinThetaSq_of_orthonormal V U hv hu hspanV hspanU,
    sinThetaSq_comm hu hv]

/-! ### Yu--Wang--Samworth Theorem 2 at the source's generality

Yu, Wang and Samworth fix `1 ≤ r ≤ s ≤ p`, impose a gap only on the *population*
eigenvalues, and then take `V = (v_r,…,v_s)` and `V̂ = (v̂_r,…,v̂_s)` to be **any**
matrices with orthonormal columns satisfying `Σ vⱼ = λⱼ vⱼ` and `Σ̂ v̂ⱼ = λ̂ⱼ v̂ⱼ`.
Removing the sample eigengap is the paper's contribution, so the sample block
must be allowed to cut through a repeated `λ̂`; the hypothesis is exactly
`LinearMap.IsSymmetric.IsOrderedEigenframe` for both operators at a common index embedding.

The theorems below are that statement.  `CorrespondingEigenblock` — which pins
both blocks to Mathlib's chosen eigenbases — is recovered from them as the
special case in which the chosen eigenvectors happen to be the canonical ones.
-/

/-- The canonical Frobenius sine of two spanned blocks, as complementary
projection energy of the second block's frame. -/
theorem sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal
    {d : ℕ} {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ^ 2
      = ∑ i, ‖(Submodule.span 𝕜 (Set.range u))ᗮ.starProjection (v i)‖ ^ 2 := by
  rw [← sinThetaSq_eq_sinThetaFrobenius_sq_of_spans hu hv rfl rfl]
  exact TauCeti.sinThetaSq_eq_sum_norm_starProjection_orthogonal_sq hu hv rfl

/-- **Turning the squared residual sandwich into the printed bound.**  From
`Δ² s² ≤ 4 c²` with `s, c ≥ 0` and `Δ > 0` one gets `s ≤ 2 c / Δ`. -/
private theorem le_two_mul_div_of_sq_gap_mul_sq_le {s Δ c : ℝ}
    (hΔ : 0 < Δ) (hc : 0 ≤ c) (h : Δ ^ 2 * s ^ 2 ≤ 4 * c ^ 2) : s ≤ 2 * c / Δ := by
  rw [le_div_iff₀ hΔ]
  nlinarith [h, hc, sq_nonneg (s * Δ - 2 * c), sq_nonneg (s * Δ + 2 * c)]

/-- **The residual-numerator form of Theorem 2** — the inequality Yu, Wang and
Samworth say their proof actually establishes, before weakening the numerator to
a perturbation norm:

`Δ ‖sin Θ(V̂, V)‖_F ≤ ‖V̂ Λ − Σ V̂‖_F`,

with `Λ = diag(λ_r,…,λ_s)` the *population* eigenvalues of the selected block.
Only the population frame's eigenvalues and the population gap appear; the
perturbed frame enters through its residual alone, so no hypothesis relates the
two operators yet. -/
theorem yuWangSamworth_sinTheta_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {d : ℕ} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
  classical
  set U := Submodule.span 𝕜 (Set.range u) with hU
  set V := Submodule.span 𝕜 (Set.range v) with hV
  set R := ∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2 with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hkey : Δ ^ 2 * Submodule.sinThetaFrobenius U V ^ 2 ≤ R := by
    rw [sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal
      (isOrderedEigenframe_iff.mp hu).orthonormal (isOrderedEigenframe_iff.mp hv).orthonormal]
    exact sq_gap_mul_sum_sq_norm_starProjection_orthogonal_le hA
      hΔ.le (hu.pointInternalGap_span hΔ hgap) v (fun i => hA.eigenvalues hn (e i))
      fun i => (isOrderedEigenframe_iff.mp hu).eigenvalue_mem_restrictedPointSpectrum i
  have hs0 : 0 ≤ Submodule.sinThetaFrobenius U V :=
    Submodule.sinThetaFrobenius_nonneg U V
  rw [le_div_iff₀ hΔ]
  nlinarith [hkey, hs0, Real.sq_sqrt hR0, Real.sqrt_nonneg R,
    sq_nonneg (Submodule.sinThetaFrobenius U V * Δ - Real.sqrt R),
    sq_nonneg (Submodule.sinThetaFrobenius U V * Δ + Real.sqrt R)]

/-- **Yu--Wang--Samworth Theorem 2, first conclusion, at the printed generality.**

`Σ` and `Σ̂` are symmetric, the block is selected by an index embedding `e` into
the sorted spectra, and `V`, `V̂` are *arbitrary* orthonormal eigenframes at
those indices — in particular the sample frame may cut a repeated sample
eigenvalue, which is the case the paper's removal of the sample eigengap is for.
With only the population separation `Δ`,

`‖sin Θ(V̂, V)‖_F ≤ 2 min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`.

The `min` is proved as printed, not as one branch: the residual is bounded twice,
by orthonormal compression plus Hoffman--Wielandt on the Frobenius side and by
Weyl on the dimension-scaled operator side. -/
theorem yuWangSamworth_sinTheta_frame_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {d : ℕ} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
        (Submodule.span 𝕜 (Set.range v)) ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by
  classical
  set U := Submodule.span 𝕜 (Set.range u) with hU
  set V := Submodule.span 𝕜 (Set.range v) with hV
  set R := ∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2 with hR
  have hkey : Δ ^ 2 * Submodule.sinThetaFrobenius U V ^ 2 ≤ R := by
    rw [hR, sinThetaFrobenius_sq_eq_sum_sq_norm_starProjection_orthogonal
      (isOrderedEigenframe_iff.mp hu).orthonormal (isOrderedEigenframe_iff.mp hv).orthonormal]
    exact sq_gap_mul_sum_sq_norm_starProjection_orthogonal_le hA
      hΔ.le (hu.pointInternalGap_span hΔ hgap) v (fun i => hA.eigenvalues hn (e i))
      fun i => (isOrderedEigenframe_iff.mp hu).eigenvalue_mem_restrictedPointSpectrum i
  -- Frobenius branch.
  have hfrob : Submodule.sinThetaFrobenius U V ≤
      2 * UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A) / Δ := by
    refine le_two_mul_div_of_sq_gap_mul_sq_le hΔ
      (apply_nonneg (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)) _)
      (hkey.trans ?_)
    rw [UnitarilyInvariantSeminorm.sq_frobenius_apply (hA.eigenvectorBasis hn) (B - A)]
    exact sum_sq_norm_frameResidual_le hA hB hn hv
  -- Dimension-scaled operator-norm branch.
  have hop : Submodule.sinThetaFrobenius U V ≤
      2 * (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖) / Δ := by
    refine le_two_mul_div_of_sq_gap_mul_sq_le hΔ (by positivity) (hkey.trans ?_)
    have hres := sum_sq_norm_frameResidual_le_of_opNorm hA hB hn hv
      (ε := ‖(B - A).toContinuousLinearMap‖)
      (fun x => by
        have hx := (B - A).toContinuousLinearMap.le_opNorm x
        rwa [LinearMap.coe_toContinuousLinearMap'] at hx)
    refine hres.trans_eq ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rcases le_total (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
      (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) with hle | hle
  · rw [min_eq_left hle]; exact hop
  · rw [min_eq_right hle]; exact hfrob

/-- **Theorem 2 for the canonically indexed blocks.**

The specialization of `yuWangSamworth_sinTheta_frame_le` in which the two frames
are Mathlib's own eigenbases at a common index set — the `CorrespondingEigenblock`
datum.  It is *not* the source statement: `CorrespondingEigenblock` fixes the
choice of eigenvectors inside a repeated eigenvalue, which Yu, Wang and Samworth
deliberately leave free on the perturbed side.  Cite
`yuWangSamworth_sinTheta_frame_le` for the printed theorem and this one when the
blocks are already presented by indices.

Related Lean work: `YuanheZ/lean-stat-learning-theory` proves operator-norm
eigenvector and spectral-projection DK endpoints in `SLT/MatrixInfra/Perturb.lean`.
Those results provide an independent check of the gap/perturbation mechanism but
do not include the YWS Frobenius minimum, population-gap residual sandwich, or
aligned-basis conclusion proved here.
-/
theorem yuWangSamworth_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (_hV : (V ∈ Module.End.invtSubmodule B))
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : PointInternalGap A U Δ) :
    Submodule.sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by
  classical
  obtain ⟨n, hn, s, rfl, rfl⟩ := hcorr
  have hcard : s.card = d := by
    rw [← hrank, (hA.eigenvectorBasis hn).finrank_spanIndices]
  have hindexGap : ∀ j ∈ s, ∀ k ∉ s,
      Δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k| := by
    intro j hj k hk
    apply hgap.2 (hA.eigenvalues hn j) (hA.eigenvalues hn k)
    · refine Module.End.mem_restrictedPointSpectrum ?_
        ((hA.eigenvectorBasis hn).orthonormal.ne_zero j)
        (hA.apply_eigenvectorBasis hn j)
      exact (hA.eigenvectorBasis hn).mem_spanIndices_of_mem hj
    · refine Module.End.mem_restrictedPointSpectrum ?_
        ((hA.eigenvectorBasis hn).orthonormal.ne_zero k)
        (hA.apply_eigenvectorBasis hn k)
      rw [OrthonormalBasis.orthogonal_spanIndices]
      exact (hA.eigenvectorBasis hn).mem_spanIndices_of_mem hk
  set e : Fin d ↪ Fin n := (s.orderEmbOfFin hcard).toEmbedding with he
  have hrange : Set.range (⇑e) = (↑s : Set (Fin n)) := by
    rw [he]
    simp
  have hgapIdx : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k| := by
    intro i k hk
    refine hindexGap (e i) (Finset.orderEmbOfFin_mem s hcard i) k fun hks => hk ?_
    rw [hrange]
    exact hks
  have hkey := yuWangSamworth_sinTheta_frame_le
    (isOrderedEigenframe_eigenvectorBasis hA hn e)
    (isOrderedEigenframe_eigenvectorBasis hB hn e) hΔ hgapIdx
  rwa [span_range_eigenvectorBasis_orderEmbOfFin (hA.eigenvectorBasis hn) hcard,
    span_range_eigenvectorBasis_orderEmbOfFin (hB.eigenvectorBasis hn) hcard] at hkey

/-- Arbitrary contiguous population eigenblock.

`hUeq` records the population interval while `hcorr` selects the perturbed block by ordered
indices, so eigenvalue drift across the numerical interval does not change the branch.  Like
`yuWangSamworth_sinTheta_le`, this is the index-block specialization; the printed hypothesis is
carried by `yuWangSamworth_sinTheta_frame_le`.
-/
theorem yuWangSamworth_intervalBlock_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    {a b Δ : ℝ} (hΔ : 0 < Δ)
    (_hUeq : U = Module.End.pointSpectralSubspace A (Set.Icc a b))
    (hcorr : CorrespondingEigenblock hA hB U V)
    (hgap : PointInternalGap A U Δ) :
    Submodule.sinThetaFrobenius U V ≤
      2 * min (Real.sqrt (finrank 𝕜 U) * ‖(B - A).toContinuousLinearMap‖)
        (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by
  have hV : (V ∈ Module.End.invtSubmodule B) := by
    obtain ⟨_n, _d, _hn, _e, hcanonical⟩ := hcorr.toCorrespondingEigenblocks
    intro x hx
    exact hcanonical.apply_mem_right hx
  exact yuWangSamworth_sinTheta_le hA hB hV hcorr rfl hΔ hgap

/-- Procrustes-aligned orthonormal bases. -/
theorem exists_aligned_orthonormalBasis
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] {d : ℕ}
    (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      ∑ i, ‖v i - u i‖ ^ 2 ≤ 2 * Submodule.sinThetaFrobenius U V ^ 2 := by
  classical
  let bU := stdOrthonormalBasis 𝕜 U
  let bV := stdOrthonormalBasis 𝕜 V
  let u : Fin d → E := fun i => ((bU (Fin.cast hrankU.symm i) : U) : E)
  let v0 : Fin d → E := fun i => ((bV (Fin.cast hrankV.symm i) : V) : E)
  have hu : Orthonormal 𝕜 u :=
    (bU.orthonormal.comp_linearIsometry U.subtypeₗᵢ).comp _
      (Fin.cast_injective hrankU.symm)
  have hv0 : Orthonormal 𝕜 v0 :=
    (bV.orthonormal.comp_linearIsometry V.subtypeₗᵢ).comp _
      (Fin.cast_injective hrankV.symm)
  have hspanU : Submodule.span 𝕜 (Set.range u) = U :=
    span_range_eq_of_orthonormal_of_mem hu
      (fun i => (bU (Fin.cast hrankU.symm i)).2) hrankU.symm
  have hspanV0 : Submodule.span 𝕜 (Set.range v0) = V :=
    span_range_eq_of_orthonormal_of_mem hv0
      (fun i => (bV (Fin.cast hrankV.symm i)).2) hrankV.symm
  let O := choosePolarUnitary (overlapOperator 𝕜 u v0)
  let v : Fin d → E := fun i =>
    hv0.synthesisMapIsometry (O.symm (EuclideanSpace.single i 1))
  have hv : Orthonormal 𝕜 v := by
    rw [orthonormal_iff_ite]
    intro i j
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change
      ⟪hv0.synthesisMapIsometry (O.symm (EuclideanSpace.single i (1 : 𝕜))),
        hv0.synthesisMapIsometry (O.symm (EuclideanSpace.single j (1 : 𝕜)))⟫_𝕜 =
          if i = j then 1 else 0
    rw [(hv0.synthesisMapIsometry).inner_map_map, O.symm.inner_map_map]
    exact orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j
  have hspanV : Submodule.span 𝕜 (Set.range v) = V :=
    span_range_eq_of_orthonormal_of_mem hv
      (fun i => hspanV0 ▸ hv0.range_synthesisMapIsometry.le
        ⟨O.symm (EuclideanSpace.single i 1), rfl⟩) hrankV.symm
  have hsum := sum_sq_norm_aligned_le_sinThetaSq hu hv0
  have hbridge := sinThetaSq_eq_sinThetaFrobenius_sq_of_spans
    hu hv0 hspanU hspanV0
  refine ⟨u, v, hu, hv, hspanU, hspanV, ?_⟩
  simpa only [v, O, hbridge] using hsum

/-- **Yu--Wang--Samworth Theorem 2, second conclusion, at the printed
generality.**  For arbitrary ordered eigenframes there are orthonormal frames of
the two blocks — the paper's `V̂ Ô` and `V` — with

`‖V̂ Ô − V‖_F ≤ 2^{3/2} min(√d ‖Σ̂ − Σ‖_op, ‖Σ̂ − Σ‖_F) / Δ`.

The `√2` is the Procrustes step `‖V̂ Ô − V‖²_F ≤ 2 ‖sin Θ‖²_F`. -/
theorem yuWangSamworth_alignedBasis_frame_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {d : ℕ} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ (u' v' : Fin d → E), Orthonormal 𝕜 u' ∧ Orthonormal 𝕜 v' ∧
      Submodule.span 𝕜 (Set.range u') = Submodule.span 𝕜 (Set.range u) ∧
      Submodule.span 𝕜 (Set.range v') = Submodule.span 𝕜 (Set.range v) ∧
      Real.sqrt (∑ i, ‖v' i - u' i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by
  obtain ⟨u', v', hu', hv', hspanU, hspanV, hsum⟩ :=
    exists_aligned_orthonormalBasis
      (by simpa only [Fintype.card_fin] using hu.finrank_span)
      (by simpa only [Fintype.card_fin] using hv.finrank_span)
  refine ⟨u', v', hu', hv', hspanU, hspanV, ?_⟩
  have hsine := yuWangSamworth_sinTheta_frame_le hu hv hΔ hgap
  have hsnn : (0 : ℝ) ≤ Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) :=
    Submodule.sinThetaFrobenius_nonneg _ _
  calc Real.sqrt (∑ i, ‖v' i - u' i‖ ^ 2)
      ≤ Real.sqrt (2 * Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 * (2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = 2 * Real.sqrt 2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by ring

/-- **The residual-numerator form of the aligned-frame conclusion** — the second
inequality Yu, Wang and Samworth record as available from their proof:
`‖V̂ Ô − V‖_F ≤ 2^{1/2} ‖V̂ Λ − Σ V̂‖_F / Δ`. -/
theorem yuWangSamworth_alignedBasis_le_residual
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {d : ℕ} {e : Fin d ↪ Fin n} {u v : Fin d → E}
    (hu : IsOrderedEigenframe hA hn e u) (hv : IsOrderedEigenframe hB hn e v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|) :
    ∃ (u' v' : Fin d → E), Orthonormal 𝕜 u' ∧ Orthonormal 𝕜 v' ∧
      Submodule.span 𝕜 (Set.range u') = Submodule.span 𝕜 (Set.range u) ∧
      Submodule.span 𝕜 (Set.range v') = Submodule.span 𝕜 (Set.range v) ∧
      Real.sqrt (∑ i, ‖v' i - u' i‖ ^ 2) ≤
        Real.sqrt 2 *
          Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
  obtain ⟨u', v', hu', hv', hspanU, hspanV, hsum⟩ :=
    exists_aligned_orthonormalBasis
      (by simpa only [Fintype.card_fin] using hu.finrank_span)
      (by simpa only [Fintype.card_fin] using hv.finrank_span)
  refine ⟨u', v', hu', hv', hspanU, hspanV, ?_⟩
  have hsine := yuWangSamworth_sinTheta_le_residual hu hv hΔ hgap
  have hsnn : (0 : ℝ) ≤ Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
      (Submodule.span 𝕜 (Set.range v)) :=
    Submodule.sinThetaFrobenius_nonneg _ _
  calc Real.sqrt (∑ i, ‖v' i - u' i‖ ^ 2)
      ≤ Real.sqrt (2 * Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * Submodule.sinThetaFrobenius (Submodule.span 𝕜 (Set.range u))
          (Submodule.span 𝕜 (Set.range v)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 *
          (Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 *
          Real.sqrt (∑ i, ‖(hA.eigenvalues hn (e i) : 𝕜) • v i - A (v i)‖ ^ 2) / Δ := by
        ring

/-- YWS aligned-basis perturbation bound for the canonically indexed blocks.

The index-block specialization of `yuWangSamworth_alignedBasis_frame_le`; it inherits the same
`hcorr` branch selection as `yuWangSamworth_sinTheta_le`, and is therefore narrower than the
printed theorem in exactly the same way.
-/
theorem yuWangSamworth_alignedBasis_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hV : (V ∈ Module.End.invtSubmodule B))
    (hcorr : CorrespondingEigenblock hA hB U V)
    {d : ℕ} (hrankU : finrank 𝕜 U = d) (hrankV : finrank 𝕜 V = d)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : PointInternalGap A U Δ) :
    ∃ (u v : Fin d → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      Submodule.span 𝕜 (Set.range u) = U ∧
      Submodule.span 𝕜 (Set.range v) = V ∧
      Real.sqrt (∑ i, ‖v i - u i‖ ^ 2) ≤
        2 * Real.sqrt 2 *
          min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
            (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by
  obtain ⟨u, v, hu, hv, hspanU, hspanV, hsum⟩ :=
    exists_aligned_orthonormalBasis hrankU hrankV
  refine ⟨u, v, hu, hv, hspanU, hspanV, ?_⟩
  have hsine := yuWangSamworth_sinTheta_le hA hB hV hcorr hrankU hΔ hgap
  have hsnn : (0 : ℝ) ≤ Submodule.sinThetaFrobenius U V :=
    Submodule.sinThetaFrobenius_nonneg U V
  calc Real.sqrt (∑ i, ‖v i - u i‖ ^ 2)
      ≤ Real.sqrt (2 * Submodule.sinThetaFrobenius U V ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * Submodule.sinThetaFrobenius U V := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hsnn]
    _ ≤ Real.sqrt 2 * (2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ) :=
        mul_le_mul_of_nonneg_left hsine (Real.sqrt_nonneg 2)
    _ = 2 * Real.sqrt 2 * min (Real.sqrt d * ‖(B - A).toContinuousLinearMap‖)
          (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A)) / Δ := by ring

omit [FiniteDimensional 𝕜 E] in
/-- **The span of an eigenvector is invariant.**  If `A u = lam • u` then every
scalar multiple of `u` is sent to a scalar multiple of `u`. -/
private theorem isInvariant_span_singleton_of_apply_eq_smul
    {A : E →ₗ[𝕜] E} {u : E} {lam : ℝ} (hAu : A u = (lam : 𝕜) • u) :
    ((Submodule.span 𝕜 {u}) ∈ Module.End.invtSubmodule A) := by
  intro x hx
  change A x ∈ Submodule.span 𝕜 {u}
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

/-- Rank-one/sign-aligned eigenvector corollary for a canonically indexed eigenline.

The `hcorr` premise selects `v` from the corresponding ordered perturbed eigenline rather than
from an arbitrary eigenvector of `B`, so this is narrower than Corollary 1.  The source-faithful
statements are `yuWangSamworth_eigenvector_frame_sinTheta_le` together with
`yuWangSamworth_eigenvector_real_le`, which are the printed displays with the normalization the
standalone printed corollary omits written out.

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
    (hgap : ∀ ν ∈ Module.End.restrictedPointSpectrum A (Submodule.span 𝕜 {u})ᗮ,
      Δ ≤ |lam - ν|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  have hu0 : u ≠ 0 := by rw [← norm_ne_zero_iff, hu]; norm_num
  have hv0 : v ≠ 0 := by rw [← norm_ne_zero_iff, hv]; norm_num
  -- The eigenlines reduce the operators.
  have hU : ((Submodule.span 𝕜 {u}) ∈ Module.End.invtSubmodule A) :=
    isInvariant_span_singleton_of_apply_eq_smul hAu
  have hV : ((Submodule.span 𝕜 {v}) ∈ Module.End.invtSubmodule B) :=
    isInvariant_span_singleton_of_apply_eq_smul hBv
  have hrankU : finrank 𝕜 (Submodule.span 𝕜 {u}) = 1 := finrank_span_singleton hu0
  have hrankV : finrank 𝕜 (Submodule.span 𝕜 {v}) = 1 := finrank_span_singleton hv0
  -- The restricted spectrum of `A` on the eigenline is exactly `{lam}`, so the internal
  -- gap follows from `hgap`.
  have hgap' : PointInternalGap A (Submodule.span 𝕜 {u}) Δ := by
    refine ⟨hU, ?_⟩
    intro l ν hl hν
    obtain ⟨x, hxU, hx0, hAx⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hl
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
    yuWangSamworth_alignedBasis_le hA hB hV hcorr hrankU hrankV hΔ hgap'
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
      (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A))
      ≤ ‖(B - A).toContinuousLinearMap‖ :=
    (min_le_left _ _).trans_eq (by rw [Nat.cast_one, Real.sqrt_one, one_mul])
  gcongr

/-! ### Corollary 1: the single-eigenvector case, source-faithful at `d = 1`

Yu, Wang and Samworth state the `d = 1` case separately because it is the one
most applications need.  Their printed hypotheses are `Σ v = λⱼ v` and
`Σ̂ v̂ = λ̂ⱼ v̂` for *some* vectors — no sample gap, and no claim that `v̂` is any
particular eigenvector when `λ̂ⱼ` is repeated.

The statements below add `‖v‖ = ‖v̂‖ = 1`, which the standalone printed display
omits and the corollary inherits from its derivation as the `d = 1` case of
Theorem 2.  That is not optional: see
`YuWangSamworth2015.corollary1_printed_unnormalized_counterexample`.
-/

omit [FiniteDimensional 𝕜 E] in
/-- A single unit vector is an orthonormal family. -/
private theorem orthonormal_const_of_norm_eq_one {u : E} (hu : ‖u‖ = 1) :
    Orthonormal 𝕜 (fun _ : Fin 1 => u) := by
  rw [orthonormal_iff_ite]
  intro i k
  simp [Subsingleton.elim i k, inner_self_eq_norm_sq_to_K, hu]

omit [FiniteDimensional 𝕜 E] in
/-- The span of the constant one-element family is the line through `u`. -/
private theorem span_range_const (u : E) :
    Submodule.span 𝕜 (Set.range fun _ : Fin 1 => u) = Submodule.span 𝕜 {u} := by
  rw [Set.range_const]

/-- **Corollary 1, first display, the source-faithful `d = 1` specialization.**
`sin Θ(v̂, v) ≤ 2 ‖Σ̂ − Σ‖_op / Δⱼ` for *arbitrary* unit eigenvectors `v`, `v̂`
belonging to the `j`-th population and sample eigenvalues, with only the
population separation `Δⱼ = min(λ_{j-1} − λⱼ, λⱼ − λ_{j+1})`.  The unit
normalization is inherited from the corollary's derivation as the `d = 1` case of
Theorem 2; the standalone printed display omits it. -/
theorem yuWangSamworth_eigenvector_frame_sinTheta_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {j : Fin n} {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hAu : A u = (hA.eigenvalues hn j : 𝕜) • u)
    (hBv : B v = (hB.eigenvalues hn j : 𝕜) • v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ k : Fin n, k ≠ j → Δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    Submodule.sinThetaFrobenius (Submodule.span 𝕜 {u}) (Submodule.span 𝕜 {v}) ≤
      2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  classical
  set e : Fin 1 ↪ Fin n := ⟨fun _ => j, fun a b _ => Subsingleton.elim a b⟩ with he
  have hframeA : IsOrderedEigenframe hA hn e fun _ => u :=
    isOrderedEigenframe_iff.mpr
      ⟨orthonormal_const_of_norm_eq_one hu, fun _ => hAu⟩
  have hframeB : IsOrderedEigenframe hB hn e fun _ => v :=
    isOrderedEigenframe_iff.mpr
      ⟨orthonormal_const_of_norm_eq_one hv, fun _ => hBv⟩
  have hgapIdx : ∀ (i : Fin 1) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k| := by
    intro i k hk
    exact hgap k fun hkj => hk ⟨i, by rw [he]; exact hkj.symm⟩
  have hkey := yuWangSamworth_sinTheta_frame_le hframeA hframeB hΔ hgapIdx
  rw [span_range_const, span_range_const] at hkey
  refine hkey.trans ?_
  have hmin : min (Real.sqrt (↑(1 : ℕ)) * ‖(B - A).toContinuousLinearMap‖)
      (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A))
      ≤ ‖(B - A).toContinuousLinearMap‖ :=
    (min_le_left _ _).trans_eq (by rw [Nat.cast_one, Real.sqrt_one, one_mul])
  gcongr

/-- **Corollary 1, second display, the source-faithful `d = 1` specialization**
— up to the orientation choice.  Over `ℝ` the unit scalar `c` is `±1`, which is exactly the
sign the paper fixes by requiring `v̂ᵀ v ≥ 0`; over `ℂ` a phase is the honest
generalization.  See `yuWangSamworth_eigenvector_real_le` for the real form,
which is the printed display with the inherited normalization written out. -/
theorem yuWangSamworth_eigenvector_frame_le
    {A B : E →ₗ[𝕜] E} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank 𝕜 E = n} {j : Fin n} {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hAu : A u = (hA.eigenvalues hn j : 𝕜) • u)
    (hBv : B v = (hB.eigenvalues hn j : 𝕜) • v)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ k : Fin n, k ≠ j → Δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    ∃ c : 𝕜, ‖c‖ = 1 ∧
      ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  classical
  set e : Fin 1 ↪ Fin n := ⟨fun _ => j, fun a b _ => Subsingleton.elim a b⟩ with he
  have hframeA : IsOrderedEigenframe hA hn e fun _ => u :=
    isOrderedEigenframe_iff.mpr
      ⟨orthonormal_const_of_norm_eq_one hu, fun _ => hAu⟩
  have hframeB : IsOrderedEigenframe hB hn e fun _ => v :=
    isOrderedEigenframe_iff.mpr
      ⟨orthonormal_const_of_norm_eq_one hv, fun _ => hBv⟩
  have hgapIdx : ∀ (i : Fin 1) (k : Fin n), k ∉ Set.range (⇑e) →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k| := by
    intro i k hk
    exact hgap k fun hkj => hk ⟨i, by rw [he]; exact hkj.symm⟩
  obtain ⟨u', v', hu'on, hv'on, hspanU, hspanV, hbound⟩ :=
    yuWangSamworth_alignedBasis_frame_le hframeA hframeB hΔ hgapIdx
  rw [span_range_const] at hspanU
  rw [span_range_const] at hspanV
  have hu'mem : u' 0 ∈ Submodule.span 𝕜 {u} := hspanU ▸ Submodule.subset_span ⟨0, rfl⟩
  have hv'mem : v' 0 ∈ Submodule.span 𝕜 {v} := hspanV ▸ Submodule.subset_span ⟨0, rfl⟩
  obtain ⟨α, hαnorm, hα⟩ :=
    exists_unit_smul_eq_of_mem_span_singleton hu (hu'on.norm_eq_one 0) hu'mem
  obtain ⟨β, hβnorm, hβ⟩ :=
    exists_unit_smul_eq_of_mem_span_singleton hv (hv'on.norm_eq_one 0) hv'mem
  have hα0 : α ≠ 0 := by rw [← norm_ne_zero_iff, hαnorm]; norm_num
  refine ⟨β * α⁻¹, by rw [norm_mul, norm_inv, hαnorm, hβnorm]; norm_num, ?_⟩
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
      (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A))
      ≤ ‖(B - A).toContinuousLinearMap‖ :=
    (min_le_left _ _).trans_eq (by rw [Nat.cast_one, Real.sqrt_one, one_mul])
  gcongr

/-! ## Recovering a mixed gap from a population gap

The proof pattern the population-gap theorems above are designed to replace: a
mixed-gap theorem is applied first, and Weyl's inequality then converts the
random mixed separation into a population one on a high-probability event.  The
deterministic core of that step is the triangle inequality, recorded here so
that comparing the two routes is a statement about two proved theorems. -/

/-- **Weyl recovery of a mixed gap.**

A population exterior gap `Δ` at the selected index block becomes a mixed
population/sample gap `Δ − ε` as soon as the perturbation is `ε`-operator-small,
because Weyl's inequality moves each sorted eigenvalue by at most `ε`.

The recovered gap is worthless unless `ε < Δ`, and that side condition is
exactly the event the two-step argument has to carry through the rest of its
proof.  `yuWangSamworth_sinTheta_frame_le` reaches the same denominator with no
such hypothesis, which is the whole point of the population-gap formulation. -/
theorem mixedGap_of_populationGap_weyl {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n) {d : ℕ} {e : Fin d ↪ Fin n}
    {Δ ε : ℝ} (hε : ∀ x : E, ‖(B - A) x‖ ≤ ε * ‖x‖)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|)
    (i : Fin d) (k : Fin n) (hk : k ∉ Set.range e) :
    Δ - ε ≤ |hA.eigenvalues hn (e i) - hB.eigenvalues hn k| := by
  have hweyl : |hB.eigenvalues hn k - hA.eigenvalues hn k| ≤ ε :=
    LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le hB hA hn hε k
  have htri : |hA.eigenvalues hn (e i) - hA.eigenvalues hn k|
      ≤ |hA.eigenvalues hn (e i) - hB.eigenvalues hn k|
        + |hB.eigenvalues hn k - hA.eigenvalues hn k| := abs_sub_le _ _ _
  have hpop := hgap i k hk
  linarith

/-! ## Orthogonal coordinate blocks

Every sharpness example for the theorems above has the same shape: two operators
diagonal in one orthonormal basis, with the two selected blocks occupying
*disjoint* index sets.  The two facts such an example needs are recorded here
once, for arbitrary index sets, so that no example has to recompute them. -/

/-- **The sine distance between disjoint coordinate blocks.**

Disjoint index sets span orthogonal subspaces, so every principal angle is a
right angle: the sine cross-projection is the projector onto the first block and
its Frobenius norm is the square root of that block's dimension. -/
theorem sinThetaFrobenius_spanIndices_of_subset_compl {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E)
    (S T : Set (Fin n)) [DecidablePred (· ∈ S)] (hdisj : S ⊆ Tᶜ) :
    Submodule.sinThetaFrobenius (b.spanIndices S) (b.spanIndices T) =
      Real.sqrt S.toFinset.card := by
  classical
  have hperp : b.spanIndices S ≤ (b.spanIndices T)ᗮ := by
    rw [OrthonormalBasis.orthogonal_spanIndices]
    exact OrthonormalBasis.spanIndices_mono b hdisj
  -- On the first block the complementary projector of the second is the identity.
  have hsin : ((b.spanIndices S).sinThetaMap (b.spanIndices T)).toLinearMap =
      ((b.spanIndices S)).starProjection.toLinearMap := by
    rw [Submodule.sinThetaMap_def]
    refine LinearMap.ext fun x => ?_
    have hmem : ((b.spanIndices S)).starProjection.toLinearMap x ∈ (b.spanIndices T)ᗮ :=
      hperp (Submodule.starProjection_apply_mem _ x)
    change ((b.spanIndices T)ᗮ).starProjection ((b.spanIndices S).starProjection x) =
      (b.spanIndices S).starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr hmem
  rw [Submodule.sinThetaFrobenius_def]
  change UnitarilyInvariantSeminorm.frobenius 𝕜 E E
    (((b.spanIndices S).sinThetaMap (b.spanIndices T)).toLinearMap) = _
  rw [hsin, UnitarilyInvariantSeminorm.frobenius_apply b (((b.spanIndices
      S)).starProjection.toLinearMap)]
  have hspan : b.spanIndices S =
      Submodule.span 𝕜 (b '' (↑S.toFinset : Set (Fin n))) := by
    rw [OrthonormalBasis.spanIndices_eq_span, Set.coe_toFinset]
  have hcol : ∀ i : Fin n, ‖((b.spanIndices S)).starProjection.toLinearMap (b i)‖ ^ 2 =
      if i ∈ S.toFinset then (1 : ℝ) else 0 := by
    intro i
    have hproj : (b.spanIndices S).starProjection (b i) =
        if i ∈ S.toFinset then b i else 0 := by
      rw [hspan]
      have hr : Set.range (b ∘ fun j : S.toFinset => (j : Fin n)) =
          b '' (S.toFinset : Set (Fin n)) := by ext; simp
      rw [(b.orthonormal.comp _ Subtype.val_injective).starProjection_apply_eq_sum
        (U := Submodule.span 𝕜 (b '' ↑S.toFinset)) (by rw [hr])]
      simp only [Function.comp_apply]
      rw [Finset.sum_coe_sort S.toFinset (fun j => ⟪b j, b i⟫_𝕜 • b j)]
      simp only [orthonormal_iff_ite.mp b.orthonormal, ite_smul,
        one_smul, zero_smul]
      exact Finset.sum_ite_eq' S.toFinset i fun j => b j
    change ‖(b.spanIndices S).starProjection (b i)‖ ^ 2 = _
    rw [hproj]
    split_ifs
    · rw [b.orthonormal.norm_eq_one i, one_pow]
    · simp
  rw [Finset.sum_congr rfl fun i _ => hcol i, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

omit [FiniteDimensional 𝕜 E] in
/-- **Aligned pairs drawn from orthogonal blocks are at distance `√(2d)`.**

If `U ⟂ V` then every unit vector of `U` is at distance `√2` from every unit
vector of `V`, so no alignment of two orthonormal `d`-frames can do better than
`∑ᵢ ‖vᵢ − uᵢ‖² = 2d`.  This is why an orthogonal-blocks example pins the
aligned-basis constant. -/
theorem sum_sq_norm_sub_eq_of_le_orthogonal {U V : Submodule 𝕜 E} (hperp : U ≤ Vᗮ)
    {d : ℕ} {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hUu : ∀ i, u i ∈ U) (hVv : ∀ i, v i ∈ V) :
    ∑ i, ‖v i - u i‖ ^ 2 = 2 * d := by
  have hcol : ∀ i, ‖v i - u i‖ ^ 2 = (2 : ℝ) := by
    intro i
    have hzero : ⟪v i, u i⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ _).mp (hperp (hUu i)) (v i) (hVv i)
    rw [@norm_sub_sq 𝕜, hu.norm_eq_one i, hv.norm_eq_one i, hzero]
    norm_num
  rw [Finset.sum_congr rfl fun i _ => hcol i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm]

end YuWangSamworth2015

namespace YuWangSamworth2015
open TauCeti

open scoped InnerProductSpace RealInnerProductSpace
open Module (finrank)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- **Sign alignment beats any other orientation.**  For unit vectors with
`⟪v, u⟫ ≥ 0` and a unit real scalar `c`, `‖v − u‖ ≤ ‖c • v − u‖`: both squared
norms are `2 − 2 c ⟪v, u⟫` with `c = 1` on the left, and `c ≤ 1`. -/
private theorem norm_sub_le_norm_smul_sub {u v : F} {c : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hc : ‖c‖ = 1) (hinner : 0 ≤ ⟪v, u⟫) :
    ‖v - u‖ ≤ ‖c • v - u‖ := by
  have hcabs : |c| = 1 := by rwa [Real.norm_eq_abs] at hc
  have hcle : c ≤ 1 := (abs_le.mp hcabs.le).2
  have hcsq : c ^ 2 = 1 := by
    rw [← sq_abs, hcabs, one_pow]
  have h1 : ‖v - u‖ ^ 2 = 2 - 2 * ⟪v, u⟫ := by
    rw [norm_sub_sq_real, hu, hv]; ring
  have h2 : ‖c • v - u‖ ^ 2 = 2 - 2 * (c * ⟪v, u⟫) := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, hu, hv, Real.norm_eq_abs]
    rw [mul_one, sq_abs, hcsq]
    ring
  have hsq : ‖v - u‖ ^ 2 ≤ ‖c • v - u‖ ^ 2 := by
    rw [h1, h2]
    nlinarith [hinner, hcle]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- **Yu--Wang--Samworth Corollary 1, the source-faithful `d = 1`
specialization.**

Not "exactly as printed": the standalone printed corollary omits `‖v‖ = ‖v̂‖ = 1`,
which it inherits from its derivation as the `d = 1` case of Theorem 2, and its
second display is false without it.  See
`YuWangSamworth2015.corollary1_printed_unnormalized_counterexample`.

Real symmetric `Σ`, `Σ̂`; a population separation
`Δⱼ = min(λ_{j-1} − λⱼ, λⱼ − λ_{j+1}) > 0` and *no* sample separation; `v`, `v̂`
arbitrary unit vectors with `Σ v = λⱼ v` and `Σ̂ v̂ = λ̂ⱼ v̂`.  Then, for the
orientation with `v̂ᵀ v ≥ 0`,

`‖v̂ − v‖ ≤ 2^{3/2} ‖Σ̂ − Σ‖_op / Δⱼ`.

The `RCLike` theorem `yuWangSamworth_eigenvector_frame_le` produces a unit scalar
`c`; over `ℝ` that scalar is `±1`, and `norm_sub_le_norm_smul_sub` says the
sign-aligned difference is the smaller of the two. -/
theorem yuWangSamworth_eigenvector_real_le
    {A B : F →ₗ[ℝ] F} {hA : A.IsSymmetric} {hB : B.IsSymmetric}
    {n : ℕ} {hn : finrank ℝ F = n} {j : Fin n} {u v : F}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hAu : A u = (hA.eigenvalues hn j : ℝ) • u)
    (hBv : B v = (hB.eigenvalues hn j : ℝ) • v)
    (hsign : 0 ≤ ⟪v, u⟫)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ k : Fin n, k ≠ j → Δ ≤ |hA.eigenvalues hn j - hA.eigenvalues hn k|) :
    ‖v - u‖ ≤ 2 * Real.sqrt 2 * ‖(B - A).toContinuousLinearMap‖ / Δ := by
  obtain ⟨c, hc, hbound⟩ :=
    yuWangSamworth_eigenvector_frame_le hu hv hAu hBv hΔ hgap
  exact (norm_sub_le_norm_smul_sub hu hv hc hsign).trans hbound

end YuWangSamworth2015
