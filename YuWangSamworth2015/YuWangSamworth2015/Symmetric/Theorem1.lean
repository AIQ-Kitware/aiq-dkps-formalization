/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import YuWangSamworth2015.GroundedImports

/-!
# Yu--Wang--Samworth Theorem 1

The paper begins by recording the classical Davis--Kahan theorem in the
interval/exterior form used by statisticians.  The repository already proves a
strictly more general unitarily invariant norm statement.  This module gives
that result a source-facing name and then exposes the Frobenius and operator
norm specializations appearing in the paper.
-/

namespace YuWangSamworth2015
open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Yu--Wang--Samworth Theorem 1 in its strongest paper-advertised form:
any unitarily invariant norm may replace the Frobenius norm. -/
theorem yuWangSamworth_theorem1_uiNorm_le
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    N (sinThetaMap U V) ≤ N (B - A) / δ := by
  rw [le_div_iff₀ hδ]
  simpa only [mul_comm] using
    sinTheta_perturbation_le N hA hB hU hV hδ hgap

/-- The printed Theorem 1 conclusion, in Frobenius norm.

Not equation (1): that display is the `r = s = j` single-eigenvector operator-norm
specialization of this theorem, and no declaration writes it literally. -/
theorem yuWangSamworth_theorem1_frobenius_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    sinThetaFrobenius U V ≤
      UnitarilyInvariantSeminorm.frobenius 𝕜 E (B - A) / δ := by
  rw [sinThetaFrobenius_eq]
  exact yuWangSamworth_theorem1_uiNorm_le
      (UnitarilyInvariantSeminorm.frobenius 𝕜 E)
      hA hB hU hV hδ hgap

/-- The operator-norm specialization explicitly mentioned after equation (1). -/
theorem yuWangSamworth_theorem1_opNorm_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B U V a b δ) :
    ‖(sinThetaMap U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ / δ := by
  rw [le_div_iff₀ hδ]
  simpa only [mul_comm] using
    opNorm_sinThetaMap_le_of_intervalGap hA hB hU hV hδ hgap

/-! ## Equation (1)

Equation (1) is the `r = s = j` specialization of Theorem 1: a single
population eigenvector `v` and a single sample eigenvector `v̂` at the same
sorted index, with the *mixed* separation
`δ = min(|λ̂_{j-1} − λ_j|, |λ̂_{j+1} − λ_j|)` in the denominator.  It was the one
displayed result of this paper with no literal wrapper.

Two hypotheses are made explicit here that the printed display leaves implicit.

* The sample side is given as an orthonormal **eigenbasis** `bhat`, not just a
  single eigenvector.  Theorem 1's separation is a condition on the spectrum of
  `Σ̂` restricted to `span{v̂_j}ᗮ`, and knowing only that `v̂_j` is an eigenvector
  does not determine that spectrum.  The paper indexes `λ̂_{j-1}, λ̂_j, λ̂_{j+1}`
  and so has the whole sorted sample spectrum in view; this is that reading.
  The population side needs no basis: `v` is an arbitrary unit eigenvector.
* The separation is stated over every `k ≠ j`.  The printed two-neighbour
  minimum equals it exactly under the interval-position condition
  `λ̂_{j+1} ≤ λ_j ≤ λ̂_{j-1}`, which is `equation1_gap_of_interval_position`
  below.  Without that condition the printed minimum can exceed the true
  exterior separation.  Note that simplicity of `λ̂_j` is *not* needed and never
  was: a repeated `λ̂_j` equals a neighbour, so `|λ̂_j − λ_j|` is already one of
  the two printed terms. -/

omit [FiniteDimensional 𝕜 E] in
/-- Internal helper: a single unit vector is an orthonormal family. -/
private theorem orthonormal_singleton_of_norm_eq_one {u : E} (hu : ‖u‖ = 1) :
    Orthonormal 𝕜 (fun _ : Fin 1 => u) := by
  rw [orthonormal_iff_ite]
  intro i k
  simp [Subsingleton.elim i k, inner_self_eq_norm_sq_to_K, hu]

/-- **Equation (1)**, with the mixed exterior separation stated over every index
other than `j`. -/
theorem yuWangSamworth_equation1_opNorm_le
    {p : ℕ} {Sig Sighat : E →ₗ[𝕜] E}
    (hSig : Sig.IsSymmetric) (hSighat : Sighat.IsSymmetric)
    (bhat : OrthonormalBasis (Fin p) 𝕜 E) (lamhat : Fin p → ℝ)
    (hbhat : ∀ k, Sighat (bhat k) = ((lamhat k : ℝ) : 𝕜) • bhat k)
    {j : Fin p} {v : E} {lam : ℝ} (hv : ‖v‖ = 1)
    (hSigv : Sig v = ((lam : ℝ) : 𝕜) • v)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ k : Fin p, k ≠ j → δ ≤ |lamhat k - lam|) :
    ‖(sinThetaMap (Submodule.span 𝕜 {v})
        (Submodule.span 𝕜 {bhat j})).toContinuousLinearMap‖
      ≤ ‖(Sighat - Sig).toContinuousLinearMap‖ / δ := by
  classical
  set U : Submodule 𝕜 E := Submodule.span 𝕜 {v} with hU
  set V : Submodule 𝕜 E := Submodule.span 𝕜 {bhat j} with hV
  -- `U` is spanned by a one-element eigenfamily.
  have hfamU : TauCeti.IsEigenFamily Sig (fun _ : Fin 1 => lam) (fun _ : Fin 1 => v) :=
    ⟨orthonormal_singleton_of_norm_eq_one hv, fun _ => hSigv⟩
  have hUeq : U = Submodule.span 𝕜 (Set.range fun _ : Fin 1 => v) := by
    rw [hU, Set.range_const]
  have hUinv : IsInvariant Sig U := by rw [hUeq]; exact hfamU.isInvariant_span
  have hUspec : SpectrumIn Sig U (Set.Icc lam lam) := by
    rw [hUeq]
    refine (hfamU.restrictedSpectrum_span_subset hSig).trans ?_
    rintro x ⟨i, rfl⟩
    exact ⟨le_rfl, le_rfl⟩
  -- `V` likewise, and `Vᗮ` is the span of the remaining basis vectors.
  have hbhatj : ‖bhat j‖ = 1 := bhat.orthonormal.1 j
  have hfamV1 : TauCeti.IsEigenFamily Sighat
      (fun _ : Fin 1 => lamhat j) (fun _ : Fin 1 => bhat j) :=
    ⟨orthonormal_singleton_of_norm_eq_one hbhatj, fun _ => hbhat j⟩
  have hVeq1 : V = Submodule.span 𝕜 (Set.range fun _ : Fin 1 => bhat j) := by
    rw [hV, Set.range_const]
  have hVinv : IsInvariant Sighat V := by rw [hVeq1]; exact hfamV1.isInvariant_span
  have hVeq : V = bhat.spanIndices ({j} : Set (Fin p)) := by
    rw [hV, OrthonormalBasis.spanIndices_eq_span, Set.image_singleton]
  have hVperpEq : Vᗮ = Submodule.span 𝕜
      (Set.range fun k : ({j}ᶜ : Set (Fin p)) => bhat (k : Fin p)) := by
    rw [hVeq, bhat.orthogonal_spanIndices, OrthonormalBasis.spanIndices_eq_span,
      Set.image_eq_range]
  have hfamV : TauCeti.IsEigenFamily Sighat
      (fun k : ({j}ᶜ : Set (Fin p)) => lamhat (k : Fin p))
      (fun k : ({j}ᶜ : Set (Fin p)) => bhat (k : Fin p)) :=
    ⟨bhat.orthonormal.comp _ Subtype.val_injective, fun k => hbhat _⟩
  have hVperpSpec : SpectrumIn Sighat Vᗮ
      {mu | mu ∉ Set.Ioo (lam - δ) (lam + δ)} := by
    rw [hVperpEq]
    refine (hfamV.restrictedSpectrum_span_subset hSighat).trans ?_
    rintro x ⟨k, rfl⟩
    have hk : (k : Fin p) ≠ j := fun h => k.2 (Set.mem_singleton_iff.mpr h)
    have hd := hgap _ hk
    intro hmem
    have hlt : |lamhat (k : Fin p) - lam| < δ :=
      abs_lt.mpr ⟨by have := hmem.1; linarith, by have := hmem.2; linarith⟩
    linarith
  exact yuWangSamworth_theorem1_opNorm_le hSig hSighat hUinv hVinv hδ
    ⟨hUspec, hVperpSpec⟩

/-- The printed two-neighbour minimum is the exterior separation, under the
interval-position condition `λ̂_{j+1} ≤ λ_j ≤ λ̂_{j-1}`.

Antitonicity of the sorted sample spectrum does the rest: below `j` the sample
eigenvalues only increase away from `λ_j`, and above `j` they only decrease.
This is the step that turns the printed display's denominator into the
hypothesis `yuWangSamworth_equation1_opNorm_le` takes. -/
theorem equation1_gap_of_interval_position
    {p : ℕ} {lamhat : Fin p → ℝ} (hanti : Antitone lamhat)
    {j : Fin p} {lam delta : ℝ}
    (hlo : ∀ q : Fin p, (q : ℕ) = (j : ℕ) + 1 → lamhat q ≤ lam)
    (hhi : ∀ q : Fin p, (q : ℕ) + 1 = (j : ℕ) → lam ≤ lamhat q)
    (hdlo : ∀ q : Fin p, (q : ℕ) = (j : ℕ) + 1 → delta ≤ |lamhat q - lam|)
    (hdhi : ∀ q : Fin p, (q : ℕ) + 1 = (j : ℕ) → delta ≤ |lamhat q - lam|) :
    ∀ k : Fin p, k ≠ j → delta ≤ |lamhat k - lam| := by
  intro k hk
  have hne : (k : ℕ) ≠ (j : ℕ) := fun h => hk (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `k` sits above `j` in the ordering, so `lamhat k ≥ lamhat (j-1) ≥ lam`
    rcases Nat.lt_or_ge ((k : ℕ) + 1) (j : ℕ) with hstep | hstep
    · have hq : ((j : ℕ) - 1) < p := by omega
      have hmono : lamhat ⟨(j : ℕ) - 1, hq⟩ ≤ lamhat k :=
        hanti (by simp only [Fin.le_def]; omega)
      have hge : lam ≤ lamhat ⟨(j : ℕ) - 1, hq⟩ := hhi _ (by simp; omega)
      have hd := hdhi (⟨(j : ℕ) - 1, hq⟩ : Fin p) (by simp; omega)
      rw [abs_of_nonneg (by linarith)] at hd ⊢
      linarith
    · exact hdhi k (by omega)
  · -- `k` sits below `j`, so `lamhat k ≤ lamhat (j+1) ≤ lam`
    rcases Nat.lt_or_ge ((j : ℕ) + 1) (k : ℕ) with hstep | hstep
    · have hq : ((j : ℕ) + 1) < p := by omega
      have hmono : lamhat k ≤ lamhat ⟨(j : ℕ) + 1, hq⟩ :=
        hanti (by simp only [Fin.le_def]; omega)
      have hle : lamhat ⟨(j : ℕ) + 1, hq⟩ ≤ lam := hlo _ (by simp)
      have hd := hdlo (⟨(j : ℕ) + 1, hq⟩ : Fin p) (by simp)
      rw [abs_of_nonpos (by linarith)] at hd ⊢
      linarith
    · exact hdlo k (by omega)

end DavisKahanTheory
end YuWangSamworth2015
