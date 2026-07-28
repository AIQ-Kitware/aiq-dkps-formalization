/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventBound
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# A self-adjoint operator has real spectrum

The basic criterion: for a self-adjoint `A : E →ₗ.[ℂ] E` and `z` off the real
axis, `A - z` has a bounded two-sided inverse, with `‖(A - z)⁻¹‖ ≤ |Im z|⁻¹`.
Hence `spectrum A ⊆ ℝ`.

The argument is the classical one, in three steps:

1. **the estimate** `‖(A - z) x‖ ≥ |Im z| ‖x‖` — because `⟪A x, x⟫` is real, the
   cross term in `‖(A - Re z) x - i (Im z) x‖²` is purely imaginary and drops
   out, leaving `‖(A - Re z)x‖² + (Im z)² ‖x‖²`;
2. **closed range** — the estimate plus closedness of `A` (self-adjoint
   operators are closed) makes the range of `A - z` closed;
3. **dense range** — a vector orthogonal to the range is an eigenvector of `A`
   for the eigenvalue `conj z`, and self-adjointness forces its eigenvalues to
   be real, so it vanishes.

## Provenance

* **Extraction class:** *new*.  Statement and proof are ours.
* **Spectra influence:** Spectra proves the same criterion
  (`Spectra.YosidaHille.isSelfAdjoint_to_surjective`,
  `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`) and that is what told us
  the criterion was needed here; per
  `docs/planning/tauceti-adaptation-and-spectra-extraction.md`, theorem
  selection is attributable even when the proof is independent.  The proof below
  was written against Mathlib's `LinearPMap` adjoint API and shares no lemma with
  Spectra's, which routes through the Cayley transform and Yosida--Hille.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Estimate
-- The estimate needs no completeness; `Star` on `LinearPMap` does, so the
-- self-adjointness results below open their own section.

/-- For a symmetric operator the quadratic form is real. -/
theorem inner_apply_self_isReal {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (x : A.domain) : (starRingEnd ℂ) ⟪A x, (x : E)⟫_ℂ = ⟪A x, (x : E)⟫_ℂ := by
  rw [inner_conj_symm]
  exact (hsym x x).symm

/-- **The basic estimate.**  `‖(A - z) x‖ ≥ |Im z| ‖x‖` for symmetric `A`.

The cross term vanishes because `⟪A x - (Re z) x, x⟫` is real while the
subtracted vector is `i (Im z) x`. -/
theorem norm_sub_smul_ge_abs_im {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖ := by
  set u : E := A x - (z.re : ℂ) • (x : E) with hu
  have hsplit : A x - z • (x : E) = u - ((z.im : ℂ) * Complex.I) • (x : E) := by
    rw [hu]
    have : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
    rw [show z • (x : E) = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • (x : E) by rw [← this]]
    rw [add_smul]
    abel
  -- `⟪u, x⟫` is real
  have hreal : (starRingEnd ℂ) ⟪u, (x : E)⟫_ℂ = ⟪u, (x : E)⟫_ℂ := by
    rw [hu, inner_sub_left, inner_smul_left, map_sub, map_mul]
    rw [inner_apply_self_isReal hsym x]
    simp [Complex.conj_ofReal]
  -- the cross term is purely imaginary
  have hcross : RCLike.re ⟪u, (((z.im : ℂ) * Complex.I) • (x : E))⟫_ℂ = 0 := by
    have hr : (⟪u, (x : E)⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
    rw [inner_smul_right]
    simp [hr]
  have hsq : ‖A x - z • (x : E)‖ ^ 2
      = ‖u‖ ^ 2 + (z.im) ^ 2 * ‖(x : E)‖ ^ 2 := by
    rw [hsplit, @norm_sub_sq ℂ, hcross, norm_smul]
    simp [Complex.norm_I, Complex.norm_real, mul_pow, sq_abs]
  nlinarith [norm_nonneg (A x - z • (x : E)), norm_nonneg u, norm_nonneg ((x : E)),
    abs_nonneg z.im, sq_abs z.im, sq_nonneg ‖u‖, hsq,
    mul_nonneg (abs_nonneg z.im) (norm_nonneg ((x : E)))]

end Estimate

section SelfAdjoint

variable [CompleteSpace E]

/-- **Dense range.**  A vector orthogonal to the range of `A - z` would make
`z ⟪y, y⟫` real; since `⟪y, y⟫` is a nonnegative real, a non-real `z` forces
`y = 0`.

This is the usual "a self-adjoint operator has no non-real eigenvalue" argument,
arranged so that it never has to name the eigenvector equation — only the
quadratic form appears, which avoids transporting `A† = A` under a dependent
domain membership. -/
theorem eq_zero_of_orthogonal_shiftRange {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) {y : E}
    (hy : ∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_ℂ = 0) : y = 0 := by
  have hdense : Dense (A.domain : Set E) := hA.dense_domain
  -- `⟪conj z • y, x⟫ = ⟪y, A x⟫`, which puts `y` in the adjoint's domain
  have hEq : ∀ x : A.domain, ⟪(starRingEnd ℂ) z • y, (x : E)⟫_ℂ = ⟪y, A x⟫_ℂ := by
    intro x
    have h := hy x
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at h
    rw [inner_smul_left, starRingEnd_self_apply]
    exact h.symm
  have hmem : y ∈ (_root_.LinearPMap.adjoint A).domain :=
    _root_.LinearPMap.mem_adjoint_domain_of_exists _ ⟨(starRingEnd ℂ) z • y, hEq⟩
  have hmemA : y ∈ A.domain := by
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmem
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hdense
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  -- `⟪y, A y⟫` is real, and equals `z * ⟪y, y⟫`
  have hkey : (starRingEnd ℂ) ⟪y, A ⟨y, hmemA⟩⟫_ℂ = ⟪y, A ⟨y, hmemA⟩⟫_ℂ := by
    rw [inner_conj_symm]
    exact hsym ⟨y, hmemA⟩ ⟨y, hmemA⟩
  have hzy : z * ⟪y, y⟫_ℂ = ⟪y, A ⟨y, hmemA⟩⟫_ℂ := by
    have h := hEq ⟨y, hmemA⟩
    rwa [inner_smul_left, starRingEnd_self_apply] at h
  rw [← hzy, map_mul, inner_self_conj] at hkey
  -- `conj z * ⟪y,y⟫ = z * ⟪y,y⟫`
  by_contra hy0
  have hnz : ⟪y, y⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hy0
  have : (starRingEnd ℂ) z = z := mul_right_cancel₀ hnz hkey
  exact hz (Complex.conj_eq_iff_im.mp this)

/-- `A - z` as a linear map out of the domain of `A`. -/
def shiftMap (A : E →ₗ.[ℂ] E) (z : ℂ) : A.domain →ₗ[ℂ] E :=
  A.toFun - z • A.domain.subtype

omit [CompleteSpace E] in
@[simp] theorem shiftMap_apply (A : E →ₗ.[ℂ] E) (z : ℂ) (x : A.domain) :
    shiftMap A z x = A x - z • (x : E) := rfl

/-- **Closed range.**  The estimate turns a convergent sequence in the range into
a Cauchy sequence of preimages; closedness of `A` (which self-adjointness
supplies) identifies the limit. -/
theorem isClosed_range_shiftMap {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    IsClosed (Set.range (shiftMap A z)) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have habs : 0 < |z.im| := abs_pos.mpr hz
  apply IsSeqClosed.isClosed
  intro w a hw hlim
  choose x hx using hw
  -- the preimages are Cauchy, by the estimate applied to differences
  have hwCauchy : CauchySeq w := hlim.cauchySeq
  have hCauchy : CauchySeq fun n => ((x n : E)) := by
    rw [Metric.cauchySeq_iff] at hwCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hwCauchy (|z.im| * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hest := norm_sub_smul_ge_abs_im hsym z (x m - x n)
    have hcoe : ((x m - x n : A.domain) : E) = (x m : E) - (x n : E) := rfl
    have hAsub : A (x m - x n) = A (x m) - A (x n) := map_sub _ _ _
    have hval : A (x m - x n) - z • ((x m - x n : A.domain) : E) = w m - w n := by
      rw [hAsub, hcoe, smul_sub, ← hx m, ← hx n]
      simp only [shiftMap_apply]
      abel
    rw [hval, hcoe] at hest
    have hd : dist (w m) (w n) < |z.im| * ε := hN m hm n hn
    rw [dist_eq_norm] at hd ⊢
    nlinarith [norm_nonneg ((x m : E) - (x n : E))]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hCauchy
  -- `A xₙ = wₙ + z • xₙ → a + z • p`, and the graph of `A` is closed
  have hAx : Filter.Tendsto (fun n => A (x n)) Filter.atTop (nhds (a + z • p)) := by
    have : ∀ n, A (x n) = w n + z • ((x n : E)) := by
      intro n; rw [← hx n]; simp only [shiftMap_apply]; abel
    simp only [this]
    exact hlim.add ((continuous_const_smul z).continuousAt.tendsto.comp hp)
  have hgraph : ((p, a + z • p) : E × E) ∈ A.graph := by
    refine (hA.isClosed).mem_of_tendsto (b := Filter.atTop)
      (f := fun n => ((x n : E), A (x n))) ?_ ?_
    · exact hp.prodMk_nhds hAx
    · filter_upwards with n using A.mem_graph (x n)
  obtain ⟨q, hq⟩ := (A.mem_graph_iff).mp hgraph
  refine ⟨q, ?_⟩
  have hq1 : (q : E) = p := hq.1
  have hq2 : A q = a + z • p := hq.2
  simp only [shiftMap_apply, hq1, hq2]
  abel

omit [CompleteSpace E] in
theorem injective_shiftMap {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : Function.Injective (shiftMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h := norm_sub_smul_ge_abs_im hsym z x
  rw [show A x - z • (x : E) = shiftMap A z x from rfl, hx, norm_zero] at h
  have hxz : ‖(x : E)‖ = 0 := by
    nlinarith [abs_pos.mpr hz, norm_nonneg ((x : E))]
  exact Subtype.ext (by simpa using hxz)

theorem surjective_shiftMap {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : Function.Surjective (shiftMap A z) := by
  have hclosed := isClosed_range_shiftMap hA hz
  set K : Submodule ℂ E := LinearMap.range (shiftMap A z) with hK
  have hKclosed : IsClosed (K : Set E) := hclosed
  have : K.HasOrthogonalProjection :=
    haveI : CompleteSpace K := hKclosed.completeSpace_coe
    inferInstance
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine eq_zero_of_orthogonal_shiftRange hA hz fun x => ?_
    have h := hy (shiftMap A z x) ⟨x, rfl⟩
    rwa [inner_eq_zero_symm] at h
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  intro y
  have : y ∈ K := hKtop ▸ Submodule.mem_top
  exact this

/-- **A self-adjoint operator has real spectrum**, quantitatively: every `z` off
the real axis lies in the resolvent set. -/
theorem mem_resolventSet_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have habs : 0 < |z.im| := abs_pos.mpr hz
  let e : A.domain ≃ₗ[ℂ] E :=
    LinearEquiv.ofBijective (shiftMap A z)
      ⟨injective_shiftMap hsym hz, surjective_shiftMap hA hz⟩
  have hesymm : ∀ y : E, shiftMap A z (e.symm y) = y := fun y => e.apply_symm_apply y
  set Rlin : E →ₗ[ℂ] E := A.domain.subtype ∘ₗ (e.symm : E →ₗ[ℂ] A.domain) with hRlin
  have hbound : ∀ y : E, ‖Rlin y‖ ≤ |z.im|⁻¹ * ‖y‖ := by
    intro y
    have h := norm_sub_smul_ge_abs_im hsym z (e.symm y)
    rw [show A (e.symm y) - z • ((e.symm y : A.domain) : E) = shiftMap A z (e.symm y) from rfl,
      hesymm] at h
    have : ‖Rlin y‖ = ‖((e.symm y : A.domain) : E)‖ := rfl
    rw [this]
    rw [inv_mul_eq_div, le_div_iff₀ habs, mul_comm]
    exact h
  refine ⟨Rlin.mkContinuous (|z.im|⁻¹) hbound, ?_, ?_⟩
  · intro ψ
    have hinv : e.symm ((shiftMap A z) ψ) = ψ := e.symm_apply_apply ψ
    change ((e.symm (A ψ - z • (ψ : E)) : A.domain) : E) = (ψ : E)
    rw [show (A ψ - z • (ψ : E)) = (shiftMap A z) ψ from rfl, hinv]
  · intro φ
    -- `(mkContinuous …) φ` is definitionally `↑(e.symm φ)`, so the whole goal is
    -- definitionally `shiftMap A z (e.symm φ) = φ`.
    exact ⟨(e.symm φ).2, hesymm φ⟩

/-- **The spectrum of a self-adjoint operator is real.** -/
theorem spectrum_subset_real {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    spectrum A ⊆ Complex.ofReal '' Set.univ := by
  intro z hz
  have him : z.im = 0 := by
    by_contra him
    exact hz (mem_resolventSet_of_im_ne_zero hA him)
  exact ⟨z.re, Set.mem_univ _, by simp [Complex.ext_iff, him]⟩

/-- The resolvent of a self-adjoint operator at a non-real point is bounded by
the reciprocal distance to the real axis. -/
theorem norm_resolvent_le_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A (mem_resolventSet_of_im_ne_zero hA hz)‖ ≤ |z.im|⁻¹ := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have habs : 0 < |z.im| := abs_pos.mpr hz
  set hmem := mem_resolventSet_of_im_ne_zero hA hz
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have hdom : resolvent A hmem y ∈ A.domain := resolvent_mem_domain hmem y
  have hsolve : A ⟨resolvent A hmem y, hdom⟩ - z • resolvent A hmem y = y :=
    sub_smul_resolvent hmem y
  have h := norm_sub_smul_ge_abs_im hsym z ⟨resolvent A hmem y, hdom⟩
  rw [show A (⟨resolvent A hmem y, hdom⟩ : A.domain)
      - z • ((⟨resolvent A hmem y, hdom⟩ : A.domain) : E) = y from hsolve] at h
  rw [inv_mul_eq_div, le_div_iff₀ habs, mul_comm]
  exact h

end SelfAdjoint

end LinearPMap
end TauCeti
