/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# A self-adjoint operator bounded below at a real point

If `A` is self-adjoint, `z` is real, and `c ‖x‖ ≤ ‖A x - z x‖` on the domain,
then `z` lies in the resolvent set.

`SelfAdjointResolvent.lean` proves the *non-real* case, where the lower bound
comes for free as `|Im z|`.  Its three steps — injectivity, closed range, dense
range — use only the bound, so they generalise; what does not generalise is the
bound's source.  At a real point there is none, so it becomes a hypothesis that
the caller earns.

That is the shape a spectral-gap argument wants: prove an estimate, obtain a
resolvent point, and let `diag_eq_zero_of_subset_resolventSet` turn resolvent
points into a statement about *every* vector's diagonal measure at once.

Realness is used in exactly one place, the dense-range step.  For non-real `z`
the argument is "a self-adjoint operator has no non-real eigenvalue".  Here
`conj z = z`, so a vector orthogonal to the range is an honest eigenvector at
`z`, and the lower bound kills it directly.

## Provenance

*New.*  The closed-range argument follows `isClosed_range_shiftMap`, with the
lower bound abstracted out of it.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {A : E →ₗ.[ℂ] E} {z : ℂ} {c : ℝ}

omit [CompleteSpace E] in
/-- A lower bound makes `A - z` injective. -/
theorem injective_shiftMap_of_lower_bound (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖) :
    Function.Injective (shiftMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h := hbd x
  rw [show A x - z • (x : E) = shiftMap A z x from rfl, hx, norm_zero] at h
  have hx0 : ‖(x : E)‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg ((x : E))]) (norm_nonneg _)
  exact Subtype.ext (by simpa using hx0)

/-- A lower bound makes the range of `A - z` closed. -/
theorem isClosed_range_shiftMap_of_lower_bound (hA : IsSelfAdjoint A) (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖) :
    IsClosed (Set.range (shiftMap A z)) := by
  apply IsSeqClosed.isClosed
  intro w a hw hlim
  choose x hx using hw
  have hwCauchy : CauchySeq w := hlim.cauchySeq
  have hCauchy : CauchySeq fun n => ((x n : E)) := by
    rw [Metric.cauchySeq_iff] at hwCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hwCauchy (c * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hest := hbd (x m - x n)
    have hcoe : ((x m - x n : A.domain) : E) = (x m : E) - (x n : E) := rfl
    have hAsub : A (x m - x n) = A (x m) - A (x n) := map_sub _ _ _
    have hval : A (x m - x n) - z • ((x m - x n : A.domain) : E) = w m - w n := by
      rw [hAsub, hcoe, smul_sub, ← hx m, ← hx n]
      simp only [shiftMap_apply]
      abel
    rw [hval, hcoe] at hest
    have hd : dist (w m) (w n) < c * ε := hN m hm n hn
    rw [dist_eq_norm] at hd ⊢
    nlinarith [norm_nonneg ((x m : E) - (x n : E))]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hAx : Filter.Tendsto (fun n => A (x n)) Filter.atTop (nhds (a + z • p)) := by
    have hval : ∀ n, A (x n) = w n + z • ((x n : E)) := by
      intro n; rw [← hx n]; simp only [shiftMap_apply]; abel
    simp only [hval]
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

/-- **Dense range, at a real point.**  A vector orthogonal to the range of
`A - z` is an eigenvector at `z` — this is where `conj z = z` is used — and the
lower bound kills it. -/
theorem eq_zero_of_orthogonal_shiftRange_of_real (hA : IsSelfAdjoint A)
    (hzre : (starRingEnd ℂ) z = z) (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖)
    {y : E} (hy : ∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_ℂ = 0) : y = 0 := by
  have hdense : Dense (A.domain : Set E) := hA.dense_domain
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
  have hadj : _root_.LinearPMap.adjoint A ⟨y, hmem⟩ = (starRingEnd ℂ) z • y :=
    _root_.LinearPMap.adjoint_apply_eq hdense ⟨y, hmem⟩ hEq
  have hAy : A ⟨y, hmemA⟩ = z • y := by
    have htrans := (_root_.LinearPMap.ext_iff.mp
      (_root_.LinearPMap.isSelfAdjoint_def.mp hA)).2 (x := y) (hf := hmem) (hg := hmemA)
    rw [← htrans, hadj, hzre]
  have h := hbd ⟨y, hmemA⟩
  rw [hAy, sub_self, norm_zero] at h
  have hy0 : ‖y‖ = 0 := le_antisymm (by nlinarith [norm_nonneg y]) (norm_nonneg _)
  simpa using hy0

/-- **A real point with a lower bound is a resolvent point.** -/
theorem mem_resolventSet_of_lower_bound (hA : IsSelfAdjoint A)
    (hzre : (starRingEnd ℂ) z = z) (hc : 0 < c)
    (hbd : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖) :
    z ∈ resolventSet A := by
  have hinj := injective_shiftMap_of_lower_bound hc hbd
  have hclosed := isClosed_range_shiftMap_of_lower_bound hA hc hbd
  set K : Submodule ℂ E := LinearMap.range (shiftMap A z) with hK
  have hKclosed : IsClosed (K : Set E) := hclosed
  have hproj : K.HasOrthogonalProjection :=
    haveI : CompleteSpace K := hKclosed.completeSpace_coe
    inferInstance
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine eq_zero_of_orthogonal_shiftRange_of_real hA hzre hc hbd fun x => ?_
    have h := hy (shiftMap A z x) ⟨x, rfl⟩
    rwa [inner_eq_zero_symm] at h
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hsurj : Function.Surjective (shiftMap A z) := by
    intro y
    have hyK : y ∈ K := hKtop ▸ Submodule.mem_top
    exact hyK
  -- the algebraic inverse, made bounded by the same estimate
  set e : A.domain ≃ₗ[ℂ] E := LinearEquiv.ofBijective (shiftMap A z) ⟨hinj, hsurj⟩ with he
  have heapp : ∀ x : A.domain, e x = A x - z • (x : E) := fun x => rfl
  have hinvbd : ∀ φ : E, ‖((e.symm φ : A.domain) : E)‖ ≤ c⁻¹ * ‖φ‖ := by
    intro φ
    have h := hbd (e.symm φ)
    rw [show A (e.symm φ) - z • ((e.symm φ : A.domain) : E) = e (e.symm φ) from
      (heapp _).symm, e.apply_symm_apply] at h
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  refine ⟨LinearMap.mkContinuous
    ((A.domain.subtype).comp (e.symm : E →ₗ[ℂ] A.domain)) c⁻¹ hinvbd, ?_, ?_⟩
  · intro ψ
    have hsym : e ψ = A ψ - z • (ψ : E) := heapp ψ
    simp only [LinearMap.mkContinuous_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype]
    rw [← hsym]
    exact congrArg Subtype.val (e.symm_apply_apply ψ)
  · intro φ
    refine ⟨(e.symm φ).2, ?_⟩
    have h := e.apply_symm_apply φ
    rw [heapp] at h
    exact h

end LinearPMap
end TauCeti
