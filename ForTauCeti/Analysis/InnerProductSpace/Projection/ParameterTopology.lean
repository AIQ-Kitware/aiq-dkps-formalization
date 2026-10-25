/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.PairedProjectionFamily
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Topology of finite-dimensional projection parameters

Orthogonal projections form a compact space in operator norm. Compatible
projections supported on selected conjugate unitary eigenspace pairs form
a closed subspace. Their joint restriction and extension bijection is a
homeomorphism, including empty eigenspaces and an empty index set.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

omit [FiniteDimensional 𝕜 E] in
/-- Orthogonal projections are closed in operator norm. -/
theorem isClosed_setOf_isStarProjection :
    IsClosed {P : E →L[𝕜] E | IsStarProjection P} := by
  simp only [isStarProjection_iff']
  exact (isClosed_eq (continuous_id.mul continuous_id) continuous_id).inter
    (isClosed_eq continuous_star continuous_id)

/-- The full orthogonal-projection parameter space is compact, including
the zero-dimensional ambient space. -/
theorem isCompact_setOf_isStarProjection :
    IsCompact {P : E →L[𝕜] E | IsStarProjection P} := by
  let := FiniteDimensional.proper 𝕜 (E →L[𝕜] E)
  apply (isCompact_closedBall (0 : E →L[𝕜] E) 1).of_isClosed_subset
    isClosed_setOf_isStarProjection
  intro P hP
  simpa only [Metric.mem_closedBall, dist_zero_right] using hP.norm_le P

instance compactSpace_starProjections :
    CompactSpace {P : E →L[𝕜] E // IsStarProjection P} :=
  isCompact_iff_compactSpace.mp isCompact_setOf_isStarProjection

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- Taking invariant restrictions cannot increase an operator difference.
The ambient and restricted maps need not be projections. -/
theorem _root_.ContinuousLinearMap.norm_sub_le_of_restrictions
    (P Q : E →L[𝕜] E) (N : Submodule 𝕜 E) (A B : N →L[𝕜] N)
    (hA : ∀ x : N, P x = (A x : E)) (hB : ∀ x : N, Q x = (B x : E)) :
    ‖A - B‖ ≤ ‖P - Q‖ := by
  apply (A - B).opNorm_le_bound (norm_nonneg _)
  intro x
  have hdiff : ((A - B) x : E) = (P - Q) x := by
    change (A x : E) - (B x : E) = P x - Q x
    rw [hA, hB]
  calc
    ‖(A - B) x‖ = ‖(P - Q) (x : E)‖ := congrArg norm hdiff
    _ ≤ ‖P - Q‖ * ‖x‖ := (P - Q).le_opNorm (x : E)

omit [CompleteSpace E] in
/-- Idempotents at operator norm distance less than one have equal rank.
Self-adjointness is unnecessary for this perturbation statement. -/
theorem finrank_range_eq_of_idempotent_of_norm_sub_lt_one
    (P Q : E →L[𝕜] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hclose : ‖P - Q‖ < 1) :
    Module.finrank 𝕜 P.range = Module.finrank 𝕜 Q.range := by
  have hle (P Q : E →L[𝕜] E) (hP : IsIdempotentElem P) (hclose : ‖P - Q‖ < 1) :
      Module.finrank 𝕜 P.range ≤ Module.finrank 𝕜 Q.range := by
    let A : P.range →ₗ[𝕜] Q.range := Q.toLinearMap.rangeRestrict.comp P.range.subtype
    apply LinearMap.finrank_le_finrank_of_injective (f := A)
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    change A x = 0 at hx
    have hQx : Q (x : E) = 0 := congrArg (fun y : Q.range => (y : E)) hx
    have hPx : P (x : E) = x := by
      obtain ⟨y, hy⟩ := x.property
      rw [← hy]
      exact congrArg (fun B : E →L[𝕜] E => B y) hP.eq
    have hbound := (P - Q).le_opNorm (x : E)
    have hdiff : (P - Q) (x : E) = x := by
      simp only [sub_apply, hPx, hQx, sub_zero]
    rw [hdiff] at hbound
    apply Subtype.ext
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x : E)])
  exact le_antisymm (hle P Q hP hclose)
    (hle Q P hQ (by simpa only [norm_sub_rev] using hclose))

/-- Projection rank is locally constant in operator norm. Thus every
fixed-rank projection sector is both open and closed. -/
theorem isLocallyConstant_starProjection_finrank :
    IsLocallyConstant (fun P : {P : E →L[𝕜] E // IsStarProjection P} =>
      Module.finrank 𝕜 P.val.range) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro P
  refine ⟨Metric.ball P 1, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, ?_⟩
  intro Q hQ
  apply finrank_range_eq_of_idempotent_of_norm_sub_lt_one Q.val P.val
    Q.property.isIdempotentElem P.property.isIdempotentElem
  simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hQ

/-- Commutation, reflection symmetry and fixed subspace support are
closed conditions on an orthogonal projection. -/
theorem isClosed_unitaryPairedProjectionSpace
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (mu : ι → 𝕜) :
    IsClosed (unitaryPairedProjectionSpace U J mu) := by
  let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
  let S := ⨆ i, N i ⊔ (N i).map J.toLinearMap
  have hcomm : IsClosed {P : E →L[𝕜] E | Commute P (U : E →L[𝕜] E)} :=
    isClosed_eq (continuous_id.mul_const _) (continuous_id.const_mul _)
  have href : IsClosed {P : E →L[𝕜] E | ∀ x, P (J x) = J (P x)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_eq (continuous_id.clm_apply continuous_const)
      (J.continuous.comp (continuous_id.clm_apply continuous_const))
  have hsupp : IsClosed {P : E →L[𝕜] E | ∀ x, P x ∈ S} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact S.closed_of_finiteDimensional.preimage
      (continuous_id.clm_apply continuous_const)
  exact isClosed_setOf_isStarProjection.inter (hcomm.inter (href.inter hsupp))

instance compactSpace_unitaryPairedProjectionSpace
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (mu : ι → 𝕜) :
    CompactSpace (unitaryPairedProjectionSpace U J mu) := by
  apply isCompact_iff_compactSpace.mp
  exact isCompact_setOf_isStarProjection.of_isClosed_subset
    (isClosed_unitaryPairedProjectionSpace U J mu) (fun _ h => h.1)

/-- Independent projection parameters on distinct nonconjugate unitary
eigenspaces give a homeomorphism onto all compatible supported ambient
projections. All spaces carry their operator norm subspace topology. -/
theorem exists_unitary_paired_projection_homeomorph
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hrev : ∀ x, (U : E →L[𝕜] E) (J x) = J (star (U : E →L[𝕜] E) x))
    (mu : ι → 𝕜) (hmu : ∀ i, ‖mu i‖ = 1) (hinj : Function.Injective mu)
    (hconj : ∀ i j, mu i ≠ star (mu j)) :
    let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
    ∃ e : (∀ i, {Q : N i →L[𝕜] N i // IsStarProjection Q}) ≃ₜ
        unitaryPairedProjectionSpace U J mu,
      ∀ Q i (x : N i), (e Q).val x = ((Q i).val x : E) := by
  classical
  let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
  let Params := ∀ i, {Q : N i →L[𝕜] N i // IsStarProjection Q}
  let Space := unitaryPairedProjectionSpace U J mu
  obtain ⟨e, he⟩ := exists_unitary_paired_projection_equiv U J hJ hrev mu hmu hinj hconj
  have hrel (Q : Params) (P : Space) : e Q = P ↔
      ∀ i (x : N i), P.val x = ((Q i).val x : E) := by
    constructor
    · rintro rfl
      exact he Q
    · intro h
      apply e.symm.injective
      apply funext
      intro i
      apply Subtype.ext
      ext x
      simpa only [Equiv.symm_apply_apply] using
        (h i x).symm.trans (by simpa using he (e.symm P) i x)
  have hgraph : IsClosed (Function.graph e) := by
    change IsClosed {z : Params × Space | e z.1 = z.2}
    simp only [hrel]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro x
    exact isClosed_eq
      (continuous_subtype_val.comp continuous_snd |>.clm_apply continuous_const)
      (continuous_subtype_val.comp
        ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).clm_apply
          continuous_const))
  have hf : Continuous e := continuous_of_isClosed_graph hgraph
  exact ⟨e.toHomeomorphOfContinuousClosed hf hf.isClosedMap, he⟩

end TauCeti
