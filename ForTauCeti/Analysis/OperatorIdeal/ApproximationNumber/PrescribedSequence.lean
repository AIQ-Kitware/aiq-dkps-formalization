/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# Operators with a prescribed approximation-number sequence

`TauCeti.approximationNumber_diagOpLp` realises every bounded antitone nonnegative
sequence as the approximation numbers of a diagonal operator on `ℓ²`.  This module
transports that realisation into an arbitrary infinite-dimensional real or complex Hilbert space:
for every bounded antitone nonnegative `d : ℕ → ℝ` there is a bounded operator on the
space whose `n`-th approximation number is exactly `d n`.

The Davis--Kahan 1970 tangent theorem consumes this as the existence half of its directed
tangent representative at infinite trial dimension: the paper prescribes the singular
values `tan θ_j` of `tan Θ₀` and takes an operator with those singular values for
granted.

The transport is by conjugation: a Hilbert basis of the closure of the span of a countable
orthonormal family identifies that closure with `ℓ²`, the diagonal operator is conjugated
through the identification, and the result is extended by zero to the whole space.  Each
step composes with contractions on both sides, so all approximation numbers are preserved
exactly.
-/

public section

open scoped InnerProductSpace
open Submodule

namespace TauCeti
namespace ApproximationNumber

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Sandwiching between contractions does not increase approximation numbers. -/
theorem approximationNumber_comp_contractions_le
    {D F G : Type*}
    [NormedAddCommGroup D] [InnerProductSpace 𝕜 D]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (L : F →L[𝕜] G) {T : E →L[𝕜] F} (R : D →L[𝕜] E)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (n : ℕ) :
    (L ∘L T ∘L R).approximationNumber n ≤ T.approximationNumber n := by
  have h1 : (L ∘L T ∘L R).approximationNumber n ≤
      ‖L‖ * (T ∘L R).approximationNumber n :=
    ContinuousLinearMap.approximationNumber_comp_le_norm_mul L (T ∘L R) n
  have h2 : (T ∘L R).approximationNumber n ≤ T.approximationNumber n * ‖R‖ :=
    T.approximationNumber_comp_le_mul_norm R n
  have hTn : 0 ≤ T.approximationNumber n := T.approximationNumber_nonneg n
  have hTRn : 0 ≤ (T ∘L R).approximationNumber n :=
    (T ∘L R).approximationNumber_nonneg n
  calc
    (L ∘L T ∘L R).approximationNumber n ≤ ‖L‖ * (T ∘L R).approximationNumber n := h1
    _ ≤ 1 * (T ∘L R).approximationNumber n :=
      mul_le_mul_of_nonneg_right hL hTRn
    _ = (T ∘L R).approximationNumber n := one_mul _
    _ ≤ T.approximationNumber n * ‖R‖ := h2
    _ ≤ T.approximationNumber n * 1 := mul_le_mul_of_nonneg_left hR hTn
    _ = T.approximationNumber n := mul_one _

/-- **Every bounded antitone nonnegative sequence is an approximation-number sequence**
on an infinite-dimensional real or complex Hilbert space. -/
theorem exists_approximationNumber_eq_of_antitone
    (hinf : ¬ FiniteDimensional 𝕜 E)
    (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n) (hanti : Antitone d) :
    ∃ D : E →L[𝕜] E, ∀ n, D.approximationNumber n = d n := by
  classical
  -- A countable orthonormal family.
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hwinf : Infinite w := by
    rw [← not_finite_iff_infinite]
    intro hfin
    cases nonempty_fintype w
    exact hinf (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  set emb : ℕ ↪ w := Infinite.natEmbedding w with hemb_def
  set e : ℕ → E := (fun i : w => (b i : E)) ∘ emb with he_def
  have he : Orthonormal 𝕜 e := b.orthonormal.comp emb emb.injective
  -- The closed span of the family, with its Hilbert basis.
  set W : Submodule 𝕜 E := (span 𝕜 (Set.range e)).topologicalClosure with hW_def
  have hWclosed : IsClosed (W : Set E) := (span 𝕜 (Set.range e)).isClosed_topologicalClosure
  have : CompleteSpace W := hWclosed.completeSpace_coe
  have hmem : ∀ n, e n ∈ W := fun n =>
    (span 𝕜 (Set.range e)).le_topologicalClosure (subset_span (Set.mem_range_self n))
  set e' : ℕ → W := fun n => ⟨e n, hmem n⟩ with he'_def
  have he' : Orthonormal 𝕜 e' := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := orthonormal_iff_ite.mp he i j
    rw [Submodule.coe_inner]
    exact h
  have hsp : ⊤ ≤ (span 𝕜 (Set.range e')).topologicalClosure := by
    rintro ⟨xv, hxv⟩ -
    have hx : xv ∈ closure ((span 𝕜 (Set.range e) : Submodule 𝕜 E) : Set E) := by
      have h2 : xv ∈ (W : Set E) := hxv
      rw [hW_def, Submodule.topologicalClosure_coe] at h2
      exact h2
    have himage : Subtype.val ''
        ((span 𝕜 (Set.range e') : Submodule 𝕜 W) : Set W) =
        ((span 𝕜 (Set.range e) : Submodule 𝕜 E) : Set E) := by
      have hmap : (span 𝕜 (Set.range e')).map (W.subtype : W →ₗ[𝕜] E) =
          span 𝕜 (Set.range e) := by
        rw [Submodule.map_span]
        congr 1
        ext y
        constructor
        · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
          exact ⟨n, rfl⟩
        · rintro ⟨n, rfl⟩
          exact ⟨e' n, ⟨n, rfl⟩, rfl⟩
      calc Subtype.val '' ((span 𝕜 (Set.range e') : Submodule 𝕜 W) : Set W) =
          (((span 𝕜 (Set.range e')).map (W.subtype : W →ₗ[𝕜] E) :
            Submodule 𝕜 E) : Set E) := rfl
        _ = ((span 𝕜 (Set.range e) : Submodule 𝕜 E) : Set E) := by rw [hmap]
    have hclos := Topology.IsEmbedding.subtypeVal (p := fun y : E => y ∈ W)
    have hkey : closure ((span 𝕜 (Set.range e') : Submodule 𝕜 W) : Set W) =
        (Subtype.val) ⁻¹'
          (closure (Subtype.val ''
            ((span 𝕜 (Set.range e') : Submodule 𝕜 W) : Set W))) :=
      hclos.closure_eq_preimage_closure_image _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, hkey,
      Set.mem_preimage, himage]
    exact hx
  set B : HilbertBasis ℕ 𝕜 W := HilbertBasis.mk he' hsp with hB_def
  -- The diagonal operator with the prescribed coefficients.
  set c : ℕ → 𝕜 := fun n => (d n : 𝕜) with hc_def
  have hK : (0 : ℝ) ≤ d 0 := h0 0
  have hc : ∀ n, ‖c n‖ ≤ d 0 := fun n => by
    rw [hc_def]
    simp only [RCLike.norm_ofReal, abs_of_nonneg (h0 n)]
    exact hanti (Nat.zero_le n)
  have hcnorm : ∀ n, ‖c n‖ = d n := fun n => by
    rw [hc_def]
    simp only [RCLike.norm_ofReal, abs_of_nonneg (h0 n)]
  have hcanti : Antitone fun n => ‖c n‖ := by
    intro m n hmn
    change ‖c n‖ ≤ ‖c m‖
    rw [hcnorm, hcnorm]
    exact hanti hmn
  set Diag := diagOpLp c hK hc with hDiag_def
  have hDiagAn : ∀ n, Diag.approximationNumber n = d n := fun n => by
    rw [hDiag_def, approximationNumber_diagOpLp c hK hc hcanti n, hcnorm]
  -- Conjugate through the Hilbert-basis identification and extend by zero.
  set U : W →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
    B.repr.toLinearIsometry.toContinuousLinearMap with hU_def
  set U' : lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] W :=
    B.repr.symm.toLinearIsometry.toContinuousLinearMap with hU'_def
  have hUnorm : ‖U‖ ≤ 1 := B.repr.toLinearIsometry.norm_toContinuousLinearMap_le
  have hU'norm : ‖U'‖ ≤ 1 := B.repr.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  have hU'U : U' ∘L U = ContinuousLinearMap.id 𝕜 W := by
    apply ContinuousLinearMap.ext
    intro x
    exact B.repr.symm_apply_apply x
  have hUU' : U ∘L U' = ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 2) := by
    apply ContinuousLinearMap.ext
    intro x
    exact B.repr.apply_symm_apply x
  set D₀ : W →L[𝕜] W := U' ∘L Diag ∘L U with hD₀_def
  have hD₀An : ∀ n, D₀.approximationNumber n = d n := by
    intro n
    refine le_antisymm ?_ ?_
    · rw [← hDiagAn n]
      exact approximationNumber_comp_contractions_le U' U hU'norm hUnorm n
    · rw [← hDiagAn n]
      have hfact : Diag = U ∘L D₀ ∘L U' := by
        rw [hD₀_def]
        apply ContinuousLinearMap.ext
        intro x
        change Diag x = B.repr (B.repr.symm (Diag (B.repr (B.repr.symm x))))
        rw [B.repr.apply_symm_apply, B.repr.apply_symm_apply]
      calc Diag.approximationNumber n = (U ∘L D₀ ∘L U').approximationNumber n := by
            rw [← hfact]
        _ ≤ D₀.approximationNumber n :=
          approximationNumber_comp_contractions_le U U' hUnorm hU'norm n
  -- Extension by zero to the whole space.
  refine ⟨W.subtypeL ∘L D₀ ∘L W.orthogonalProjectionOnto, fun n => ?_⟩
  have hsubnorm : ‖W.subtypeL‖ ≤ 1 := W.norm_subtypeL_le
  have hprojnorm : ‖W.orthogonalProjectionOnto‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    have : ‖(W.orthogonalProjectionOnto x : E)‖ ≤ ‖x‖ := by
      have hcoe : ((W.orthogonalProjectionOnto x : W) : E) = W.starProjection x := rfl
      rw [hcoe]
      exact W.norm_starProjection_apply_le x
    exact this
  refine le_antisymm ?_ ?_
  · rw [← hD₀An n]
    exact approximationNumber_comp_contractions_le W.subtypeL
      W.orthogonalProjectionOnto hsubnorm hprojnorm n
  · rw [← hD₀An n]
    have hfact : D₀ = W.orthogonalProjectionOnto ∘L
        (W.subtypeL ∘L D₀ ∘L W.orthogonalProjectionOnto) ∘L W.subtypeL := by
      apply ContinuousLinearMap.ext
      intro x
      have h1 : W.orthogonalProjectionOnto ((x : E)) = x := by
        apply Subtype.ext
        exact Submodule.starProjection_eq_self_iff.mpr x.2
      have h2 : W.orthogonalProjectionOnto ((D₀ x : W) : E) = D₀ x := by
        apply Subtype.ext
        exact Submodule.starProjection_eq_self_iff.mpr (D₀ x).2
      change D₀ x = W.orthogonalProjectionOnto
          ((D₀ (W.orthogonalProjectionOnto (x : E)) : W) : E)
      rw [h1, h2]
    calc D₀.approximationNumber n = (W.orthogonalProjectionOnto ∘L
        (W.subtypeL ∘L D₀ ∘L W.orthogonalProjectionOnto) ∘L W.subtypeL).approximationNumber
          n := by rw [← hfact]
      _ ≤ (W.subtypeL ∘L D₀ ∘L W.orthogonalProjectionOnto).approximationNumber n :=
        approximationNumber_comp_contractions_le W.orthogonalProjectionOnto
          W.subtypeL hprojnorm hsubnorm n

end ApproximationNumber
end TauCeti
