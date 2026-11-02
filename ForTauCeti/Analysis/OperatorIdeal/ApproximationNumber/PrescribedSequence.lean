/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# Operators with a prescribed approximation-number sequence

Accepted `lp.exists_singularValue_diagonalCLM_eq` realises every bounded antitone nonnegative
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
/-- **Extension by zero preserves every approximation number.**

`W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto` is the operator on the ambient space that
agrees with `A` on `W` and vanishes on `Wᗮ`.  Both outer factors are contractions, so no
approximation number can increase; compressing back to `W` recovers `A` exactly, and the
same estimate run in the other direction gives the reverse inequality.

This is the "corestriction is invisible to the approximation numbers" step: an operator
supported on a subspace has the same singular data read on that subspace as read on the
whole space. -/
theorem approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (A : W →L[𝕜] W) (n : ℕ) :
    ((W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto).singularValue n : ℝ) =
      (A.singularValue n : ℝ) := by
  have hsubnorm : ‖W.subtypeL‖₊ ≤ 1 := by exact_mod_cast W.norm_subtypeL_le
  have hprojnorm : ‖W.orthogonalProjectionOnto‖₊ ≤ 1 := by
    exact_mod_cast W.orthogonalProjectionOnto_norm_le
  have hfact : A = W.orthogonalProjectionOnto ∘L
      (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto) ∘L W.subtypeL := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h1 : W.orthogonalProjectionOnto ((x : E)) = x :=
      Subtype.ext (Submodule.starProjection_eq_self_iff.mpr x.2)
    have h2 : W.orthogonalProjectionOnto ((A x : W) : E) = A x :=
      Subtype.ext (Submodule.starProjection_eq_self_iff.mpr (A x).2)
    change A x = W.orthogonalProjectionOnto
        ((A (W.orthogonalProjectionOnto (x : E)) : W) : E)
    rw [h1, h2]
  apply congrArg NNReal.toReal
  refine le_antisymm ?_ ?_
  · calc
      (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto).singularValue n ≤
          ‖W.subtypeL‖₊ * A.singularValue n * ‖W.orthogonalProjectionOnto‖₊ :=
        ContinuousLinearMap.singularValue_comp_comp_le _ _ _ n
      _ ≤ 1 * A.singularValue n * 1 := by gcongr
      _ = A.singularValue n := by simp
  · calc
      A.singularValue n = (W.orthogonalProjectionOnto ∘L
          (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto) ∘L W.subtypeL).singularValue n := by
        rw [← hfact]
      _ ≤ ‖W.orthogonalProjectionOnto‖₊ *
          (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto).singularValue n * ‖W.subtypeL‖₊ :=
        ContinuousLinearMap.singularValue_comp_comp_le _ _ _ n
      _ ≤ 1 * (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto).singularValue n * 1 := by
        gcongr
      _ = (W.subtypeL ∘L A ∘L W.orthogonalProjectionOnto).singularValue n := by simp

/-- **Every bounded antitone nonnegative sequence is an approximation-number sequence**
on an infinite-dimensional real or complex Hilbert space. -/
theorem exists_approximationNumber_eq_of_antitone
    (hinf : ¬ FiniteDimensional 𝕜 E)
    (d : ℕ → ℝ) (h0 : ∀ n, 0 ≤ d n) (hanti : Antitone d) :
    ∃ D : E →L[𝕜] E, ∀ n, (D.singularValue n : ℝ) = d n := by
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
  -- Consume the accepted sequence-space realization.
  let values : ℕ → NNReal := fun n => ⟨d n, h0 n⟩
  have hvalues : Antitone values := fun _ _ h => NNReal.coe_le_coe.mpr (hanti h)
  obtain ⟨coeffs, hcoeffs⟩ :=
    lp.exists_singularValue_diagonalCLM_eq (𝕜 := 𝕜) (p := 2) hvalues
  let Diag := lp.diagonalCLM (p := 2) coeffs
  have hDiagAn : ∀ n, (Diag.singularValue n : ℝ) = d n := fun n =>
    congrArg NNReal.toReal (congrFun hcoeffs n)
  -- Conjugate through the Hilbert-basis identification and extend by zero.
  set U : W →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
    B.repr.toLinearIsometry.toContinuousLinearMap with hU_def
  set U' : lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] W :=
    B.repr.symm.toLinearIsometry.toContinuousLinearMap with hU'_def
  set D₀ : W →L[𝕜] W := U' ∘L Diag ∘L U with hD₀_def
  have hD₀An : ∀ n, (D₀.singularValue n : ℝ) = d n := by
    intro n
    rw [hD₀_def, hU_def, hU'_def,
      ContinuousLinearMap.singularValue_comp_linearIsometryEquiv]
    exact hDiagAn n
  -- Extension by zero to the whole space.
  refine ⟨W.subtypeL ∘L D₀ ∘L W.orthogonalProjectionOnto, fun n => ?_⟩
  rw [approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto W D₀ n]
  exact hD₀An n

end ApproximationNumber
end TauCeti
