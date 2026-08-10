/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8
import ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-!
# Krein's completion theorem in ambient form

`ForTauCeti/Analysis/InnerProductSpace/Polar/SelfAdjointCompletion.lean` proves
the normalised self-adjoint Krein/Julia column completion on a Hilbert `L²`
direct sum.  This module transports it to the ambient formulation Davis--Kahan
Section 8 actually needs:

> for a bounded self-adjoint `T` on `X` and an orthogonally complemented `P`,
> there is a self-adjoint `T'` agreeing with `T` on `P` and with
> `‖T'‖ = ‖T P_P‖`.

The caller supplies `T`, its self-adjointness and `P`.  No block matrices, no
Douglas factor, no defect operator, no completion certificate, and no
nonvanishing hypothesis: the zero-restriction case is handled internally.

The coordinate system is Mathlib's `Submodule.orthogonalDecomposition`,
`X ≃ₗᵢ[ℂ] WithLp 2 (P × Pᗮ)`.  Being a `LinearIsometryEquiv` it transports the
norm and the inner product for free, which is what the last two steps need.

The load-bearing scalar identity is `‖l2Column A B‖ = ‖T ∘L P.starProjection‖`,
proved rather than assumed: the decomposition is isometric, so the column norm
is `‖T ∘L P.subtypeL‖`, and that equals the ambient restriction norm by two
inequalities -- `P.starProjection` fixes `P`, and it is a contraction.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Krein

open DavisKahanExt
open TauCeti.DavisKahan

universe u

section Ambient

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [CompleteSpace X]

/-- **The restriction norm does not care whether the source is the subspace or
the projection.**  `‖T ∘ ι_P‖ = ‖T P_P‖`: the projection fixes `P`, giving one
inequality, and it is a contraction, giving the other.

Stated over an arbitrary `RCLike` field, with its own binders: the real
Section 8 descent needs it over `ℝ`, and nothing in the argument sees the
scalars. -/
theorem norm_comp_subtypeL_eq_norm_comp_starProjection
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X]
    (T : X →L[𝕜] X) (P : Submodule 𝕜 X) [P.HasOrthogonalProjection]
    [CompleteSpace P] :
    ‖T ∘L P.subtypeL‖ = ‖T ∘L P.starProjection‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun u => ?_
    have hfix : P.starProjection (u : X) = (u : X) :=
      Submodule.starProjection_eq_self_iff.mpr u.2
    have : (T ∘L P.subtypeL) u = (T ∘L P.starProjection) (u : X) := by
      show T (u : X) = T (P.starProjection (u : X))
      rw [hfix]
    rw [this]
    calc ‖(T ∘L P.starProjection) (u : X)‖ ≤ ‖T ∘L P.starProjection‖ * ‖(u : X)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖T ∘L P.starProjection‖ * ‖u‖ := rfl
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    set w : P := ⟨P.starProjection x, P.starProjection_apply_mem x⟩ with hw
    have hval : (T ∘L P.starProjection) x = (T ∘L P.subtypeL) w := rfl
    have hwn : ‖w‖ = ‖P.starProjection x‖ := rfl
    rw [hval]
    calc ‖(T ∘L P.subtypeL) w‖ ≤ ‖T ∘L P.subtypeL‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T ∘L P.subtypeL‖ * ‖x‖ := by
          rw [hwn]
          exact mul_le_mul_of_nonneg_left (P.norm_starProjection_apply_le x)
            (ContinuousLinearMap.opNorm_nonneg _)

variable {Y : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

omit [CompleteSpace X] in
/-- Precomposition by an isometric equivalence does not change the norm. -/
theorem norm_isometryEquiv_comp {Z : Type u} [NormedAddCommGroup Z]
    [InnerProductSpace ℂ Z] (U : X ≃ₗᵢ[ℂ] Y) (S : Z →L[ℂ] X) :
    ‖(U : X →L[ℂ] Y) ∘L S‖ = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun z => ?_
    show ‖U (S z)‖ ≤ ‖S‖ * ‖z‖
    rw [U.norm_map]
    exact S.le_opNorm z
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun z => ?_
    have h : ‖S z‖ = ‖((U : X →L[ℂ] Y) ∘L S) z‖ := by
      show ‖S z‖ = ‖U (S z)‖
      rw [U.norm_map]
    rw [h]
    exact ((U : X →L[ℂ] Y) ∘L S).le_opNorm z

omit [CompleteSpace X] in
/-- **Unitary transport preserves self-adjointness**, across two Hilbert
spaces: the isometric equivalence preserves the inner product. -/
theorem isSelfAdjointOperator_transport (U : X ≃ₗᵢ[ℂ] Y) (K : Y →L[ℂ] Y)
    (hK : IsSelfAdjointOperator K) :
    IsSelfAdjointOperator ((U.symm : Y →L[ℂ] X) ∘L K ∘L (U : X →L[ℂ] Y)) := by
  intro x y
  show ⟪U.symm (K (U x)), y⟫_ℂ = ⟪x, U.symm (K (U y))⟫_ℂ
  rw [← U.inner_map_map (U.symm (K (U x))) y,
    ← U.inner_map_map x (U.symm (K (U y))),
    U.apply_symm_apply, U.apply_symm_apply]
  exact hK (U x) (U y)

omit [CompleteSpace X] in
/-- **Unitary transport preserves the operator norm**, across two Hilbert
spaces. -/
theorem norm_transport (U : X ≃ₗᵢ[ℂ] Y) (K : Y →L[ℂ] Y) :
    ‖(U.symm : Y →L[ℂ] X) ∘L K ∘L (U : X →L[ℂ] Y)‖ = ‖K‖ := by
  set M : X →L[ℂ] X := (U.symm : Y →L[ℂ] X) ∘L K ∘L (U : X →L[ℂ] Y) with hM
  have hMapply : ∀ x : X, M x = U.symm (K (U x)) := fun _ => rfl
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    rw [hMapply, U.symm.norm_map, ← U.norm_map x]
    exact K.le_opNorm _
  · refine ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _) fun y => ?_
    have hy : ‖K y‖ = ‖M (U.symm y)‖ := by
      rw [hMapply, U.apply_symm_apply, U.symm.norm_map]
    rw [hy, ← U.symm.norm_map y]
    exact M.le_opNorm _

omit [CompleteSpace X] in
/-- Scaling a column scales both of its coordinates. -/
theorem l2Column_smul {F G : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (c : ℂ) (a : X →L[ℂ] F) (b : X →L[ℂ] G) :
    TauCeti.l2Column (c • a) (c • b) = c • TauCeti.l2Column a b := by
  ext u
  show WithLp.toLp 2 ((c • a) u, (c • b) u) = c • WithLp.toLp 2 (a u, b u)
  rw [show ((c • a) u, (c • b) u) = c • (a u, b u) from rfl, WithLp.toLp_smul]

/-! ### The ambient completion -/

/-- **Krein's completion theorem, ambient form.**

A bounded self-adjoint `T` on a complex Hilbert space `X` and an orthogonally
complemented closed subspace `P` admit a self-adjoint `T'` that agrees with `T`
on `P` and whose norm is exactly the norm of the restriction `T P_P`.

The caller supplies `T`, its self-adjointness and `P`: no block matrices, no
Douglas factor `Γ`, no defect operator, no completion certificate, and no
nonvanishing hypothesis.  The zero-restriction case is handled internally by
`T' = 0`.

The proof reads the first block column of `T` in the orthogonal decomposition
`X ≃ₗᵢ[ℂ] WithLp 2 (P × Pᗮ)`, normalises it by the exact restriction norm --
which is why `‖l2Column A B‖ = ‖T P_P‖` has to be *proved* -- feeds the
normalised column to `TauCeti.exists_selfAdjoint_norm_one_extension_of_column`,
rescales, and transports back through the isometric equivalence. -/
theorem exists_selfAdjoint_completion_eq_norm_restriction
    (T : X →L[ℂ] X) (hT : IsSelfAdjoint T) (P : Submodule ℂ X)
    [P.HasOrthogonalProjection] :
    ∃ T' : X →L[ℂ] X, IsSelfAdjoint T' ∧
      T' ∘L P.starProjection = T ∘L P.starProjection ∧
      ‖T'‖ = ‖T ∘L P.starProjection‖ := by
  classical
  let : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Pᗮ : Submodule ℂ X) :=
    (Pᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  set r : ℝ := ‖T ∘L P.starProjection‖ with hrdef
  by_cases hr : r = 0
  · refine ⟨0, IsSelfAdjoint.zero _, ?_, ?_⟩
    · have hz : T ∘L P.starProjection = 0 := by
        rw [← norm_eq_zero, ← hrdef]; exact hr
      rw [hz, ContinuousLinearMap.zero_comp]
    · rw [norm_zero]; exact hr.symm
  have hrpos : 0 < r := lt_of_le_of_ne
    (by rw [hrdef]; exact ContinuousLinearMap.opNorm_nonneg _) (Ne.symm hr)
  have hrealsa : ∀ t : ℝ, IsSelfAdjoint ((t : ℂ)) := fun t => Complex.conj_ofReal t
  -- normalise the operator, not the column: the ambient endomorphism algebra is
  -- where scalar norms are available
  set T₀ : X →L[ℂ] X := ((r⁻¹ : ℝ) : ℂ) • T with hT₀def
  have hT₀sa : IsSelfAdjoint T₀ := by
    rw [hT₀def]; exact IsSelfAdjoint.smul (hrealsa _) hT
  have hT₀res : T₀ ∘L P.starProjection = ((r⁻¹ : ℝ) : ℂ) • (T ∘L P.starProjection) := by
    rw [hT₀def, ContinuousLinearMap.smul_comp]
  -- the first block column of the normalised operator
  set U : X ≃ₗᵢ[ℂ] WithLp 2 (P × Pᗮ) := P.orthogonalDecomposition with hUdef
  set Acol : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L T₀ ∘L P.subtypeL with hAdef
  set Bcol : (P : Submodule ℂ X) →L[ℂ] (Pᗮ : Submodule ℂ X) :=
    Pᗮ.orthogonalProjectionOnto ∘L T₀ ∘L P.subtypeL with hBdef
  have hAsa : IsSelfAdjoint Acol := isSelfAdjoint_compressOperator hT₀sa P
  set C : P →L[ℂ] WithLp 2 (P × Pᗮ) := TauCeti.l2Column Acol Bcol with hCdef
  have hCeq : C = (U : X →L[ℂ] WithLp 2 (P × Pᗮ)) ∘L T₀ ∘L P.subtypeL := by
    rw [hCdef, hUdef]
    ext u
    show TauCeti.l2Column Acol Bcol u = P.orthogonalDecomposition (T₀ (u : X))
    rw [TauCeti.l2Column_apply, Submodule.orthogonalDecomposition_apply]
    rfl
  have hCnorm : ‖C‖ = 1 := by
    rw [hCeq, hUdef, norm_isometryEquiv_comp,
      norm_comp_subtypeL_eq_norm_comp_starProjection, hT₀res, norm_smul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ r⁻¹), ← hrdef,
      inv_mul_cancel₀ hr]
  -- the normalised Krein completion, in coordinates
  obtain ⟨K0, hK0sa, hK0norm, hK0col⟩ :=
    TauCeti.exists_selfAdjoint_norm_one_extension_of_column Acol Bcol hAsa
      (TauCeti.l2Column_gram_le_id_of_norm_le_one Acol Bcol (le_of_eq hCnorm))
      hCnorm
  -- transport back to `X`
  set T₁ : X →L[ℂ] X := (U.symm : WithLp 2 (P × Pᗮ) →L[ℂ] X) ∘L K0 ∘L
    (U : X →L[ℂ] WithLp 2 (P × Pᗮ)) with hT₁def
  have hT₁sa : IsSelfAdjoint T₁ := by
    rw [hT₁def]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (isSelfAdjointOperator_transport U K0
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK0sa))
  have hT₁norm : ‖T₁‖ = 1 := by rw [hT₁def, norm_transport, hK0norm]
  have hT₁res : T₁ ∘L P.starProjection = T₀ ∘L P.starProjection := by
    ext x
    show U.symm (K0 (U (P.starProjection x))) = T₀ (P.starProjection x)
    set px : X := P.starProjection x with hpxdef
    have hpx : px ∈ P := P.starProjection_apply_mem x
    set u : P := ⟨px, hpx⟩ with hudef
    have h1 : P.orthogonalProjectionOnto px = u := by
      apply Subtype.ext
      change P.starProjection px = px
      exact Submodule.starProjection_eq_self_iff.mpr hpx
    have h2 : Pᗮ.orthogonalProjectionOnto px = 0 := by
      apply Subtype.ext
      change Pᗮ.starProjection px = (0 : X)
      rw [Submodule.starProjection_orthogonal_apply,
        Submodule.starProjection_eq_self_iff.mpr hpx, sub_self]
    have hUpx : U px = TauCeti.l2Inl (𝕜 := ℂ) (F := ((Pᗮ : Submodule ℂ X) : Type u)) u := by
      rw [hUdef, Submodule.orthogonalDecomposition_apply, h1, h2,
        TauCeti.l2Inl_apply]
    have hKu : K0 (TauCeti.l2Inl (𝕜 := ℂ) (F := ((Pᗮ : Submodule ℂ X) : Type u)) u) = C u :=
      congrArg (fun M : P →L[ℂ] WithLp 2 (P × Pᗮ) => M u) hK0col
    rw [hUpx, hKu, hCeq]
    show U.symm ((U : X →L[ℂ] WithLp 2 (P × Pᗮ)) (T₀ (u : X))) = T₀ px
    rw [hUdef]
    exact P.orthogonalDecomposition.symm_apply_apply _
  -- scale back
  refine ⟨((r : ℝ) : ℂ) • T₁, IsSelfAdjoint.smul (hrealsa _) hT₁sa, ?_, ?_⟩
  · rw [ContinuousLinearMap.smul_comp, hT₁res, hT₀res, smul_smul,
      show (((r : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ)) = 1 by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one],
      one_smul]
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrpos.le, hT₁norm, mul_one]

/-- **The pointwise form on `P`.**  A thin consequence of the capstone: the
completion agrees with `T` at every vector of `P`.  This is the shape the
Davis--Kahan residual reduction consumes. -/
theorem exists_selfAdjoint_completion_eqOn_of_norm_restriction
    (T : X →L[ℂ] X) (hT : IsSelfAdjoint T) (P : Submodule ℂ X)
    [P.HasOrthogonalProjection] :
    ∃ T' : X →L[ℂ] X, IsSelfAdjoint T' ∧ (∀ x ∈ P, T' x = T x) ∧
      ‖T'‖ = ‖T ∘L P.starProjection‖ := by
  obtain ⟨T', hsa, hcol, hnorm⟩ :=
    exists_selfAdjoint_completion_eq_norm_restriction T hT P
  refine ⟨T', hsa, fun x hx => ?_, hnorm⟩
  have hfix : P.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have h := congrArg (fun M : X →L[ℂ] X => M x) hcol
  show T' x = T x
  simpa only [ContinuousLinearMap.comp_apply, hfix] using h

end Ambient

end Krein
end Frontier
end Experimental
end DavisKahan
end TauCeti
