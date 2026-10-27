/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenOptimizerAngles

/-!
# Fixed directions at finite-cost Hilbert Schatten local minima

The full zero-gradient kernel has compact reflecting displacement.
Its finite source-reducing support inherits finite global optimality.
Together with the positive gradient cutoffs, this proves that a local
minimum preserving a subspace is identity. Apply this to the zero-angle
sector to retain arbitrary common and common-orthogonal directions.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal TauCeti.LinearIsometryEquivOperatorNorm

private theorem eq_one_of_schatten_minimal_self_complex
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (q : ℝ) (hq : 1 ≤ q) (K : Submodule ℂ F) (U : F ≃ₗᵢ[ℂ] F)
    (hmin : ∀ T : F ≃ₗᵢ[ℂ] F, K.map T.toLinearMap = K →
      (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (U : F →L[ℂ] F)) ≤
        (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (T : F →L[ℂ] F))) :
    (U : F →L[ℂ] F) = 1 := by
  have h := hmin (LinearIsometryEquiv.refl ℂ F) (by
    change K.map (LinearMap.id : F →ₗ[ℂ] F) = K
    simp only [Submodule.map_id])
  change (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (U : F →L[ℂ] F)) ≤
    (OperatorIdealFamily.schatten ℂ q hq).gauge (1 - (1 : F →L[ℂ] F)) at h
  rw [sub_self, OperatorIdealFamily.gauge_zero] at h
  have hzero := ((OperatorIdealFamily.schatten ℂ q hq).gauge_eq_zero_iff _).mp
    (le_antisymm h zero_le)
  exact (sub_eq_zero.mp hzero).symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Identity is the only finite-cost operator-norm local minimum among
unitaries preserving a prescribed subspace, in arbitrary Hilbert dimension.
The full infinite zero-gradient sector is included. -/
theorem eq_one_of_schatten_isLocalMinOn_self_transport_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = K)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)))
      {T | K.map T.toLinearMap = K} U) : (U : E →L[ℂ] E) = 1 := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let A := G.modulus
  have hGc : IsCompactOperator G := isCompactOperator_schattenUnitaryGradient p.toReal hp1 U (by
    rw [← neg_sub 1 (U : E →L[ℂ] E)]
    exact (OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
      p.toReal hp1.le (1 - (U : E →L[ℂ] E)) hfinite).neg)
  have hAc : IsCompactOperator A := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hseq : A.singularValue = G.singularValue :=
      funext (fun n => ContinuousLinearMap.singularValue_modulus G n)
    rw [hseq]
    exact hGc.tendsto_singularValue
  apply eq_of_eq_on_ker_and_positive_eigenSpans hAc G.isSelfAdjoint_modulus
    G.isPositive_modulus.re_inner_nonneg_left
  · rw [show A.ker = G.ker from G.ker_modulus]
    let Z := G.ker
    let K₀ := K.comap Z.subtype
    let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
    have hK : Z.IsReducing K.starProjection.toLinearMap :=
      K.isReducing_ker_of_reflection_conjugate_eq_neg G
        (isSelfAdjoint_schattenUnitaryGradient _ _)
        (gradient_reflection_conjugate_eq_neg_of_schatten_isLocalMinOn_complex
          p hp hp1 K K U hmap hfinite hmin)
    obtain ⟨V, hV, _, hself⟩ :=
      exists_selfAdjoint_unitary_restriction_schatten_gradient_kernel p.toReal hp1 hp2 U
    obtain ⟨V', hV', hlocal, hVfinite, hVmin⟩ :=
      exists_schatten_locally_minimizing_reducing_restriction p.toReal hp1.le K K Z U hmap
        hfinite hmin hK (U.isReducing_of_restriction Z V hV)
    have heq : V' = V := by
      ext x
      exact (hV' x).trans (hV x).symm
    subst V'
    have hVc := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p.toReal hp1.le
      (1 - (V : Z →L[ℂ] Z))
      hVfinite
    obtain ⟨n, hn⟩ := V.exists_rank_displacement_le_of_isSelfAdjoint hself hVc
    obtain ⟨M, hM, _, hMK, hMV, _, hfix⟩ := exists_finite_transport_support K₀ ⊥ V n hn
    let : FiniteDimensional ℂ M := hM
    obtain ⟨W, hW, hWmap, _, hWlocal⟩ :=
      exists_schatten_locally_minimizing_finite_restriction p.toReal hp1.le K₀ K₀ M V
        hlocal hVfinite hVmin hMK hMV.mem_invtSubmodule
    have hWmin := schatten_isMin_of_isLocalMinOn_finite_complex p hp hp1 hp2
      (K₀.comap M.subtype) (K₀.comap M.subtype) W hWmap hWlocal
    have hWone := eq_one_of_schatten_minimal_self_complex p.toReal hp1.le (K₀.comap M.subtype) W hWmin
    have hVhead (y : M) : V (y : Z) = (y : Z) := by
      have h := congrArg (fun B : M →L[ℂ] M => B y) hWone
      exact (hW y).symm.trans (congrArg Subtype.val h)
    have hVfix (y : Z) : V y = y := by
      calc
        V y = V (M.starProjection y + Mᗮ.starProjection y) :=
          congrArg V (M.starProjection_add_starProjection_orthogonal y).symm
        _ = M.starProjection y + Mᗮ.starProjection y := by
          rw [map_add]
          exact congrArg₂ (fun a b : Z => a + b)
            (hVhead ⟨_, M.starProjection_apply_mem y⟩) (hfix _ (Mᗮ.starProjection_apply_mem y))
        _ = y := M.starProjection_add_starProjection_orthogonal y
    intro x hx
    exact (hV ⟨x, hx⟩).symm.trans (congrArg Subtype.val (hVfix ⟨x, hx⟩))
  · intro ε hε x hx
    obtain ⟨hM, _, _, _, _, V, hV, _, hlocal, hVmin⟩ :=
      exists_minimizing_restriction_on_gradient_cutoff_of_isLocalMinOn_complex
        p hp hp1 hp2 K K U hmap hfinite hmin ε hε
    let M := eigenSpan A (Set.Ioi ε)
    let : FiniteDimensional ℂ M := hM
    have hvalue (W : M ≃ₗᵢ[ℂ] M) :
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
            (1 - (W : M →L[ℂ] M)) ^ p.toReal =
          ENNReal.ofReal (UnitarilyInvariantSeminorm.schatten ℂ M M p
            (LinearMap.id - W.toLinearMap) ^ p.toReal) := by
      rw [OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp]
      rfl
    have hnative (W : M ≃ₗᵢ[ℂ] M)
        (hW : (K.comap M.subtype).map W.toLinearMap = K.comap M.subtype) :
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (V : M →L[ℂ] M)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (W : M →L[ℂ] M)) := by
      apply (ENNReal.rpow_le_rpow_iff (zero_lt_one.trans hp1)).mp
      rw [hvalue, hvalue]
      exact ENNReal.ofReal_le_ofReal (hVmin W hW)
    have hVone := eq_one_of_schatten_minimal_self_complex p.toReal hp1.le (K.comap M.subtype) V hnative
    exact (hV ⟨x, hx⟩).symm.trans (congrArg Subtype.val
      (congrArg (fun B : M →L[ℂ] M => B ⟨x, hx⟩) hVone))

/-- Every finite-cost operator-norm local optimizer fixes all directions
on which the two projections agree, including infinite common-source
and common-orthogonal subspaces. -/
theorem apply_eq_self_of_projections_eq_of_schatten_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≠ ∞)
    (hmin : IsLocalMinOn
      (fun T : E ≃ₗᵢ[ℂ] E => (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)))
      {T | K.map T.toLinearMap = L} U)
    (x : E) (hx : K.starProjection x = L.starProjection x) : U x = x := by
  let S := K.sinAngleOperator L
  let Z := S.ker
  let := K.hasOrthogonalProjection_comap_subtype_of_complete Z
  let := L.hasOrthogonalProjection_comap_subtype_of_complete Z
  have hPQ (y : Z) : K.starProjection (y : E) = L.starProjection y := by
    have h := K.norm_sinAngleOperator_apply L (y : E)
    rw [show K.sinAngleOperator L (y : E) = 0 from y.property, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
  have hK : Z.IsReducing K.starProjection.toLinearMap := by
    apply (K.starProjection_isSymmetric.isReducing_iff_mem_invtSubmodule Z).mpr
    intro y hy
    change S (K.starProjection y) = 0
    have h := congrArg (fun B : E →L[ℂ] E => B y)
      (K.commute_starProjection_sinAngleOperator L).eq
    change K.starProjection (S y) = S (K.starProjection y) at h
    rw [← h, show S y = 0 from hy, map_zero]
  have hpair : K.comap Z.subtype = L.comap Z.subtype := by
    apply Submodule.ext
    intro y
    change (y : E) ∈ K ↔ (y : E) ∈ L
    rw [← K.starProjection_eq_self_iff, hPQ y, L.starProjection_eq_self_iff]
  obtain ⟨V, hV, hlocal, hVfinite, hVmin⟩ :=
    exists_schatten_locally_minimizing_reducing_restriction p.toReal hp1.le K L Z U hmap
      hfinite hmin hK (U.isReducing_ker_of_commute_selfAdjoint S
        (K.isPositive_sinAngleOperator L).isSelfAdjoint
        (commute_sinAngleOperator_of_schatten_isLocalMinOn_complex p hp hp1 hp2 K L U hmap hfinite hmin))
  rw [← hpair] at hlocal hVmin
  have hVone := eq_one_of_schatten_isLocalMinOn_self_transport_complex p hp hp1 hp2
    (K.comap Z.subtype) V hlocal hVfinite hVmin
  have hxZ : x ∈ Z := by
    change S x = 0
    apply norm_eq_zero.mp
    rw [K.norm_sinAngleOperator_apply L, hx, sub_self, norm_zero]
  exact (hV ⟨x, hxZ⟩).symm.trans (congrArg Subtype.val
    (congrArg (fun B : Z →L[ℂ] Z => B ⟨x, hxZ⟩) hVone))

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
