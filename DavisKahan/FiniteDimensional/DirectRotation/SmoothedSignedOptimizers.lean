/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerPairedPhases

/-!
# Independent signed phase minimizers for arbitrary ambient pairs

Each paired canonical-rotation eigenvector pair admits either sign of its
optimal scalar phase, independently of all other pairs. These choices give
actual global ambient transport minimizers, including repeated angles and
right angles. The frame is derived from the subspaces. This construction
does not assert that one fixed frame lists all equal-angle optimizers.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- In any paired rotation frame of the actual subspace pair, every
independent choice of optimal phase sign gives an ambient global minimizer.
The basis may be adapted to additional commuting spectral data. -/
theorem exists_signed_weighted_transport_in_frame_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    {n m : ℕ} (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
    (theta : Fin n → ℝ) (eps : Fin m → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2))
    (hC0 : ∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (0, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (0, i)))
    (hC1 : ∀ i, Proposition35.section3CosAngleOperator K L (e (.inl (1, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (1, i)))
    (hCf : ∀ j, Proposition35.section3CosAngleOperator K L (e (.inr j)) = e (.inr j))
    (hR0 : ∀ i, R (e (.inl (0, i))) =
      Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i)))
    (hR1 : ∀ i, R (e (.inl (1, i))) =
      Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i)))
    (hRf : ∀ j, R (e (.inr j)) = e (.inr j))
    (hJ0 : ∀ i, K.reflection (e (.inl (0, i))) = e (.inl (1, i)))
    (hJf : ∀ j, K.reflection (e (.inr j)) = (eps j : ℂ) • e (.inr j)) :
    ∀ sign : Fin n → Bool, ∃ T : E ≃ₗᵢ[ℂ] E,
      K.map T.toLinearMap = L ∧
      (∀ r i, (R.trans T.symm) (e (.inl (r, i))) =
        circlePhase 1 (if sign i then optimalWeightedPhase a b (theta i)
          else -optimalWeightedPhase a b (theta i)) • e (.inl (r, i))) ∧
      (∀ j, T (e (.inr j)) = e (.inr j)) ∧
      UnitarilyInvariantSeminorm.nuclear ℂ E E
        ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
          weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ∧
      ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
        UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ≤
          UnitarilyInvariantSeminorm.nuclear ℂ E E
            ((a : ℂ) • S.toLinearMap - (b : ℂ) • LinearMap.id) := by
  classical
  let C := Proposition35.section3CosAngleOperator K L
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  intro sign
  let delta (i : Fin n) := if sign i then optimalWeightedPhase a b (theta i)
    else -optimalWeightedPhase a b (theta i)
  let lam : ((Fin 2 × Fin n) ⊕ Fin m) → ℂ :=
    Sum.elim (fun j => circlePhase 1 (delta j.2)) (fun _ => 1)
  obtain ⟨Z, hZ⟩ := e.exists_linearIsometryEquiv_apply_eq_smul lam (by
    intro j
    rcases j with ⟨r, i⟩ | j
    · exact norm_circlePhase 1 (delta i) zero_le_one
    · exact norm_one)
  have hZp (r : Fin 2) (i : Fin n) : Z (e (.inl (r, i))) =
      circlePhase 1 (delta i) • e (.inl (r, i)) := hZ (.inl (r, i))
  have hZf (j : Fin m) : Z (e (.inr j)) = e (.inr j) := by
    simpa only [lam, Sum.elim_inr, one_smul] using hZ (.inr j)
  have hJ1 (i) : K.reflection (e (.inl (1, i))) = e (.inl (0, i)) := by
    rw [← hJ0, K.reflection_reflection]
  have hcomm (x : E) : Z (K.reflection x) = K.reflection (Z x) := by
    have heq : Z.toLinearMap.comp K.reflection.toLinearMap =
        K.reflection.toLinearMap.comp Z.toLinearMap := by
      apply e.toBasis.ext
      intro j
      change Z (K.reflection (e j)) = K.reflection (Z (e j))
      rcases j with ⟨r, i⟩ | j
      · by_cases hr : r = 0
        · subst r
          rw [hJ0, hZp, hZp, map_smul, hJ0]
        · have hr1 : r = 1 := by omega
          subst r
          rw [hJ1, hZp, hZp, map_smul, hJ1]
      · rw [hJf, map_smul, hZf, hJf]
    exact DFunLike.congr_fun heq x
  have hinv (x : E) : Z.symm (K.reflection x) = K.reflection (Z.symm x) := by
    apply Z.injective
    rw [Z.apply_symm_apply, hcomm, Z.apply_symm_apply]
  let T := Z.symm.trans R
  have hT : K.map T.toLinearMap = L := by
    apply (K.map_eq_iff_intertwines_reflection L T).mpr
    intro x
    change R (Z.symm (K.reflection x)) = L.reflection (R (Z.symm x))
    rw [hinv]
    exact (K.map_eq_iff_intertwines_reflection L R).mp hRmap (Z.symm x)
  have hrel : R.trans T.symm = Z := by
    ext x
    change Z (R.symm (R x)) = Z x
    rw [R.symm_apply_apply]
  have hTf (j : Fin m) : T (e (.inr j)) = e (.inr j) := by
    have hZsf : Z.symm (e (.inr j)) = e (.inr j) := by
      apply Z.injective
      rw [Z.apply_symm_apply, hZf]
    change R (Z.symm (e (.inr j))) = _
    rw [hZsf, show R (e (.inr j)) = _ from hRf j]
  have hcost := nuclear_phaseTransport_eq_sum_weightedPhaseCost a b hab.le theta delta e R Z
    hR0 hR1 hRf hZp hZf
  have hvalue := weightedRotationMinimum_eq_paired_sum a b hab.le C theta hθ e hC0 hC1 hCf
  have hsum : (∑ i, weightedPhaseCost a b (theta i) (delta i)) =
      ∑ i, weightedPhaseMinimum a b (theta i) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [delta]
    split
    · exact weightedPhaseCost_optimal a b (theta i) hb hab.le ⟨(hθ i).1.le, (hθ i).2⟩
    · rw [weightedPhaseCost_neg]
      exact weightedPhaseCost_optimal a b (theta i) hb hab.le ⟨(hθ i).1.le, (hθ i).2⟩
  rw [hsum] at hcost
  simp only [Fintype.card_fin] at hcost
  have hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) = weightedRotationMinimum a b C :=
    hcost.trans hvalue.symm
  refine ⟨T, hT, ?_, hTf, hatt, ?_⟩
  · intro r i
    rw [hrel]
    exact hZp r i
  · intro S hS
    obtain ⟨W, _, hW, hmin⟩ :=
      exists_unitary_minimizing_weighted_transport a b hb hab K L hKL
    rw [hatt, ← hW]
    exact hmin S hS

/-- An arbitrary finite complex subspace pair admits a common paired
rotation frame in which every independent choice of optimal phase sign
is realized by a global optimizer over all ambient transporters.
No supplied block decomposition or simple-angle hypothesis is required. -/
theorem exists_independent_signed_weighted_transport_minimizers_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    ∃ n m : ℕ, ∃ (e : OrthonormalBasis ((Fin 2 × Fin n) ⊕ Fin m) ℂ E)
      (theta : Fin n → ℝ),
      (∀ i, theta i ∈ Set.Ioc 0 (Real.pi / 2)) ∧
      (∀ i, R (e (.inl (0, i))) =
        Complex.exp ((theta i : ℂ) * Complex.I) • e (.inl (0, i))) ∧
      (∀ i, R (e (.inl (1, i))) =
        Complex.exp ((-theta i : ℝ) * Complex.I) • e (.inl (1, i))) ∧
      (∀ j, R (e (.inr j)) = e (.inr j)) ∧
      ∀ sign : Fin n → Bool, ∃ T : E ≃ₗᵢ[ℂ] E,
        K.map T.toLinearMap = L ∧
        (∀ r i, (R.trans T.symm) (e (.inl (r, i))) =
          circlePhase 1 (if sign i then optimalWeightedPhase a b (theta i)
            else -optimalWeightedPhase a b (theta i)) • e (.inl (r, i))) ∧
        (∀ j, T (e (.inr j)) = e (.inr j)) ∧
        UnitarilyInvariantSeminorm.nuclear ℂ E E
          ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
            weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L) ∧
        ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
          UnitarilyInvariantSeminorm.nuclear ℂ E E
              ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) ≤
            UnitarilyInvariantSeminorm.nuclear ℂ E E
              ((a : ℂ) • S.toLinearMap - (b : ℂ) • LinearMap.id) := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  obtain ⟨n, m, e, theta, eps, hθ, hC0, hC1, hCf, hR0, hR1, hRf, hJ0, hJf⟩ :=
    exists_subspace_paired_rotation_reflection_basis_complex K L hKL
  refine ⟨n, m, e, theta, hθ, hR0, hR1, hRf, ?_⟩
  exact exists_signed_weighted_transport_in_frame_complex a b hb hab K L hKL R
    ((K.map_eq_iff_intertwines_reflection L R).mpr
      (nonacuteDirectRotation_reflection_intertwines K L (finiteCrossedDefectEquiv K L hKL)))
    e theta eps hθ hC0 hC1 hCf hR0 hR1 hRf hJ0 hJf

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
