/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedOptimizerRigidity
import DavisKahan.FiniteDimensional.DirectRotation.SmoothedCertificateAverage

/-!
# Spectral separation of every smoothed optimizer

The self-adjoint dual displacement, together with the already fixed
subcritical directions, yields a positive unitary-average equation.
This equation separates distinct principal cosines without presupposing
that the competitor preserves the principal planes.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every ambient weighted transport optimizer satisfies a positive
twisted-average equation with the intrinsic clipped cosine. Both its
relative phase and the grading preserve the original principal cosine.
No acuteness, simplicity, or supplied invariant-block assumption is made. -/
theorem minimizing_weighted_transport_twisted_average_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := (R.trans T.symm : E →L[ℂ] E)
    let C := Proposition35.section3CosAngleOperator K L
    let F := cfc (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ)) C
    ∃ S : unitary (E →L[ℂ] E), IsSelfAdjoint (S : E →L[ℂ] E) ∧
      Commute (S : E →L[ℂ] E) C ∧
      Z + (S : E →L[ℂ] E) * star Z * (S : E →L[ℂ] E) =
        (2 : ℂ) • clippedWeightedCosine a b C ∧
      Commute Z C ∧ (clippedWeightedCosine a b C).IsPositive ∧
      (R : E →L[ℂ] E) = C + Complex.I • ((S : E →L[ℂ] E) * F) ∧
      ∀ c : ℝ, 0 < c → ∀ x : E, C x = (c : ℂ) • x →
        Z ((S : E →L[ℂ] E) x) = (S : E →L[ℂ] E) (Z x) := by
  classical
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z' := R.trans T.symm
  let Z := Unitary.linearIsometryEquiv.symm Z'
  let C := Proposition35.section3CosAngleOperator K L
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨n, m, e, theta, V', hθ, hR0, hR1, hRf, _, hV', hC0, hC1, hCf, hcert, hfixed⟩ :=
    exists_paired_certificate_for_weighted_transport_complex a b hb hab K L hKL T hT
  let V := Unitary.linearIsometryEquiv.symm V'
  let A : E →L[ℂ] E := (a : ℂ) • (R : E →L[ℂ] E)
  have hA0 (i) : A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)) := by
    change (a : ℂ) • R (e (.inl (0, i))) = _
    rw [show R (e (.inl (0, i))) = _ from hR0 i, smul_smul, Complex.exp_ofReal_mul_I]
    congr 1
    simp only [Complex.ofReal_mul]
    ring
  have hA1 (i) : A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)) := by
    change (a : ℂ) • R (e (.inl (1, i))) = _
    rw [show R (e (.inl (1, i))) = _ from hR1 i, smul_smul,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hAf (j) : A (e (.inr j)) = (a : ℂ) • e (.inr j) := by
    change (a : ℂ) • R (e (.inr j)) = _
    rw [show R (e (.inr j)) = _ from hRf j]
  have hpos := (hcert.mp hatt).2
  have hself : IsSelfAdjoint
      (star (V : E →L[ℂ] E) * (A - (b : ℂ) • (Z : E →L[ℂ] E))) := by
    rw [show star (V : E →L[ℂ] E) = (V'.symm : E →L[ℂ] E) from V'.adjoint_eq_symm]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hpos.isSymmetric
  have hfix (i) (hi : b ≤ a * Real.cos (theta i)) (r : Fin 2) :
      (Z : E →L[ℂ] E) (e (.inl (r, i))) = e (.inl (r, i)) := by
    apply T.injective
    change T (T.symm (R (e (.inl (r, i))))) = T (e (.inl (r, i)))
    rw [T.apply_symm_apply, (hfixed hatt).1 i hi r]
  have hfixf (j) : (Z : E →L[ℂ] E) (e (.inr j)) = e (.inr j) := by
    apply T.injective
    change T (T.symm (R (e (.inr j)))) = T (e (.inr j))
    rw [T.apply_symm_apply, (hfixed hatt).2 j]
    exact hRf j
  obtain ⟨S, hS, hSe, havg, hcommB, hBpos⟩ :=
    paired_certificate_twisted_average_complex a b hb hab theta hθ e A hA0 hA1 hAf
      Z V hV' hself hfix hfixf
  let c : ((Fin 2 × Fin n) ⊕ Fin m) → ℝ :=
    Sum.elim (fun j => Real.cos (theta j.2)) (fun _ => 1)
  let beta (j) := min 1 (a * c j / b)
  let B := clippedWeightedCosine a b C
  have hCe (j) : C (e j) = (c j : ℂ) • e j := by
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        exact hC0 i
      · have hr1 : r = 1 := by omega
        subst r
        exact hC1 i
    · simpa only [c, Sum.elim_inr, Complex.ofReal_one, one_smul] using hCf j
  have hBe (j) : B (e j) = (beta j : ℂ) • e j :=
    clippedWeightedCosine_apply_of_apply_eq_smul_complex a b (c j) C (e j) (hCe j)
  have hBeq : B = (basisDiagonal e beta).toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro j
    change B (e j) = basisDiagonal e beta (e j)
    rw [hBe, basisDiagonal_apply_basis]
    rfl
  change (Z : E →L[ℂ] E) + (S : E →L[ℂ] E) * star (Z : E →L[ℂ] E) *
    (S : E →L[ℂ] E) = (2 : ℂ) • (basisDiagonal e beta).toContinuousLinearMap at havg
  change Commute (Z : E →L[ℂ] E) (basisDiagonal e beta).toContinuousLinearMap at hcommB
  change (basisDiagonal e beta).toContinuousLinearMap.IsPositive at hBpos
  rw [← hBeq] at havg hcommB hBpos
  have hfixall (j) (hi : b ≤ a * c j) : (Z : E →L[ℂ] E) (e j) = e j := by
    rcases j with ⟨r, i⟩ | j
    · exact hfix i hi r
    · exact hfixf j
  have hcommC := commute_of_clipped_diagonal_and_fixed_complex e a b (hb.trans hab) hb c
    C B hC hBpos.isSelfAdjoint hCe hBe Z hcommB hfixall
  have hSC : Commute (S : E →L[ℂ] E) C := by
    change (S : E →L[ℂ] E) * C = C * (S : E →L[ℂ] E)
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro j
    change (S : E →L[ℂ] E) (C (e j)) = C ((S : E →L[ℂ] E) (e j))
    rw [hCe, hSe, map_smul, map_smul, hCe, hSe]
    module
  let F := cfc (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ)) C
  have hFe (j) : F (e j) = (Real.sqrt (1 - c j ^ 2) : ℂ) • e j := by
    rw [show F = cfc (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ)) C from rfl,
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ (hCe j)]
    simp only [Complex.ofReal_re]
  have hsqrt (i) : Real.sqrt (1 - Real.cos (theta i) ^ 2) = Real.sin (theta i) := by
    rw [show 1 - Real.cos (theta i) ^ 2 = Real.sin (theta i) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq (theta i)]]
    exact Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi (hθ i).1.le
      (by linarith [(hθ i).2, Real.pi_pos]))
  have hrec : (R : E →L[ℂ] E) = C + Complex.I • ((S : E →L[ℂ] E) * F) := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro j
    change R (e j) = C (e j) + Complex.I • (S : E →L[ℂ] E) (F (e j))
    rw [hCe, hFe, map_smul, hSe]
    rcases j with ⟨r, i⟩ | j
    · by_cases hr : r = 0
      · subst r
        rw [show R (e (.inl (0, i))) = _ from hR0 i]
        dsimp only [c, Sum.elim_inl]
        rw [hsqrt, Complex.exp_ofReal_mul_I]
        norm_num only [ite_true, Complex.ofReal_one]
        module
      · have hr1 : r = 1 := by omega
        subst r
        rw [show R (e (.inl (1, i))) = _ from hR1 i]
        dsimp only [c, Sum.elim_inl]
        rw [hsqrt, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
        simp only [hr, ite_false, Complex.ofReal_neg, Complex.ofReal_one]
        module
    · rw [show R (e (.inr j)) = _ from hRf j]
      norm_num [c]
  refine ⟨S, hS, hSC, havg, hcommC, hBpos, hrec, ?_⟩
  intro d hd x hx
  have hbetapos : 0 < min 1 (a * d / b) :=
    lt_min zero_lt_one (div_pos (mul_pos (hb.trans hab) hd) hb)
  exact (ContinuousLinearMap.rigidity_of_unitary_twisted_average_on_eigenvector
    Z S hS B hBpos havg (min 1 (a * d / b) : ℝ)
      (Complex.ofReal_ne_zero.mpr hbetapos.ne') x
      (clippedWeightedCosine_apply_of_apply_eq_smul_complex a b d C x hx)).2

/-- Every optimizer preserves the principal-cosine eigenspaces. Thus
distinct principal angles cannot be mixed, including the right-angle
defect space and the common fixed space. -/
theorem minimizing_weighted_transport_commutes_cosine_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L)) :
    Commute (T : E →L[ℂ] E) (Proposition35.section3CosAngleOperator K L) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  obtain ⟨S, _, _, _, hZ, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hR : Commute (R : E →L[ℂ] E) C :=
    Proposition35.nonacuteDirectRotation_comm_cosine K L (finiteCrossedDefectEquiv K L hKL)
  have hRstar : Commute (star (R : E →L[ℂ] E)) C := by
    change star (R : E →L[ℂ] E) * C = C * star (R : E →L[ℂ] E)
    simpa only [star_mul, hC.star_eq] using (congrArg star hR.eq).symm
  have hprod := hZ.mul_left hRstar
  have heq : (R.trans T.symm : E →L[ℂ] E) * star (R : E →L[ℂ] E) =
      star (T : E →L[ℂ] E) := by
    rw [show star (R : E →L[ℂ] E) = (R.symm : E →L[ℂ] E) from R.adjoint_eq_symm,
      show star (T : E →L[ℂ] E) = (T.symm : E →L[ℂ] E) from T.adjoint_eq_symm]
    ext x
    change T.symm (R (R.symm x)) = T.symm x
    rw [R.apply_symm_apply]
  rw [heq] at hprod
  change (T : E →L[ℂ] E) * C = C * (T : E →L[ℂ] E)
  have h := congrArg star hprod.eq
  simp only [star_mul, star_star] at h
  change star C * (T : E →L[ℂ] E) = (T : E →L[ℂ] E) * star C at h
  rw [hC.star_eq] at h
  exact h.symm

/-- On each positive principal-cosine eigenspace, every minimizing
relative phase has the exact scalar real part prescribed by clipping.
This includes all subcritical and critical blocks and arbitrary multiplicity. -/
theorem minimizing_weighted_transport_relative_real_part_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (c : ℝ) (hc : 0 < c) (x : E)
    (hx : Proposition35.section3CosAngleOperator K L x = (c : ℂ) • x) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := (R.trans T.symm : E →L[ℂ] E)
    Z x + star Z x = (2 * ((min 1 (a * c / b) : ℝ) : ℂ)) • x := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z := Unitary.linearIsometryEquiv.symm (R.trans T.symm)
  let C := Proposition35.section3CosAngleOperator K L
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨S, hS, _, havg, _, hBpos, _, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hbeta : 0 < min 1 (a * c / b) :=
    lt_min zero_lt_one (div_pos (mul_pos (hb.trans hab) hc) hb)
  have hBx := clippedWeightedCosine_apply_of_apply_eq_smul_complex a b c C x hx
  exact (ContinuousLinearMap.rigidity_of_unitary_twisted_average_on_eigenvector
    Z S hS (clippedWeightedCosine a b C) hBpos havg
      (min 1 (a * c / b) : ℝ) (Complex.ofReal_ne_zero.mpr hbeta.ne') x hBx).1

/-- On positive-cosine eigenspaces the minimizing relative phase also
preserves the canonical rotation eigenphases. Equal-angle multiplicity
does not permit mixing the two opposite rotation phases. -/
theorem minimizing_weighted_transport_relative_commutes_rotation_on_positive_cosine_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (c : ℝ) (hc : 0 < c) (x : E)
    (hx : Proposition35.section3CosAngleOperator K L x = (c : ℂ) • x) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := (R.trans T.symm : E →L[ℂ] E)
    Z (R x) = R (Z x) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z := (R.trans T.symm : E →L[ℂ] E)
  let C := Proposition35.section3CosAngleOperator K L
  let F := cfc (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ)) C
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨S, _, _, _, hZC, _, hrec, hgrade⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hCZx : C (Z x) = (c : ℂ) • Z x := by
    have h := congrArg (fun A : E →L[ℂ] E => A x) hZC.eq
    change Z (C x) = C (Z x) at h
    rw [hx, map_smul] at h
    exact h.symm
  have hF (y : E) (hy : C y = (c : ℂ) • y) :
      F y = (Real.sqrt (1 - c ^ 2) : ℂ) • y := by
    rw [show F = cfc (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ)) C from rfl,
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ hy]
    simp only [Complex.ofReal_re]
  change Z ((R : E →L[ℂ] E) x) = (R : E →L[ℂ] E) (Z x)
  rw [hrec]
  change Z (C x + Complex.I • (S : E →L[ℂ] E) (F x)) =
    C (Z x) + Complex.I • (S : E →L[ℂ] E) (F (Z x))
  rw [hx, hCZx, hF x hx, hF (Z x) hCZx, map_add, map_smul, map_smul,
    map_smul, map_smul, map_smul, hgrade c hc x hx]

/-- If the principal cosine is injective, every minimizing relative phase
commutes with the whole canonical rotation. The fixed directions and
arbitrary repeated positive cosines are included. -/
theorem minimizing_weighted_transport_relative_commutes_rotation_of_injective_cosine_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (hinj : Function.Injective (Proposition35.section3CosAngleOperator K L)) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    Commute (R.trans T.symm : E →L[ℂ] E) (R : E →L[ℂ] E) := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let C := Proposition35.section3CosAngleOperator K L
  have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).toLinearMap
  let e := hC.isSymmetric.eigenvectorBasis rfl
  let c := hC.isSymmetric.eigenvalues rfl
  have he (i) : C (e i) = (c i : ℂ) • e i := hC.isSymmetric.apply_eigenvectorBasis rfl i
  have hc (i) : 0 < c i := by
    have hnonneg : 0 ≤ c i := hC.nonneg_eigenvalues rfl i
    have hne : c i ≠ 0 := by
      intro hz
      have hx : e i = 0 := by
        apply hinj
        change C (e i) = C 0
        rw [he, hz, Complex.ofReal_zero, zero_smul, map_zero]
      exact e.orthonormal.ne_zero i hx
    exact lt_of_le_of_ne hnonneg hne.symm
  apply ContinuousLinearMap.coe_injective
  apply e.toBasis.ext
  intro i
  change (R.trans T.symm) (R (e i)) = R ((R.trans T.symm) (e i))
  exact minimizing_weighted_transport_relative_commutes_rotation_on_positive_cosine_complex
    a b hb hab K L hKL T hT hatt (c i) (hc i) (e i) (he i)

/-- Every minimizing transporter is self-adjoint on the actual right-angle
defect space. The preceding cosine commutation theorem makes this a
reducing restriction, with no coupling to positive angles or fixed space. -/
theorem minimizing_weighted_transport_selfAdjoint_on_right_defect_complex
    (a b : ℝ) (hb : 0 < b) (hab : b < a)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hatt : UnitarilyInvariantSeminorm.nuclear ℂ E E
      ((a : ℂ) • T.toLinearMap - (b : ℂ) • LinearMap.id) =
        weightedRotationMinimum a b (Proposition35.section3CosAngleOperator K L))
    (x : E) (hx : Proposition35.section3CosAngleOperator K L x = 0) :
    (T : E →L[ℂ] E) x = star (T : E →L[ℂ] E) x := by
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
      nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
        unitary (E →L[ℂ] E))
  let Z := (R.trans T.symm : E →L[ℂ] E)
  let C := Proposition35.section3CosAngleOperator K L
  let B := clippedWeightedCosine a b C
  let F := cfc (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ)) C
  have hC : IsSelfAdjoint C :=
    ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  let : IsStarNormal C := hC.isStarNormal
  obtain ⟨S, hS, hSC, havg, hZC, _, hrec, _⟩ :=
    minimizing_weighted_transport_twisted_average_complex a b hb hab K L hKL T hT hatt
  have hSS (y : E) : (S : E →L[ℂ] E) ((S : E →L[ℂ] E) y) = y := by
    have h := congrArg (fun A : E →L[ℂ] E => A y) (Unitary.star_mul_self_of_mem S.property)
    rwa [hS.star_eq] at h
  have hSker (y : E) (hy : C y = 0) : C ((S : E →L[ℂ] E) y) = 0 := by
    have h := congrArg (fun A : E →L[ℂ] E => A y) hSC.eq
    change (S : E →L[ℂ] E) (C y) = C ((S : E →L[ℂ] E) y) at h
    rw [hy, map_zero] at h
    exact h.symm
  have hFker (y : E) (hy : C y = 0) : F y = y := by
    have h := ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal
      (fun z : ℂ => ((Real.sqrt (1 - z.re ^ 2) : ℝ) : ℂ))
      (show C y = (0 : ℂ) • y by simpa only [zero_smul] using hy)
    simpa only [Complex.zero_re, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
      Real.sqrt_one, Complex.ofReal_one, one_smul] using h
  have hBker (y : E) (hy : C y = 0) : B y = 0 := by
    have h := clippedWeightedCosine_apply_of_apply_eq_smul_complex a b 0 C y
      (by simpa only [Complex.ofReal_zero, zero_smul] using hy)
    simpa using h
  have hRker (y : E) (hy : C y = 0) : R y = Complex.I • (S : E →L[ℂ] E) y := by
    change (R : E →L[ℂ] E) y = _
    rw [hrec]
    change C y + Complex.I • (S : E →L[ℂ] E) (F y) = _
    rw [hy, hFker y hy, zero_add]
  have hRstar (y : E) (hy : C y = 0) : star (R : E →L[ℂ] E) y =
      -Complex.I • (S : E →L[ℂ] E) y := by
    apply R.injective
    rw [show star (R : E →L[ℂ] E) = (R.symm : E →L[ℂ] E) from R.adjoint_eq_symm]
    change R (R.symm y) = R (-Complex.I • (S : E →L[ℂ] E) y)
    rw [R.apply_symm_apply, map_smul, hRker _ (hSker y hy), hSS, smul_smul]
    simp
  have hZstarC : Commute (star Z) C := by
    change star Z * C = C * star Z
    have h := congrArg star hZC.eq
    simp only [star_mul] at h
    change star C * star Z = star Z * star C at h
    rw [hC.star_eq] at h
    exact h.symm
  have hCZstar : C (star Z x) = 0 := by
    have h := congrArg (fun A : E →L[ℂ] E => A x) hZstarC.eq
    change star Z (C x) = C (star Z x) at h
    rw [hx, map_zero] at h
    exact h.symm
  have hrel := congrArg (fun A : E →L[ℂ] E => A ((S : E →L[ℂ] E) x)) havg
  change Z ((S : E →L[ℂ] E) x) +
    (S : E →L[ℂ] E) (star Z ((S : E →L[ℂ] E) ((S : E →L[ℂ] E) x))) =
      (2 : ℂ) • B ((S : E →L[ℂ] E) x) at hrel
  rw [hSS, hBker _ (hSker x hx), smul_zero] at hrel
  have hTformula : (T : E →L[ℂ] E) = (R : E →L[ℂ] E) * star Z := by
    rw [show star Z = ((R.trans T.symm).symm : E →L[ℂ] E) from
      (R.trans T.symm).adjoint_eq_symm]
    ext y
    change T y = R (R.symm (T y))
    rw [R.apply_symm_apply]
  have hTstarformula := congrArg star hTformula
  simp only [star_mul, star_star] at hTstarformula
  calc
    (T : E →L[ℂ] E) x = Complex.I • (S : E →L[ℂ] E) (star Z x) := by
      rw [hTformula]
      exact hRker _ hCZstar
    _ = -Complex.I • Z ((S : E →L[ℂ] E) x) := by
      rw [eq_neg_of_add_eq_zero_right hrel, smul_neg, neg_smul]
    _ = star (T : E →L[ℂ] E) x := by
      rw [hTstarformula]
      change _ = Z (star (R : E →L[ℂ] E) x)
      rw [hRstar x hx, map_smul]

/-- All global Charbonnier transport minimizers preserve the principal
cosine operator. This excludes mixing between unequal principal angles
and between the right-angle, positive-angle, and fixed summands. -/
theorem smoothed_minimizer_commutes_cosine_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap) :
    Commute (T : E →L[ℂ] E) (Proposition35.section3CosAngleOperator K L) := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  exact minimizing_weighted_transport_commutes_cosine_complex a a⁻¹
    (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha)
    K L hKL T hT (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin)

/-- Every positive-cosine eigenspace of every global Charbonnier minimizer
has the prescribed relative real part, including multiplicities and the
critical endpoint. At a supercritical angle the scalar is `eta² cos theta`. -/
theorem smoothed_minimizer_relative_real_part_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap)
    (c : ℝ) (hc : 0 < c) (x : E)
    (hx : Proposition35.section3CosAngleOperator K L x = (c : ℂ) • x) :
    let R := Unitary.linearIsometryEquiv
      (⟨nonacuteDirectRotation K L (finiteCrossedDefectEquiv K L hKL),
        nonacuteDirectRotation_mem_unitary K L (finiteCrossedDefectEquiv K L hKL)⟩ :
          unitary (E →L[ℂ] E))
    let Z := (R.trans T.symm : E →L[ℂ] E)
    Z x + star Z x =
      (2 * ((min 1 ((smoothingRadius tau) ^ 2 * c) : ℝ) : ℂ)) • x := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  have h := minimizing_weighted_transport_relative_real_part_complex a a⁻¹
    (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha)
    K L hKL T hT (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin)
      c hc x hx
  have hcoef : a * c / a⁻¹ = a ^ 2 * c := by rw [div_inv_eq_mul]; ring
  simpa only [hcoef] using h

/-- On the right-angle defect space every global Charbonnier optimizer
is a self-adjoint unitary restriction. This includes all multiplicities
and imposes no choice of a defect-space identification. -/
theorem smoothed_minimizer_selfAdjoint_on_right_defect_complex
    (tau : ℝ) (htau : 0 < tau)
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (hmin : ∀ S : E ≃ₗᵢ[ℂ] E, K.map S.toLinearMap = L →
      smoothedDisplacementCost tau T.toLinearMap ≤ smoothedDisplacementCost tau S.toLinearMap)
    (x : E) (hx : Proposition35.section3CosAngleOperator K L x = 0) :
    (T : E →L[ℂ] E) x = star (T : E →L[ℂ] E) x := by
  let a := smoothingRadius tau
  have ha : 1 < a := one_lt_smoothingRadius tau htau
  have ha0 : 0 < a := zero_lt_one.trans ha
  exact minimizing_weighted_transport_selfAdjoint_on_right_defect_complex a a⁻¹
    (inv_pos.mpr ha0) (((inv_lt_one₀ ha0).mpr ha).trans ha)
    K L hKL T hT (smoothed_minimizer_weighted_cost_eq_complex tau htau K L hKL T hT hmin) x hx

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
