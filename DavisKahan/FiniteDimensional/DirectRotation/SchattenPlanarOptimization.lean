/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseTransport
import DavisKahan.FiniteDimensional.DirectRotation.SchattenPhaseCriticalAngle
import TauCeti.Analysis.InnerProductSpace.NormalOperator
import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Eigenphase budgets for complex planar transport

A unitary transporting a line through angle `theta` must spend at least
`2 * theta` in the sum of its absolute eigenphases. This relates arbitrary
planar competitors to the attained scalar-phase minimum.
-/

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open TauCeti.DavisKahan1970.Section4Examples
open scoped ComplexConjugate ENNReal

noncomputable section

private theorem norm_phase_average_lower_bound (a b s t : ℝ) (hst : s + t = 1) :
    Real.cos ((a - b) / 2) ≤
      ‖(s : ℂ) * Complex.exp ((a : ℂ) * Complex.I) +
        (t : ℂ) * Complex.exp ((b : ℂ) * Complex.I)‖ := by
  let sigma := (a + b) / 2
  let z := Complex.exp ((-sigma : ℝ) * Complex.I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I (-sigma)
  have hphase (u : ℝ) : z * Complex.exp ((u : ℂ) * Complex.I) =
      Complex.exp (((u - sigma : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrot : z * ((s : ℂ) * Complex.exp ((a : ℂ) * Complex.I) +
      (t : ℂ) * Complex.exp ((b : ℂ) * Complex.I)) =
      (s : ℂ) * Complex.exp (((a - sigma : ℝ) : ℂ) * Complex.I) +
        (t : ℂ) * Complex.exp (((b - sigma : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (s : ℂ) * (z * Complex.exp ((a : ℂ) * Complex.I)) +
          (t : ℂ) * (z * Complex.exp ((b : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [hphase, hphase]
  have hre (u : ℝ) : (Complex.exp ((u : ℂ) * Complex.I)).re = Real.cos u := by
    rw [Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have hreal : (z * ((s : ℂ) * Complex.exp ((a : ℂ) * Complex.I) +
      (t : ℂ) * Complex.exp ((b : ℂ) * Complex.I))).re = Real.cos ((a - b) / 2) := by
    rw [hrot]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hre]
    rw [show a - sigma = (a - b) / 2 by dsimp [sigma]; ring,
      show b - sigma = -((a - b) / 2) by dsimp [sigma]; ring, Real.cos_neg]
    rw [← add_mul, hst, one_mul]
  rw [← hreal]
  exact (Complex.re_le_norm _).trans_eq (by rw [norm_mul, hz, one_mul])

/-- The absolute eigenphases of a planar line transport have total angle
at least twice the angle of that line. This scalar form applies to its
spectral average on a unit vector. -/
theorem eigenphase_budget_of_phase_average (theta a b s t : ℝ)
    (hθ : theta ∈ Icc 0 (Real.pi / 2)) (hst : s + t = 1)
    (havg : ‖(s : ℂ) * Complex.exp ((a : ℂ) * Complex.I) +
        (t : ℂ) * Complex.exp ((b : ℂ) * Complex.I)‖ = Real.cos theta) :
    2 * theta ≤ |a| + |b| := by
  by_contra hbudget
  have hbad : |a| + |b| < 2 * theta := lt_of_not_ge hbudget
  have hgap : |(a - b) / 2| < theta := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_sub a b]
  have hc : Real.cos theta < Real.cos ((a - b) / 2) := by
    calc
      Real.cos theta < Real.cos |(a - b) / 2| :=
        Real.strictAntiOn_cos
          ⟨abs_nonneg _, by linarith [hθ.2, Real.pi_pos]⟩
          ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩ hgap
      _ = _ := Real.cos_abs _
  have hnorm := norm_phase_average_lower_bound a b s t hst
  rw [havg] at hnorm
  exact (not_lt_of_ge hnorm) hc

private theorem inner_eq_spectral_average
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (T : E →ₗ[ℂ] E) (mu : ι → ℂ) (hmu : ∀ i, T (b i) = mu i • b i) (x : E) :
    inner ℂ x (T x) = ∑ i, ((‖b.repr x i‖ ^ 2 : ℝ) : ℂ) * mu i := by
  have himage : T x = ∑ i, (b.repr x i * mu i) • b i := by
    calc
      T x = T (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, hmu, smul_smul]
  rw [himage, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmul : b.repr x i * inner ℂ x (b i) = ((‖b.repr x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [b.repr_apply_apply, ← inner_conj_symm x (b i), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [inner_smul_right]
  calc
    (b.repr x i * mu i) * inner ℂ x (b i) =
        (b.repr x i * inner ℂ x (b i)) * mu i := by ring
    _ = _ := by rw [hmul]

/-- A complex planar unitary admits an orthonormal eigenbasis with phases
in the principal range. Their absolute values have the transport budget
whenever a unit vector witnesses the angle of the transported line. -/
theorem exists_planar_eigenphase_budget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (hE : Module.finrank ℂ E = 2)
    (W : E ≃ₗᵢ[ℂ] E) (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2))
    (x : E) (hx : ‖x‖ = 1) (hinner : ‖inner ℂ x (W x)‖ = Real.cos theta) :
    ∃ (b : OrthonormalBasis (Fin 2) ℂ E) (a : Fin 2 → ℝ),
      (∀ i, |a i| ≤ Real.pi) ∧
      (∀ i, W (b i) = Complex.exp ((a i : ℂ) * Complex.I) • b i) ∧
      2 * theta ≤ |a 0| + |a 1| := by
  let : IsStarNormal W.toLinearMap := by
    constructor
    change W.toLinearMap.adjoint * W.toLinearMap = W.toLinearMap * W.toLinearMap.adjoint
    rw [W.adjoint_toLinearMap_eq_symm]
    ext y
    simp
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal W.toLinearMap
      (show Fintype.card (Fin 2) = Module.finrank ℂ E by simp [hE])
  have hnorm (i : Fin 2) : ‖mu i‖ = 1 := by
    have h := W.norm_map (b i)
    rw [show W (b i) = mu i • b i from hmu i, norm_smul,
      b.orthonormal.1 i, mul_one] at h
    exact h
  have hphase (i : Fin 2) : Complex.exp (((mu i).arg : ℂ) * Complex.I) = mu i := by
    have h := Complex.norm_mul_exp_arg_mul_I (mu i)
    simpa only [hnorm i, Complex.ofReal_one, one_mul] using h
  refine ⟨b, fun i => (mu i).arg, fun i => Complex.abs_arg_le_pi _, ?_, ?_⟩
  · intro i
    rw [hphase]
    exact hmu i
  · have hsum := b.sum_sq_norm_inner_right x
    simp only [Fin.sum_univ_two, hx, one_pow] at hsum
    have hweights : ‖b.repr x 0‖ ^ 2 + ‖b.repr x 1‖ ^ 2 = 1 := by
      simpa only [b.repr_apply_apply] using hsum
    have havg := inner_eq_spectral_average b W.toLinearMap mu hmu x
    rw [Fin.sum_univ_two, ← hphase 0, ← hphase 1] at havg
    apply eigenphase_budget_of_phase_average theta ((mu 0).arg) ((mu 1).arg)
      (‖b.repr x 0‖ ^ 2) (‖b.repr x 1‖ ^ 2) hθ hweights
    rw [← havg]
    exact hinner

private theorem schatten_planar_eigenbasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (b : OrthonormalBasis (Fin 2) ℂ E)
    (W : E ≃ₗᵢ[ℂ] E) (mu : Fin 2 → ℂ) (hmu : ∀ i, W (b i) = mu i • b i)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) =
      (‖1 - mu 0‖ ^ p.toReal + ‖1 - mu 1‖ ^ p.toReal) ^ (1 / p.toReal) := by
  let A : E →ₗ[ℂ] E := LinearMap.id - W.toLinearMap
  have hE : Module.finrank ℂ E = 2 := by
    rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hdiag : A = Matrix.toLin b.toBasis b.toBasis
      (Matrix.diagonal ![1 - mu 0, 1 - mu 1]) := by
    apply b.toBasis.ext
    intro i
    simp only [Matrix.toLin_self, Matrix.diagonal_apply, Fin.sum_univ_two]
    fin_cases i <;> simp [A, hmu, sub_smul]
  rw [UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp]
  congr 1
  change A.singularValues.sum (fun _ s => s ^ p.toReal) = _
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [← A.sum_fin_singularValues (fun s : ℝ => s ^ p.toReal)
    (Real.zero_rpow hp0.ne'), hE, Fin.sum_univ_two]
  rcases le_total ‖1 - mu 1‖ ‖1 - mu 0‖ with hle | hle
  · rw [hdiag, Matrix.singularValues_toLin_diagonal_fin_two b hle]
    simp
  · have hswap : A = Matrix.toLin (b.reindex (Equiv.swap 0 1)).toBasis
        (b.reindex (Equiv.swap 0 1)).toBasis (Matrix.diagonal ![1 - mu 1, 1 - mu 0]) := by
      apply (b.reindex (Equiv.swap 0 1)).toBasis.ext
      intro i
      simp only [Matrix.toLin_self, Matrix.diagonal_apply, Fin.sum_univ_two]
      fin_cases i <;> simp [A, hmu, sub_smul]
    rw [hswap, Matrix.singularValues_toLin_diagonal_fin_two _ hle]
    simp [add_comm]

private theorem norm_one_sub_phase_eq_chord_abs (a : ℝ) (ha : |a| ≤ Real.pi) :
    ‖1 - Complex.exp ((a : ℂ) * Complex.I)‖ = phaseChord |a| := by
  rw [norm_sub_rev, mul_comm (a : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold phaseChord
  rcases le_total 0 a with h0 | h0
  · have hs : 0 ≤ Real.sin (a / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [le_abs_self a, Real.pi_pos])
    rw [abs_of_nonneg h0, abs_of_nonneg hs]
  · have hs : Real.sin (a / 2) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
        (by linarith [neg_abs_le a, Real.pi_pos])
    rw [abs_of_nonpos h0, neg_div, Real.sin_neg, abs_of_nonpos hs]

/-- The attained scalar cost is a lower bound for every complex planar
unitary moving a unit vector through the prescribed projective angle.
The competing unitary has no scalar-phase restriction. -/
theorem phaseMinimum_le_schatten_planar
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (hE : Module.finrank ℂ E = 2)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (W : E ≃ₗᵢ[ℂ] E) (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2))
    (x : E) (hx : ‖x‖ = 1) (hinner : ‖inner ℂ x (W x)‖ = Real.cos theta) :
    phaseMinimum p.toReal theta ^ (1 / p.toReal) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p (LinearMap.id - W.toLinearMap) := by
  obtain ⟨b, a, ha, hWa, hbudget⟩ := exists_planar_eigenphase_budget hE W theta hθ x hx hinner
  rw [schatten_planar_eigenbasis b W (fun i => Complex.exp ((a i : ℂ) * Complex.I)) hWa p hp,
    norm_one_sub_phase_eq_chord_abs (a 0) (ha 0),
    norm_one_sub_phase_eq_chord_abs (a 1) (ha 1)]
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  exact Real.rpow_le_rpow (phaseMinimum_nonneg p.toReal theta hp1 hθ)
    (phaseMinimum_le_chord_sum p.toReal theta |a 0| |a 1| hp1 hθ.1
      ⟨abs_nonneg _, ha 0⟩ ⟨abs_nonneg _, ha 1⟩ hbudget) (by positivity)

private def sourceUnitVector : ComplexPlane :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    ((EuclideanSpace.basisFun (Fin 2) ℂ 0) + EuclideanSpace.basisFun (Fin 2) ℂ 1)

private theorem sourceUnitVector_apply (i : Fin 2) : sourceUnitVector i = (Real.sqrt 2 : ℂ)⁻¹ := by
  fin_cases i <;> simp [sourceUnitVector, EuclideanSpace.basisFun_apply]

private theorem sourceUnitVector_norm : ‖sourceUnitVector‖ = 1 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hsq := EuclideanSpace.norm_sq_eq sourceUnitVector
  simp only [Fin.sum_univ_two, sourceUnitVector_apply, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hs.le, inv_pow] at hsq
  rw [Real.sq_sqrt (by norm_num)] at hsq
  have hsq' : ‖sourceUnitVector‖ ^ 2 = 1 := by convert hsq using 1; norm_num
  nlinarith [norm_nonneg sourceUnitVector]

private theorem sourceUnitVector_span : Submodule.span ℂ {sourceUnitVector} =
    ComplexTraceOptimality.sourceLine := by
  change Submodule.span ℂ {(Real.sqrt 2 : ℂ)⁻¹ •
      ((EuclideanSpace.basisFun (Fin 2) ℂ 0) + EuclideanSpace.basisFun (Fin 2) ℂ 1)} = _
  rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 (by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity : Real.sqrt 2 ≠ 0))))]
  rfl

private theorem sourceUnitVector_inner_rotation (theta : ℝ) :
    inner ℂ sourceUnitVector ((scalarPhaseTransport theta 0) sourceUnitVector) =
      (Real.cos theta : ℂ) := by
  change inner ℂ sourceUnitVector
    ((scalarPhaseTransport theta 0).toLinearMap sourceUnitVector) = _
  rw [scalarPhaseTransport_toLinearMap,
    TauCeti.DavisKahan1970.Section4Examples.example42Competitor_eq_phase_smul]
  simp only [TauCeti.DavisKahan1970.Section4Examples.example42Phase_zero,
    one_smul]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    TauCeti.DavisKahan1970.Section4Examples.example42DirectRotation,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    sourceUnitVector_apply]
  simp [TauCeti.DavisKahan1970.Section4Examples.example42Phase,
    Real.cos_neg, Real.sin_neg, Complex.conj_ofReal]
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hinv : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by rw [inv_pow, hs2]
  calc
    _ = 2 * Complex.cos (theta : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 := by ring
    _ = _ := by rw [hinv]; ring

/-- A unit source vector witnesses the projective angle for every unitary
transporting the model source line to its target. -/
theorem sourceLine_exists_angle_witness (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    ∃ x ∈ ComplexTraceOptimality.sourceLine, ‖x‖ = 1 ∧
      ∀ W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
        ComplexTraceOptimality.sourceLine.map W.toLinearMap =
          ComplexTraceOptimality.targetLine theta →
        ‖inner ℂ x (W x)‖ = Real.cos theta := by
  refine ⟨sourceUnitVector, ?_, sourceUnitVector_norm, ?_⟩
  · rw [← sourceUnitVector_span]
    exact Submodule.mem_span_singleton_self _
  · intro W hW
    have hmap : (Submodule.span ℂ {sourceUnitVector}).map W.toLinearMap =
        (Submodule.span ℂ {sourceUnitVector}).map (scalarPhaseTransport theta 0).toLinearMap := by
      rw [sourceUnitVector_span, hW, scalarPhaseTransport_transports]
    rw [Submodule.map_span, Submodule.map_span, Set.image_singleton,
      Set.image_singleton] at hmap
    change Submodule.span ℂ {W sourceUnitVector} =
      Submodule.span ℂ {(scalarPhaseTransport theta 0) sourceUnitVector} at hmap
    have hmem : W sourceUnitVector ∈
        Submodule.span ℂ {(scalarPhaseTransport theta 0) sourceUnitVector} := by
      rw [← hmap]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hnorm := congrArg norm hc
    rw [norm_smul, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
      sourceUnitVector_norm, mul_one] at hnorm
    rw [← hc, inner_smul_right, norm_mul, hnorm, one_mul,
      sourceUnitVector_inner_rotation, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-- Every admissible planar unitary has cost at least the scalar minimum. -/
theorem phaseMinimum_le_schatten_of_transports_model_lines
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2))
    (W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane)
    (hW : ComplexTraceOptimality.sourceLine.map W.toLinearMap =
      ComplexTraceOptimality.targetLine theta) :
    phaseMinimum p.toReal theta ^ (1 / p.toReal) ≤
      UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
        (LinearMap.id - W.toLinearMap) := by
  obtain ⟨x, _, hx, hinner⟩ := sourceLine_exists_angle_witness theta hθ
  exact phaseMinimum_le_schatten_planar finrank_euclideanSpace_fin p hp W theta hθ
    x hx (hinner W hW)

/-- A scalar phase attains the unrestricted Schatten minimum among all
complex planar unitaries transporting the same two lines. -/
theorem exists_global_planar_schatten_minimizer
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (theta : ℝ) (hθ : theta ∈ Icc 0 (Real.pi / 2)) :
    ∃ delta ∈ Icc 0 theta,
      ComplexTraceOptimality.sourceLine.map (scalarPhaseTransport theta delta).toLinearMap =
          ComplexTraceOptimality.targetLine theta ∧
      UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) =
            phaseMinimum p.toReal theta ^ (1 / p.toReal) ∧
      ∀ W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
        ComplexTraceOptimality.sourceLine.map W.toLinearMap =
            ComplexTraceOptimality.targetLine theta →
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - (scalarPhaseTransport theta delta).toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
            (LinearMap.id - W.toLinearMap) := by
  obtain ⟨delta, hδ, htrans, hcost, _⟩ := exists_scalarPhaseTransport_minimizer p hp theta hθ
  refine ⟨delta, hδ, htrans, hcost, ?_⟩
  intro W hW
  rw [hcost]
  exact phaseMinimum_le_schatten_of_transports_model_lines p hp theta hθ W hW

/-- The explicit critical angle is necessary and sufficient for the
canonical transport to minimize the full planar Schatten problem. -/
theorem canonical_planar_transport_isMin_iff_le_criticalAngle
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (theta : ℝ) (h0 : 0 < theta) (hπ : theta < Real.pi / 2) :
    (∀ W : ComplexPlane ≃ₗᵢ[ℂ] ComplexPlane,
      ComplexTraceOptimality.sourceLine.map W.toLinearMap =
          ComplexTraceOptimality.targetLine theta →
      UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - (scalarPhaseTransport theta 0).toLinearMap) ≤
        UnitarilyInvariantSeminorm.schatten ℂ ComplexPlane ComplexPlane p
          (LinearMap.id - W.toLinearMap)) ↔ theta ≤ criticalAngle p.toReal := by
  have hθ : theta ∈ Icc 0 (Real.pi / 2) := ⟨h0.le, hπ.le⟩
  rw [← critical_inequality_iff p.toReal theta hp1 hp2
      ⟨h0.le, by linarith [Real.pi_pos]⟩,
    ← canonical_phase_isMinOn_iff p.toReal theta hp1 hp2 h0 hπ]
  constructor
  · intro hmin delta hδ
    have h := hmin (scalarPhaseTransport theta delta)
      (scalarPhaseTransport_transports theta delta)
    rw [scalarPhaseTransport_schatten p hp theta 0 le_rfl h0.le hπ.le,
      scalarPhaseTransport_schatten p hp theta delta hδ.1 hδ.2 hπ.le] at h
    have hnonneg (eta : ℝ) (hη : eta ∈ Icc 0 theta) : 0 ≤ phasePower p.toReal theta eta :=
      (phaseMinimum_nonneg p.toReal theta hp1.le hθ).trans
        (phaseMinimum_le_phasePower p.toReal theta hp1.le h0.le hη)
    exact (Real.rpow_le_rpow_iff (hnonneg 0 ⟨le_rfl, h0.le⟩) (hnonneg delta hδ)
      (one_div_pos.2 (by linarith : 0 < p.toReal))).1 h
  · intro hmin W hW
    have heq := phaseMinimum_eq_of_isMinOn p.toReal theta 0 ⟨le_rfl, h0.le⟩ hmin
    rw [scalarPhaseTransport_schatten p hp theta 0 le_rfl h0.le hπ.le, ← heq]
    exact phaseMinimum_le_schatten_of_transports_model_lines p hp theta hθ W hW

end
end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
