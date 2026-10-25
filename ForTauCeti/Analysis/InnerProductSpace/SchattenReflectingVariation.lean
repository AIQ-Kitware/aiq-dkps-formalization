/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenReflectingPhases
public import ForTauCeti.Analysis.InnerProductSpace.PlanarSchatten
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Actual planar reflecting-unitary variations

A real reflecting matrix is multiplied on the right by a diagonal
complex phase. The resulting unitary curve preserves the transported
source projection. Its exact Schatten displacement is computed from
trace and determinant, including the initially vanishing singular value.
-/

public section

noncomputable section

namespace TauCeti.ReflectingVariation

open scoped ENNReal Matrix ComplexConjugate Topology

abbrev Plane := EuclideanSpace ℂ (Fin 2)

private def phase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_neg_sub_phase (t : ℝ) :
    phase (-t) - phase t = -2 * Complex.I * (Real.sin t : ℂ) := by
  change Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I) = _
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

private theorem phase_mem_unitary (t : ℝ) : phase t ∈ unitary ℂ := by
  have hn : Complex.normSq (phase t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, show ‖phase t‖ = 1 from Complex.norm_exp_ofReal_mul_I t]
    norm_num
  have hs : star (phase t) * phase t = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hn, Complex.ofReal_one]
  exact Unitary.mem_iff.mpr ⟨hs, by rwa [mul_comm]⟩

/-- A real planar reflection, with `d²+k²=1` as its geometric hypothesis. -/
def reflectionMatrix (d k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(d : ℂ), -(k : ℂ); -(k : ℂ), (d : ℂ)]

/-- The diagonal phase commutes with the source coordinate projection. -/
def diagonalPhase (d t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![phase ((d + 1) * t / 2), phase ((d - 1) * t / 2)]

/-- The actual matrix curve through the reflecting transporter. -/
def variationMatrix (d k t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  reflectionMatrix d k * diagonalPhase d t

/-- Its action as a continuous operator on the complex Euclidean plane. -/
def variation (d k t : ℝ) : Plane →L[ℂ] Plane :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (variationMatrix d k t)

theorem reflectionMatrix_mem_unitary (d k : ℝ) (hdk : d ^ 2 + k ^ 2 = 1) :
    reflectionMatrix d k ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc : (d : ℂ) ^ 2 + (k : ℂ) ^ 2 = 1 := by exact_mod_cast hdk
  have hstar : star (reflectionMatrix d k) = reflectionMatrix d k := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [reflectionMatrix, Matrix.star_apply]
  have hsquare : reflectionMatrix d k * reflectionMatrix d k = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using hc
    · simp [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simpa [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two, add_comm] using hc
  exact Unitary.mem_iff.mpr ⟨by rw [hstar, hsquare], by rw [hstar, hsquare]⟩

theorem diagonalPhase_mem_unitary (d t : ℝ) :
    diagonalPhase d t ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  apply Matrix.diagonal_mem_unitary.mpr
  apply Unitary.mem_iff.mpr
  constructor
  · ext i
    change star (![phase ((d + 1) * t / 2), phase ((d - 1) * t / 2)] i) *
      ![phase ((d + 1) * t / 2), phase ((d - 1) * t / 2)] i = 1
    fin_cases i <;> exact Unitary.star_mul_self_of_mem (phase_mem_unitary _)
  · ext i
    change ![phase ((d + 1) * t / 2), phase ((d - 1) * t / 2)] i *
      star (![phase ((d + 1) * t / 2), phase ((d - 1) * t / 2)] i) = 1
    fin_cases i <;> exact Unitary.mul_star_self_of_mem (phase_mem_unitary _)

/-- The whole variation is unitary, for every real parameter. -/
theorem variation_mem_unitary (d k : ℝ) (hdk : d ^ 2 + k ^ 2 = 1) (t : ℝ) :
    variation d k t ∈ unitary (Plane →L[ℂ] Plane) :=
  Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (mul_mem (reflectionMatrix_mem_unitary d k hdk) (diagonalPhase_mem_unitary d t))

private theorem trace_variationMatrix (d k t : ℝ) (hd : |d| ≤ 1) :
    (variationMatrix d k t).trace =
      phase (reflectingSmallPhase d t) - phase (reflectingLargeOffset d t) := by
  let u := d * t / 2
  let v := t / 2
  let chi := Real.arcsin (d * Real.sin v)
  have hbound : |d * Real.sin v| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg d) (Real.abs_sin_le_one _)).trans hd
  have hsin : Real.sin chi = d * Real.sin v :=
    Real.sin_arcsin (neg_le_of_abs_le hbound) (le_of_abs_le hbound)
  have htrace : (variationMatrix d k t).trace =
      -(d : ℂ) * phase (u + v) + (d : ℂ) * phase (u + -v) := by
    have ha : (d + 1) * t / 2 = u + v := by dsimp only [u, v]; ring
    have hb : (d - 1) * t / 2 = u + -v := by dsimp only [u, v]; ring
    simp [variationMatrix, diagonalPhase, reflectionMatrix, Matrix.trace,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, ha, hb]
  rw [htrace, show reflectingSmallPhase d t = u + -chi by rfl,
    show reflectingLargeOffset d t = u + chi by rfl,
    phase_add, phase_add, phase_add, phase_add]
  calc
    _ = (d : ℂ) * phase u * (phase (-v) - phase v) := by ring
    _ = phase u * (phase (-chi) - phase chi) := by
      rw [phase_neg_sub_phase, phase_neg_sub_phase, hsin, Complex.ofReal_mul]
      ring
    _ = _ := by ring

private theorem det_variationMatrix (d k t : ℝ) (hdk : d ^ 2 + k ^ 2 = 1) :
    (variationMatrix d k t).det =
      phase (reflectingSmallPhase d t) * -phase (reflectingLargeOffset d t) := by
  have hc : (d : ℂ) ^ 2 + (k : ℂ) ^ 2 = 1 := by exact_mod_cast hdk
  have hdet : (reflectionMatrix d k).det = -1 := by
    simp only [Matrix.det_fin_two, reflectionMatrix, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -hc
  rw [variationMatrix, Matrix.det_mul, hdet, diagonalPhase, Matrix.det_diagonal,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← phase_add, mul_neg, ← phase_add, neg_one_mul]
  congr 1
  unfold reflectingSmallPhase reflectingLargeOffset
  congr 1
  ring

private theorem norm_one_sub_phase (t : ℝ) :
    ‖1 - phase t‖ = |2 * Real.sin (t / 2)| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [phase, Complex.exp_ofReal_mul_I, Complex.sub_re, Complex.one_re,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
    Complex.sub_im, Complex.one_im, Complex.add_im, Complex.mul_im, mul_one, zero_add]
  have hc : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (t / 2) using 1
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq (t / 2)]

private theorem norm_one_add_phase (t : ℝ) :
    ‖1 + phase t‖ = |2 * Real.cos (t / 2)| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [phase, Complex.exp_ofReal_mul_I, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
    Complex.add_im, Complex.one_im, Complex.mul_im, mul_one, zero_add]
  have hc : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (t / 2) using 1
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- The actual Schatten displacement of the matrix curve equals the
two-phase scalar cost, including at the reflecting initial point. -/
theorem schatten_displacement_variation (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (d k : ℝ) (hdk : d ^ 2 + k ^ 2 = 1) (t : ℝ) :
    UnitarilyInvariantSeminorm.schatten ℂ Plane Plane p
        (LinearMap.id - (variation d k t).toLinearMap) ^ p.toReal =
      reflectingPhasePower p.toReal d t := by
  let := isStarNormal_of_mem_unitary (variation_mem_unitary d k hdk t)
  have hd : |d| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg k], by nlinarith [sq_nonneg k]⟩
  have htrace : LinearMap.trace ℂ Plane (variation d k t).toLinearMap =
      phase (reflectingSmallPhase d t) + -phase (reflectingLargeOffset d t) := by
    rw [variation, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
    exact trace_variationMatrix d k t hd
  have hdet : LinearMap.det (variation d k t).toLinearMap =
      phase (reflectingSmallPhase d t) * -phase (reflectingLargeOffset d t) := by
    rw [variation, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
    exact det_variationMatrix d k t hdk
  rw [schatten_displacement_rpow_eq_of_trace_det_fin_two (variation d k t)
    (by simp) _ _ htrace hdet p hp, norm_one_sub_phase, sub_neg_eq_add, norm_one_add_phase]
  rfl

/-- The source projection onto the first coordinate line. -/
def sourceProjection : Plane →L[ℂ] Plane :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (Matrix.diagonal ![1, 0])

theorem sourceProjection_isStarProjection : IsStarProjection sourceProjection := by
  let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
  let f := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  have hsq : P * P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  have hstar : star P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.star_apply]
  change IsStarProjection (f P)
  refine ⟨?_, ?_⟩
  · change f P * f P = f P
    rw [← map_mul, hsq]
  · change star (f P) = f P
    rw [← map_star, hstar]

/-- Every matrix in the curve transports the same actual source projection
to its image under the initial reflection. -/
theorem variation_transports (d k : ℝ) (t : ℝ) :
    variation d k t * sourceProjection * star (variation d k t) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (reflectionMatrix d k) *
        sourceProjection *
        star (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (reflectionMatrix d k)) := by
  let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
  have hcomm : diagonalPhase d t * P = P * diagonalPhase d t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalPhase, P, Matrix.mul_apply, Fin.sum_univ_two]
  have hphase : diagonalPhase d t * P * star (diagonalPhase d t) = P := by
    rw [hcomm, mul_assoc, Unitary.mul_star_self_of_mem (diagonalPhase_mem_unitary d t), mul_one]
  have hmatrix : variationMatrix d k t * P * star (variationMatrix d k t) =
      reflectionMatrix d k * P * star (reflectionMatrix d k) := by
    rw [variationMatrix, star_mul]
    calc
      _ = reflectionMatrix d k * (diagonalPhase d t * P * star (diagonalPhase d t)) *
          star (reflectionMatrix d k) := by simp only [mul_assoc]
      _ = _ := by rw [hphase]
  let f := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  change f (variationMatrix d k t) * f P * star (f (variationMatrix d k t)) =
    f (reflectionMatrix d k) * f P * star (f (reflectionMatrix d k))
  simpa only [map_mul, map_star] using congrArg
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) hmatrix

theorem variation_zero (d k : ℝ) :
    variation d k 0 = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (reflectionMatrix d k) := by
  have hphase : diagonalPhase d 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalPhase, phase]
  simp only [variation, variationMatrix, hphase, mul_one]

theorem continuous_variation (d k : ℝ) : Continuous (variation d k) := by
  have hm : Continuous (variationMatrix d k) := by
    change Continuous (fun t : ℝ => reflectionMatrix d k * Matrix.diagonal
      ![Complex.exp ((((d + 1) * t / 2 : ℝ) : ℂ) * Complex.I),
        Complex.exp ((((d - 1) * t / 2 : ℝ) : ℂ) * Complex.I)])
    fun_prop
  have hf : Continuous (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) :=
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
  exact hf.comp hm

/-- A genuine planar reflecting transporter with `d!=0` fails local
minimality among all unitary transports of its source projection.
No differentiability of the objective at zero singular values is assumed. -/
theorem not_isLocalMinOn_reflecting_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (d k : ℝ) (hdk : d ^ 2 + k ^ 2 = 1) (hd0 : d ≠ 0) :
    ¬ IsLocalMinOn
      (fun T : Plane →L[ℂ] Plane => UnitarilyInvariantSeminorm.schatten ℂ Plane Plane p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (Plane →L[ℂ] Plane) ∧
        T * sourceProjection * star T =
          variation d k 0 * sourceProjection * star (variation d k 0)}
      (variation d k 0) := by
  intro hmin
  have hfeasible (t : ℝ) : variation d k t ∈
      {T | T ∈ unitary (Plane →L[ℂ] Plane) ∧
        T * sourceProjection * star T =
          variation d k 0 * sourceProjection * star (variation d k 0)} := by
    refine ⟨variation_mem_unitary d k hdk t, ?_⟩
    rw [variation_zero]
    exact variation_transports d k t
  have hcurve := hmin.comp_continuousOn (s := Set.univ)
    (fun t _ => hfeasible t) (continuous_variation d k).continuousOn (Set.mem_univ 0)
  rw [isLocalMinOn_univ_iff] at hcurve
  change ∀ᶠ t in 𝓝 (0 : ℝ), _ ≤ _ at hcurve
  have hcost0 : reflectingPhasePower p.toReal d 0 = (2 : ℝ) ^ p.toReal := by
    simp [reflectingPhasePower, reflectingSmallPhase, reflectingLargeOffset,
      Real.zero_rpow (by linarith : p.toReal ≠ 0)]
  simp only [Function.comp_apply,
    schatten_displacement_variation p hp d k hdk, hcost0] at hcurve
  obtain ⟨r, hr, hdescent⟩ := reflectingPhasePower_strict_descent p.toReal d hp1 hd0
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp hcurve
  let t := min r s / 2
  have htpos : 0 < t := half_pos (lt_min hr hs)
  have htr : |t| < r := by rw [abs_of_pos htpos]; dsimp only [t]; linarith [min_le_left r s]
  have hts : dist t 0 < s := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    dsimp only [t]
    linarith [min_le_right r s]
  exact (not_lt_of_ge (hball hts)) (hdescent t (by rwa [abs_of_pos htpos]) htr)

section NegativeIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

private def negativeScalar (t : ℝ) : E →L[ℂ] E := -phase t • (1 : E →L[ℂ] E)

omit [FiniteDimensional ℂ E] in
private theorem negativeScalar_mem_unitary (t : ℝ) :
    negativeScalar (E := E) t ∈ unitary (E →L[ℂ] E) := by
  have hs : -phase t ∈ unitary ℂ := by
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · rw [star_neg, neg_mul_neg]
      exact Unitary.star_mul_self_of_mem (phase_mem_unitary t)
    · rw [star_neg, neg_mul_neg]
      exact Unitary.mul_star_self_of_mem (phase_mem_unitary t)
  exact Unitary.smul_mem_of_mem hs (one_mem _)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem negativeScalar_zero : negativeScalar (E := E) 0 = -1 := by
  simp [negativeScalar, phase]

omit [FiniteDimensional ℂ E] in
private theorem negativeScalar_transports (P : E →L[ℂ] E) (t : ℝ) :
    negativeScalar t * P * star (negativeScalar t) = P := by
  have hcomm : negativeScalar (E := E) t * P = P * negativeScalar t := by
    simp only [negativeScalar, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [hcomm, mul_assoc, Unitary.mul_star_self_of_mem (negativeScalar_mem_unitary t), mul_one]

omit [CompleteSpace E] in
private theorem negativeScalar_cost (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (t : ℝ) :
    UnitarilyInvariantSeminorm.schatten ℂ E E p
      (LinearMap.id - (negativeScalar t).toLinearMap) ^ p.toReal =
        Module.finrank ℂ E * |2 * Real.cos (t / 2)| ^ p.toReal := by
  let e := stdOrthonormalBasis ℂ E
  have hdisp (i : Fin (Module.finrank ℂ E)) :
      ((LinearMap.id : E →ₗ[ℂ] E) - (negativeScalar (E := E) t).toLinearMap) (e i) =
        (1 + phase t) • e i := by
    change e i - (-phase t) • e i = _
    module
  rw [schatten_rpow_eq_sum_norm_eigenvalues e _ _ hdisp p hp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_one_add_phase]

/-- A negative identity block of positive dimension cannot be a local
minimum for any finite Schatten transport cost. The source operator is
arbitrary, since scalar phases commute with every source. -/
theorem not_isLocalMinOn_negative_identity [Nontrivial E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (P : E →L[ℂ] E) :
    ¬ IsLocalMinOn
      (fun T : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (E →L[ℂ] E) ∧ T * P * star T = P} (-1 : E →L[ℂ] E) := by
  intro hmin
  rw [← negativeScalar_zero] at hmin
  have hcont : Continuous (negativeScalar (E := E)) := by
    change Continuous (fun t : ℝ => -Complex.exp ((t : ℂ) * Complex.I) • (1 : E →L[ℂ] E))
    fun_prop
  have hcurve := hmin.comp_continuousOn (s := Set.univ)
    (fun t _ => ⟨negativeScalar_mem_unitary t, negativeScalar_transports P t⟩)
    hcont.continuousOn (Set.mem_univ 0)
  rw [isLocalMinOn_univ_iff] at hcurve
  change ∀ᶠ t in 𝓝 (0 : ℝ), _ ≤ _ at hcurve
  simp only [Function.comp_apply, negativeScalar_cost p hp, zero_div,
    Real.cos_zero, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hcurve
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hcurve
  let t := min r Real.pi / 2
  have ht : 0 < t := half_pos (lt_min hr Real.pi_pos)
  have htpi : t < Real.pi := by
    dsimp only [t]
    linarith [min_le_right r Real.pi, Real.pi_pos]
  have htr : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp only [t]
    linarith [min_le_left r Real.pi]
  have hcpos : 0 < Real.cos (t / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hclt : Real.cos (t / 2) < 1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0 : ℝ) ≤ 0 from le_rfl) (show t / 2 ≤ Real.pi by linarith [Real.pi_pos])
      (half_pos ht)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  have hpow : |2 * Real.cos (t / 2)| ^ p.toReal < (2 : ℝ) ^ p.toReal := by
    apply Real.rpow_lt_rpow (abs_nonneg _) _ hp0
    rw [abs_of_pos (mul_pos (by norm_num) hcpos)]
    linarith
  have hn : 0 < (Module.finrank ℂ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  exact (not_lt_of_ge (hball htr)) (mul_lt_mul_of_pos_left hpow hn)

end NegativeIdentity

end TauCeti.ReflectingVariation
