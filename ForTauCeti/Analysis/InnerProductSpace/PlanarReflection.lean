/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis

/-!
# Source-preserving normal coordinates for a planar reflection

A complex self-adjoint planar unitary other than the two scalar
involutions is a real reflection after a diagonal unitary change of
coordinates. The change fixes the first coordinate projection, so it
can be used in constrained transport variations. These are classical
two-projection normal forms, with the scalar cases kept explicit.
-/

public section

noncomputable section

namespace ContinuousLinearMap

/-- Endomorphisms of a space of dimension at most one commute.
The cyclic-generator proof also includes the zero-dimensional space. -/
theorem commute_of_finrank_le_one
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (A B : E →L[𝕜] E) (hE : Module.finrank 𝕜 E ≤ 1) :
    Commute A B := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hE
  obtain ⟨a, ha⟩ := hv (A v)
  obtain ⟨b, hb⟩ := hv (B v)
  ext x
  obtain ⟨c, rfl⟩ := hv x
  change A (B (c • v)) = B (A (c • v))
  simp only [map_smul, ← ha, ← hb]
  module

end ContinuousLinearMap

namespace TauCeti.PlanarReflection

open scoped Matrix ComplexConjugate

private theorem trace_eq_zero_of_nonscalar
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitary _)
    (hself : IsSelfAdjoint M) (hpos : M ≠ 1) (hneg : M ≠ -1) : M.trace = 0 := by
  have hsq : M * M = 1 := by
    simpa only [hself.star_eq] using Unitary.star_mul_self_of_mem hM
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hsq
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hsq
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) hsq
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hsq
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
    Fin.isValue, Fin.reduceEq, ite_true, ite_false] at h00 h01 h10 h11
  simp only [Matrix.trace, Fin.sum_univ_two]
  by_contra htr
  have hb : M 0 1 = 0 := (mul_eq_zero.mp (show M 0 1 * (M 0 0 + M 1 1) = 0 by
    linear_combination h01)).resolve_right htr
  have hc : M 1 0 = 0 := (mul_eq_zero.mp (show M 1 0 * (M 0 0 + M 1 1) = 0 by
    linear_combination h10)).resolve_right htr
  have had : M 0 0 = M 1 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp (show (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 by
      linear_combination h00 - h11)).resolve_right htr)
  have ha : M 0 0 = 1 ∨ M 0 0 = -1 := by
    apply sq_eq_one_iff.mp
    simpa only [hb, zero_mul, add_zero, ← sq] using h00
  rcases ha with ha | ha
  · apply hpos
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, ha]
  · apply hneg
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, ha]

private theorem exists_unitary_polar (z : ℂ) :
    ∃ u : unitary ℂ, z = (‖z‖ : ℂ) * (u : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simp [hz]⟩
  let u : ℂ := z / (‖z‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hz)]
  have hs : star u * u = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hu]
    norm_num
  refine ⟨⟨u, Unitary.mem_iff.mpr ⟨hs, by rwa [mul_comm]⟩⟩, ?_⟩
  dsimp only [u]
  exact (mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))).symm

/-- A nonscalar self-adjoint unitary matrix has real reflecting
coordinates after a diagonal unitary conjugation. The change commutes
with the source coordinate projection, even when the off-diagonal
coefficient vanishes. -/
theorem exists_diagonal_conjugate_real_reflection
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitary _)
    (hself : IsSelfAdjoint M) (hpos : M ≠ 1) (hneg : M ≠ -1) :
    ∃ (d k : ℝ) (D : unitary (Matrix (Fin 2) (Fin 2) ℂ)),
      d ^ 2 + k ^ 2 = 1 ∧ 0 ≤ k ∧
      Commute (D : Matrix (Fin 2) (Fin 2) ℂ) (Matrix.diagonal ![1, 0]) ∧
      M = (D : Matrix (Fin 2) (Fin 2) ℂ) *
        !![-(d : ℂ), -(k : ℂ); -(k : ℂ), (d : ℂ)] * star (D : Matrix (Fin 2) (Fin 2) ℂ) := by
  have htrace := trace_eq_zero_of_nonscalar M hM hself hpos hneg
  have hdiag : conj (M 0 0) = M 0 0 := by
    simpa only [Matrix.star_apply, Complex.star_def] using congrArg
      (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hself.star_eq
  have ha : ((M 0 0).re : ℂ) = M 0 0 := RCLike.conj_eq_iff_re.mp hdiag
  have hc : conj (M 1 0) = M 0 1 := by
    simpa only [Matrix.star_apply, Complex.star_def] using congrArg
      (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hself.star_eq
  have hb : M 1 1 = -M 0 0 := by
    simp only [Matrix.trace, Fin.sum_univ_two] at htrace
    change M 0 0 + M 1 1 = 0 at htrace
    linear_combination htrace
  let d := -(M 0 0).re
  let k := ‖M 1 0‖
  obtain ⟨u, hu⟩ := exists_unitary_polar (-(M 1 0))
  have hku : -(k : ℂ) * (u : ℂ) = M 1 0 := by
    simpa only [norm_neg, neg_mul, neg_neg] using congrArg Neg.neg hu.symm
  let Dm : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, (u : ℂ)]
  have hD : Dm ∈ unitary _ := by
    apply Matrix.diagonal_mem_unitary.mpr
    refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · ext i
      change star (![1, (u : ℂ)] i) * ![1, (u : ℂ)] i = 1
      fin_cases i
      · simp
      · exact Unitary.star_mul_self_of_mem u.property
    · ext i
      change ![1, (u : ℂ)] i * star (![1, (u : ℂ)] i) = 1
      fin_cases i
      · simp
      · exact Unitary.mul_star_self_of_mem u.property
  have hsq : M * M = 1 := by
    simpa only [hself.star_eq] using Unitary.star_mul_self_of_mem hM
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hsq
  have hnorm : (M 0 0).re ^ 2 + ‖M 1 0‖ ^ 2 = 1 := by
    have hn : conj (M 1 0) * M 1 0 = (‖M 1 0‖ ^ 2 : ℝ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have him : (M 0 0).im = 0 := by
      simpa only [Complex.ofReal_im] using (congrArg Complex.im ha).symm
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h00
    rw [← hc, hn] at h00
    have heq := congrArg Complex.re h00
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.one_re, him, mul_zero, sub_zero] at heq
    nlinarith
  refine ⟨d, k, ⟨Dm, hD⟩, ?_, norm_nonneg _, ?_, ?_⟩
  · simpa only [d, k, neg_sq] using hnorm
  · exact Matrix.commute_diagonal _ _
  · have hkc : -(k : ℂ) * conj (u : ℂ) = M 0 1 := by
      have h := congrArg conj hku
      simpa only [map_mul, map_neg, Complex.conj_ofReal, hc] using h
    have hunit : (u : ℂ) * conj (u : ℂ) = 1 := by
      simpa only [Complex.star_def] using Unitary.mul_star_self_of_mem u.property
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Dm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, d, ha]
    · simpa [Dm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using hkc.symm
    · simpa [Dm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, mul_comm] using hku.symm
    · simp [Dm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, d, ha, hb]
      linear_combination -(M 0 0) * hunit

section ProjectionCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A nonconstant orthogonal projection on a complex plane has an
orthonormal basis with its range coordinate first. No rank hypothesis
is supplied: dimension two and exclusion of zero and identity suffice. -/
theorem exists_source_orthonormalBasis
    (P : E →L[ℂ] E) (hP : IsStarProjection P) (hE : Module.finrank ℂ E = 2)
    (hzero : P ≠ 0) (hone : P ≠ 1) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ E, P (b 0) = b 0 ∧ P (b 1) = 0 := by
  let hs := hP.isSelfAdjoint.isSymmetric
  let b := hs.eigenvectorBasis hE
  let mu := hs.eigenvalues hE
  have he (i : Fin 2) : P (b i) = (mu i : ℂ) • b i := hs.apply_eigenvectorBasis hE i
  have hcases (i : Fin 2) : mu i = 0 ∨ mu i = 1 := by
    have hidem : IsIdempotentElem (mu i : ℂ) := by
      apply smul_left_injective ℂ (b.orthonormal.ne_zero i)
      have h := congrArg (fun A : E →L[ℂ] E => A (b i)) hP.isIdempotentElem.eq
      change P (P (b i)) = P (b i) at h
      rwa [he, map_smul, he, smul_smul] at h
    exact_mod_cast IsIdempotentElem.iff_eq_zero_or_one.mp hidem
  rcases hcases 0 with h0 | h0 <;> rcases hcases 1 with h1 | h1
  · exfalso
    have hz (i : Fin 2) : mu i = 0 := by
      fin_cases i
      · exact h0
      · exact h1
    apply hzero
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    change P (b i) = 0
    simpa only [hz i, Complex.ofReal_zero, zero_smul] using he i
  · have horder : mu 1 ≤ mu 0 := hs.eigenvalues_antitone hE (by decide : (0 : Fin 2) ≤ 1)
    norm_num [h0, h1] at horder
  · exact ⟨b, by simpa only [h0, Complex.ofReal_one, one_smul] using he 0,
      by simpa only [h1, Complex.ofReal_zero, zero_smul] using he 1⟩
  · exfalso
    have ho (i : Fin 2) : mu i = 1 := by
      fin_cases i
      · exact h0
      · exact h1
    apply hone
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    change P (b i) = b i
    simpa only [ho i, Complex.ofReal_one, one_smul] using he i

omit [FiniteDimensional ℂ E] in
private theorem conj_toEuclideanCLM_repr_symm
    (b : OrthonormalBasis (Fin 2) ℂ E) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (b.repr.symm.conjStarAlgEquiv (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M)).toLinearMap =
      Matrix.toLin b.toBasis b.toBasis M := by
  ext x
  apply b.repr.injective
  apply WithLp.ofLp_injective 2
  change (b.repr (b.repr.symm
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M (b.repr x)))).ofLp = _
  rw [b.repr.apply_symm_apply, Matrix.ofLp_toEuclideanCLM]
  ext i
  have h := congrArg (fun v : Fin 2 → ℂ => v i) (Matrix.repr_toLin b.toBasis b.toBasis M x)
  have hrepr : ⇑(b.toBasis.repr x) = (b.repr x).ofLp := by
    ext j
    exact b.coe_toBasis_repr_apply x j
  rw [hrepr] at h
  simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using h.symm

/-- Every nonscalar self-adjoint unitary on a complex plane has real
reflection coordinates adapted to any nonconstant source projection.
The coordinate isometry is constructed from the actual two operators. -/
theorem exists_source_reflection_coordinates
    (P R : E →L[ℂ] E) (hP : IsStarProjection P)
    (hR : R ∈ unitary (E →L[ℂ] E)) (hself : IsSelfAdjoint R)
    (hE : Module.finrank ℂ E = 2) (hzero : P ≠ 0) (hone : P ≠ 1)
    (hpos : R ≠ 1) (hneg : R ≠ -1) :
    ∃ (e : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] E) (d k : ℝ),
      d ^ 2 + k ^ 2 = 1 ∧ 0 ≤ k ∧
      e.conjStarAlgEquiv (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        (Matrix.diagonal ![1, 0])) = P ∧
      e.conjStarAlgEquiv (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        !![-(d : ℂ), -(k : ℂ); -(k : ℂ), (d : ℂ)]) = R := by
  obtain ⟨b, hb0, hb1⟩ := exists_source_orthonormalBasis P hP hE hzero hone
  let f := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  let e₀ := b.repr.symm
  let g := f.trans e₀.conjStarAlgEquiv
  have hPcoord : g (Matrix.diagonal ![1, 0]) = P := by
    apply ContinuousLinearMap.coe_injective
    change (b.repr.symm.conjStarAlgEquiv (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      (Matrix.diagonal ![1, 0]))).toLinearMap = P.toLinearMap
    rw [conj_toEuclideanCLM_repr_symm]
    apply b.toBasis.ext
    intro i
    rw [Matrix.toLin_self]
    fin_cases i
    · convert hb0.symm using 1 <;> norm_num [Fin.sum_univ_two]
    · convert hb1.symm using 1 <;> norm_num [Fin.sum_univ_two]
  let M := g.symm R
  have hM : M ∈ unitary _ := Unitary.map_mem g.symm hR
  have hMself : IsSelfAdjoint M := by
    change star (g.symm R) = g.symm R
    rw [← map_star, hself.star_eq]
  have hMpos : M ≠ 1 := by
    intro h
    apply hpos
    calc
      R = g M := (g.apply_symm_apply R).symm
      _ = 1 := by rw [h, map_one]
  have hMneg : M ≠ -1 := by
    intro h
    apply hneg
    calc
      R = g M := (g.apply_symm_apply R).symm
      _ = -1 := by rw [h, map_neg, map_one]
  obtain ⟨d, k, D, hdk, hk, hcomm, hform⟩ :=
    exists_diagonal_conjugate_real_reflection M hM hMself hMpos hMneg
  let U : unitary (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
    ⟨f D, Unitary.map_mem f D.property⟩
  let u := Unitary.linearIsometryEquiv U
  let e := u.trans e₀
  have hconj (B : Matrix (Fin 2) (Fin 2) ℂ) :
      u.conjStarAlgEquiv (f B) = f ((D : Matrix (Fin 2) (Fin 2) ℂ) * B *
        star (D : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv, Unitary.conjStarAlgAut_apply]
    change f D * f B * star (f D) = _
    rw [← map_star, ← map_mul, ← map_mul]
  have hsource : (D : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![1, 0] *
      star (D : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![1, 0] := by
    rw [hcomm.eq, mul_assoc, Unitary.mul_star_self_of_mem D.property, mul_one]
  refine ⟨e, d, k, hdk, hk, ?_, ?_⟩
  · change e₀.conjStarAlgEquiv (u.conjStarAlgEquiv (f (Matrix.diagonal ![1, 0]))) = P
    rw [hconj, hsource]
    exact hPcoord
  · change e₀.conjStarAlgEquiv (u.conjStarAlgEquiv
      (f !![-(d : ℂ), -(k : ℂ); -(k : ℂ), (d : ℂ)])) = R
    rw [hconj, ← hform]
    exact g.apply_symm_apply R

end ProjectionCoordinates

end TauCeti.PlanarReflection
