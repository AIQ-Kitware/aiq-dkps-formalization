/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.RealSpectralSignObstruction
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Compatible real spectral sign projections

An orthogonal complex structure exchanges the two halves of a reflection.
A compatible sign projection exists precisely when either half admits an
orthogonal complex structure. Equivalently the full real dimension is
divisible by four. The construction uses the classical even-dimensional
orthogonal-complex-structure criterion from `AlmostComplexStructure`; the
projection formulation here is a local derivation, with no historical-first
claim. Its nuclear-transport application and the source comparisons are in
`dev/spectral-transport-unification.md` (provenance rows T1 and T8).
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The positive projection of a self-adjoint involution, retaining an
explicit complementary reflection symmetry. -/
theorem half_one_add_projection_of_odd_involution_real
    (A J : E →L[ℝ] E) (hA : IsSelfAdjoint A) (hsq : A * A = 1)
    (hodd : A * J + J * A = 0) :
    IsStarProjection ((1 / 2 : ℝ) • (1 + A)) ∧
      ((1 / 2 : ℝ) • (1 + A)) * J + J * ((1 / 2 : ℝ) • (1 + A)) = J := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change ((1 / 2 : ℝ) • (1 + A)) * ((1 / 2 : ℝ) • (1 + A)) =
      (1 / 2 : ℝ) • (1 + A)
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hsq]
    module
  · change star ((1 / 2 : ℝ) • (1 + A)) = (1 / 2 : ℝ) • (1 + A)
    simp only [star_smul, star_trivial, star_add, star_one, hA.star_eq]
  · simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
    linear_combination (norm := module) (1 / 2 : ℝ) • hodd

private theorem exists_sign_projection_of_even_range_real
    (K P : E →L[ℝ] E) (hKs : star K = -K) (hKsq : K * K = -1)
    (hP : IsStarProjection P) (hPK : P * K + K * P = K)
    (heven : Even (Module.finrank ℝ P.range)) :
    ∃ Q : E →L[ℝ] E, IsStarProjection Q ∧ Commute Q K ∧
      Q * ((2 : ℝ) • P - 1) + ((2 : ℝ) • P - 1) * Q = (2 : ℝ) • P - 1 := by
  let M := P.range
  obtain ⟨U, hU, hUs⟩ :=
    AlmostComplexStructure.exists_skew_unitary_iff_even_finrank_real.mpr heven
  have hUsq : U * U = -1 := by
    have h := Unitary.star_mul_self_of_mem hU
    rw [hUs, neg_mul] at h
    exact neg_eq_iff_eq_neg.mp h
  have hPr : M.starProjection = P :=
    (isStarProjection_iff_eq_starProjection_range.mp hP).choose_spec.symm
  let H : E →L[ℝ] E := M.subtypeL ∘L U ∘L M.orthogonalProjectionOnto
  have hHs : star H = -H := by
    change H.adjoint = -H
    dsimp only [H]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      M.adjoint_subtypeL, M.adjoint_orthogonalProjectionOnto]
    change M.subtypeL ∘L ((star U) ∘L M.orthogonalProjectionOnto) = _
    rw [hUs]
    simp only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg]
  have hPH : P * H = H := by
    ext x
    change P (U (M.orthogonalProjectionOnto x) : M) = _
    calc
      _ = M.starProjection (U (M.orthogonalProjectionOnto x) : M) :=
        congrArg (fun T : E →L[ℝ] E => T (U (M.orthogonalProjectionOnto x) : M)) hPr.symm
      _ = _ := M.starProjection_eq_self_iff.mpr (U (M.orthogonalProjectionOnto x)).property
  have hHP : H * P = H := by
    have h := congrArg star hPH
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hHs, neg_mul, neg_inj] using h
  have hHsq : H * H = -P := by
    ext x
    change (U (M.orthogonalProjectionOnto (U (M.orthogonalProjectionOnto x) : M)) : M) =
      -(P x)
    rw [M.orthogonalProjectionOnto_mem_subspace_eq_self]
    have h := congrArg (fun A : M →L[ℝ] M => (A (M.orthogonalProjectionOnto x) : E)) hUsq
    simpa only [mul_apply_eq_comp, neg_apply,
      one_apply_eq_self, Submodule.coe_neg, M.coe_orthogonalProjectionOnto_apply,
      hPr] using h
  have hPKP : P * K * P = 0 := by
    have h := congrArg (fun A : E →L[ℝ] E => A * P) hPK
    simp only [add_mul, mul_assoc, hP.isIdempotentElem.eq] at h
    exact add_right_cancel (h.trans (zero_add (K * P)).symm)
  have hHKH : H * K * H = 0 := by
    calc
      _ = (H * P) * K * (P * H) := by rw [hHP, hPH]
      _ = H * (P * K * P) * H := by noncomm_ring
      _ = 0 := by rw [hPKP]; simp
  have hKPK : K * P * K = P - 1 := by
    have h := congrArg (fun A : E →L[ℝ] E => K * A) hPK
    simp only [mul_add, ← mul_assoc, hKsq, neg_mul, one_mul] at h
    linear_combination (norm := noncomm_ring) h
  let A := K * H + H * K
  have hAs : star A = A := by simp only [A, star_add, star_mul, hHs, hKs, neg_mul_neg]; abel
  have hAsq : A * A = 1 := by
    calc
      _ = K * (H * K * H) + K * (H * H) * K + H * (K * K) * H +
          (H * K * H) * K := by dsimp only [A]; noncomm_ring
      _ = 1 := by rw [hHKH, hHsq, hKsq]; simp only [mul_zero, zero_mul, zero_add,
        add_zero, mul_neg, neg_mul, mul_one, hKPK, hHsq]; abel
  have hAK : A * K = K * A := by
    dsimp only [A]
    linear_combination (norm := noncomm_ring) H * hKsq - hKsq * H
  have hAP : A * P + P * A = A := by
    dsimp only [A]
    linear_combination (norm := noncomm_ring) K * hHP + hPK * H +
      H * hPK + hPH * K - hHP * K - K * hPH
  let Q := (1 / 2 : ℝ) • (1 + A)
  refine ⟨Q, ⟨?_, ?_⟩, ?_, ?_⟩
  · change Q * Q = Q
    dsimp only [Q]
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      one_mul, mul_one, hAsq]
    module
  · change star Q = Q
    simp only [Q, star_smul, star_trivial, star_add, star_one, hAs]
  · change Q * K = K * Q
    simp only [Q, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hAK]
  · dsimp only [Q]
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub,
      one_mul, mul_one, smul_smul]
    linear_combination (norm := module) hAP

/-- A real negative-square block with a compatible orthogonal reflection
admits a commuting, complement-exchanged orthogonal projection exactly
when its full real dimension is divisible by four. -/
theorem exists_spectral_sign_projection_iff_four_dvd_finrank_real
    (G J : E →L[ℝ] E) (c : ℝ) (hc : c ≠ 0)
    (hGs : star G = -G) (hG : G * G = -(c * c) • 1)
    (hJs : IsSelfAdjoint J) (hJ : J * J = 1)
    (hJG : J * G + G * J = 0) :
    (∃ P : E →L[ℝ] E, IsStarProjection P ∧ Commute P G ∧ P * J + J * P = J) ↔
      4 ∣ Module.finrank ℝ E := by
  constructor
  · rintro ⟨P, hP, hPG, hex⟩
    exact four_dvd_finrank_of_spectral_sign_projection_real G J P c hc hG hJ hP hPG hex
  · intro hdim
    let K := c⁻¹ • G
    have hKs : star K = -K := by simp only [K, star_smul, star_trivial, hGs, smul_neg]
    have hKsq : K * K = -1 := by
      simp only [K, smul_mul_assoc, mul_smul_comm, hG, smul_smul]
      have hcoeff : c⁻¹ * (c⁻¹ * -(c * c)) = -1 := by field_simp
      rw [hcoeff, neg_one_smul]
    have hJK : J * K + K * J = 0 := by
      simp only [K, mul_smul_comm, smul_mul_assoc, ← smul_add, hJG, smul_zero]
    let P := (1 / 2 : ℝ) • (1 + J)
    have hP : IsStarProjection P := by
      constructor
      · change P * P = P
        simp only [P, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
          one_mul, mul_one, hJ]
        module
      · change star P = P
        simp only [P, star_smul, star_trivial, star_add, star_one, hJs.star_eq]
    have hPK : P * K + K * P = K := by
      simp only [P, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
      linear_combination (norm := module) (1 / 2 : ℝ) • hJK
    have hBsq : (K * J) * (K * J) = 1 := by
      linear_combination (norm := noncomm_ring) K * hJK * J - hKsq * (J * J) + hJ
    have hPB : P * (K * J) + (K * J) * P = K * J := by
      simp only [P, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
      have h := congrArg (fun A : E →L[ℝ] E => A * J) hJK
      simp only [add_mul, mul_assoc, zero_mul] at h
      simp only [mul_assoc]
      linear_combination (norm := module) (1 / 2 : ℝ) • h
    have heq := finrank_range_eq_ker_of_projection_exchange_real P (K * J)
      hP.isIdempotentElem hBsq hPB
    have hdimP := LinearMap.finrank_range_add_finrank_ker P.toLinearMap
    have heven : Even (Module.finrank ℝ P.range) := by
      obtain ⟨m, hm⟩ := hdim
      exact ⟨m, by omega⟩
    obtain ⟨Q, hQ, hQK, hQJ⟩ :=
      exists_sign_projection_of_even_range_real K P hKs hKsq hP hPK heven
    have hJform : (2 : ℝ) • P - 1 = J := by dsimp only [P]; module
    refine ⟨Q, hQ, ?_, hJform ▸ hQJ⟩
    have hGform : G = c • K := by simp [K, smul_smul, hc]
    change Q * G = G * Q
    rw [hGform, mul_smul_comm, smul_mul_assoc, hQK.eq]

omit [CompleteSpace E] in
/-- A complex structure anticommuting with a reflection pairs its two
reflection eigenspaces. The full real dimension is twice the dimension
of its positive reflection eigenspace. -/
theorem finrank_eq_two_mul_positive_eigenspace_real
    (K J : E →L[ℝ] E) (hK : K * K = -1) (hJ : J * J = 1)
    (hJK : J * K + K * J = 0) :
    Module.finrank ℝ E = 2 * Module.finrank ℝ (Module.End.eigenspace J.toLinearMap 1) := by
  let P := (1 / 2 : ℝ) • (1 + J)
  have hP : IsIdempotentElem P := by
    change P * P = P
    simp only [P, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hJ]
    module
  have hBsq : (K * J) * (K * J) = 1 := by
    linear_combination (norm := noncomm_ring) K * hJK * J - hK * (J * J) + hJ
  have hPB : P * (K * J) + (K * J) * P = K * J := by
    simp only [P, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one]
    have h := congrArg (fun A : E →L[ℝ] E => A * J) hJK
    simp only [add_mul, mul_assoc, zero_mul] at h
    simp only [mul_assoc]
    linear_combination (norm := module) (1 / 2 : ℝ) • h
  have heq := finrank_range_eq_ker_of_projection_exchange_real P (K * J) hP hBsq hPB
  have hdim := LinearMap.finrank_range_add_finrank_ker P.toLinearMap
  have hJP : J * P = P := by
    simp only [P, mul_smul_comm, mul_add, mul_one, hJ]
    module
  have hrange : P.range = Module.End.eigenspace J.toLinearMap 1 := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      apply Module.End.mem_eigenspace_iff.mpr
      change J (P y) = (1 : ℝ) • P y
      rw [one_smul]
      exact congrArg (fun A : E →L[ℝ] E => A y) hJP
    · intro hx
      have hx := Module.End.mem_eigenspace_iff.mp hx
      change J x = (1 : ℝ) • x at hx
      rw [one_smul] at hx
      refine ⟨x, ?_⟩
      change (1 / 2 : ℝ) • (x + J x) = x
      rw [hx]
      module
  rw [← hrange]
  omega

end TauCeti
