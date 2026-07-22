/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes
import DavisKahan.FiniteDimensional.Core.OperatorBlocks
import ForMathlib.Analysis.InnerProductSpace.CourantFischer
import ForMathlib.Analysis.InnerProductSpace.KyFan
import ForMathlib.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

/-!
# Fan dominance for the finite direct rotation

This file supplies the missing mathematics behind Davis--Kahan Section 4.
The argument has two distinct parts.

* For every scalar field `RCLike 𝕜`, the positive displacement square of the
  canonical direct rotation is weakly majorized by that of every unitary
  carrying `U` onto `V`.  The proof writes the canonical intertwiner as the
  competitor times a two-block pinching, applies the Fan--Hoffman inequality
  `lambda_i (Re A) <= sigma_i A`, and then uses pinching contraction.

The historical full-displacement short-rotation claim is not part of this
module.  As stated for arbitrary orthogonal competitors it is false even over
`ℝ`: with two equal principal angles, a multiplicity-space rotation combines
one zero rotation and one `2θ` rotation and has smaller trace displacement than
the plane-by-plane direct rotation.  The sound replacement is the unrestricted
pointwise and UI-norm minimality of the restricted displacement `(I-W)P_U`,
proved in `DirectRotation.PrincipalPlanes`.

No fictional principal-plane namespace is assumed.  All spectral data are
obtained from the modulus of the canonical intertwiner and ordinary
finite-dimensional Courant--Fischer theory.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Hermitian part `(A + A star) / 2`. -/
noncomputable def hermitianPart (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (((2 : ℝ)⁻¹ : ℝ) : 𝕜) • (A + A.adjoint)

/-- Positive displacement square `(I - W star)(I - W)`. -/
noncomputable def displacementSquare (W : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (LinearMap.id - W.adjoint) ∘ₗ (LinearMap.id - W)

@[simp] theorem hermitianPart_apply (A : E →ₗ[𝕜] E) (x : E) :
    hermitianPart A x = (((2 : ℝ)⁻¹ : ℝ) : 𝕜) • (A x + A.adjoint x) := by
  simp [hermitianPart]

theorem hermitianPart_isSymmetric (A : E →ₗ[𝕜] E) :
    (hermitianPart A).IsSymmetric := by
  intro x y
  simp only [hermitianPart_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, inner_add_left, inner_add_right,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  ring

theorem re_inner_hermitianPart (A : E →ₗ[𝕜] E) (x : E) :
    RCLike.re ⟪hermitianPart A x, x⟫_𝕜 = RCLike.re ⟪A x, x⟫_𝕜 := by
  have hconj : RCLike.re ⟪x, A x⟫_𝕜 = RCLike.re ⟪A x, x⟫_𝕜 := by
    rw [← inner_conj_symm (A x) x, RCLike.conj_re]
  rw [hermitianPart_apply, inner_smul_left, RCLike.conj_ofReal,
    inner_add_left, LinearMap.adjoint_inner_left, RCLike.re_ofReal_mul,
    map_add, hconj]
  ring

theorem displacementSquare_positive (W : E →ₗ[𝕜] E) :
    (displacementSquare W).IsPositive := by
  have h := LinearMap.isPositive_adjoint_comp_self (LinearMap.id - W)
  have he : LinearMap.adjoint (LinearMap.id - W) =
      LinearMap.id - W.adjoint := by
    rw [map_sub, LinearMap.adjoint_id]
  rwa [he] at h

theorem displacementSquare_apply_inner (W : E →ₗ[𝕜] E) (x : E) :
    RCLike.re ⟪displacementSquare W x, x⟫_𝕜 = ‖W x - x‖ ^ 2 := by
  have he : (LinearMap.id : E →ₗ[𝕜] E) - W.adjoint =
      LinearMap.adjoint (LinearMap.id - W) := by
    rw [map_sub, LinearMap.adjoint_id]
  -- `congr 2` peels past the norm and leaves the false `x - W x = W x - x`
  rw [displacementSquare, LinearMap.comp_apply, he,
    LinearMap.adjoint_inner_left, inner_self_eq_norm_sq,
    LinearMap.sub_apply, LinearMap.id_apply, norm_sub_rev]

theorem displacementSquare_unitary (W : E ≃ₗᵢ[𝕜] E) :
    displacementSquare W.toLinearMap =
      (2 : 𝕜) • (LinearMap.id - hermitianPart W.toLinearMap) := by
  ext x
  simp only [displacementSquare, hermitianPart, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, W.adjoint_toLinearMap_eq_symm,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
    LinearIsometryEquiv.symm_apply_apply]
  -- the two sides carry `2` and `(2 : ℝ)⁻¹` as unrelated scalar atoms
  match_scalars <;> push_cast <;> ring

/-- A unitary carrying `U` onto `V` intertwines their orthogonal projections. -/
theorem projection_intertwines_of_map_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    W.toLinearMap ∘ₗ projection U = projection V ∘ₗ W.toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [← U.starProjection_add_starProjection_orthogonal x]
  have hU : W (U.starProjection x) ∈ V := by
    rw [← hmap]
    exact ⟨U.starProjection x, U.starProjection_apply_mem x, rfl⟩
  have hperp : W (Uᗮ.starProjection x) ∈ Vᗮ := by
    intro v hv
    rw [← hmap] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← W.inner_map_map]
    exact Submodule.inner_right_of_mem_orthogonal hu
      (Uᗮ.starProjection_apply_mem x)
  simp only [LinearMap.comp_apply, map_add]
  rw [projection_apply_of_mem hU, projection_apply_of_mem_orthogonal hperp,
    add_zero, projection_apply_of_mem (U.starProjection_apply_mem x),
    projection_apply_of_mem_orthogonal (Uᗮ.starProjection_apply_mem x),
    map_zero, add_zero]

/-- The adjoint intertwining relation. -/
theorem adjoint_projection_intertwines_of_map_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    W.symm.toLinearMap ∘ₗ projection V = projection U ∘ₗ W.symm.toLinearMap := by
  have h := congrArg LinearMap.adjoint
    (projection_intertwines_of_map_eq U V W hmap)
  simpa [LinearMap.adjoint_comp, projection_adjoint,
    W.adjoint_toLinearMap_eq_symm] using h

/-- Multiplying the canonical intertwiner by a competing unitary on the left
produces the diagonal pinching of the competitor's adjoint. -/
theorem symm_comp_canonicalIntertwiner_eq_pinch
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    W.symm.toLinearMap ∘ₗ canonicalIntertwiner U V =
      pinch U W.symm.toLinearMap := by
  have hstar := adjoint_projection_intertwines_of_map_eq U V W hmap
  have hstarPerp := adjoint_projection_intertwines_of_map_eq Uᗮ Vᗮ W (by
    rw [Submodule.map_orthogonal W.toLinearEquiv, hmap])
  ext x
  simp only [canonicalIntertwiner, pinch, LinearMap.comp_apply,
    LinearMap.add_apply, map_add]
  rw [show W.symm (projection V (projection U x)) =
      projection U (W.symm (projection U x)) by
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun hstar (projection U x)]
  rw [show W.symm (complementaryProjection V (complementaryProjection U x)) =
      complementaryProjection U (W.symm (complementaryProjection U x)) by
        simpa [complementaryProjection, LinearMap.comp_apply] using
          LinearMap.congr_fun hstarPerp (complementaryProjection U x)]

/-- The modulus of the pinched competitor is the modulus of the canonical
intertwiner. -/
theorem abs_pinch_competitor_eq_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    ForMathlib.abs (pinch U W.symm.toLinearMap) =
      ForMathlib.abs (canonicalIntertwiner U V) := by
  have hfactor := symm_comp_canonicalIntertwiner_eq_pinch U V W hmap
  have hgram :
      (pinch U W.symm.toLinearMap).adjoint ∘ₗ pinch U W.symm.toLinearMap =
        (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V := by
    rw [← hfactor, LinearMap.adjoint_comp, W.symm.adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.symm_symm]
    ext x
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.coe_coe, LinearIsometryEquiv.symm_apply_apply]
  exact LinearMap.IsPositive.sqrt_eq_sqrt_of_eq
    (LinearMap.isPositive_adjoint_comp_self (pinch U W.symm.toLinearMap))
    (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V)) hgram

/-- Fan--Hoffman pointwise inequality: every sorted eigenvalue of the Hermitian
part is bounded by the corresponding singular value. -/
theorem eigenvalues_hermitianPart_le_singularValues
    (A : E →ₗ[𝕜] E) (i : Fin (finrank 𝕜 E)) :
    (hermitianPart_isSymmetric A).eigenvalues rfl i ≤
      A.singularValues (i : ℕ) := by
  classical
  let H := hermitianPart A
  let C := ForMathlib.abs A
  let b := (isPositive_abs A).isSymmetric.eigenvectorBasis rfl
  let tail := specSubspace b (fun j : Fin (finrank 𝕜 E) => i ≤ j)
  obtain ⟨L, hLdim, hLlow⟩ :=
    forall_unit_vector_eigenvalue_le_re_inner
      (hermitianPart_isSymmetric A) rfl i
  have htaildim : finrank 𝕜 tail = finrank 𝕜 E - (i : ℕ) := by
    dsimp [tail]
    rw [finrank_specSubspace]
    simpa using Fin.card_Ici i
  have hinter : L ⊓ tail ≠ ⊥ := by
    intro hbot
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq L tail
    rw [hbot, finrank_bot, add_zero, hLdim, htaildim] at hdim
    have hle : finrank 𝕜 (L ⊔ tail : Submodule 𝕜 E) ≤ finrank 𝕜 E :=
      Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinter
  let x := (((‖z‖⁻¹ : ℝ) : 𝕜) • z)
  have hxL : x ∈ L := L.smul_mem _ hz.1
  have hxtail : x ∈ tail := tail.smul_mem _ hz.2
  have hxnorm : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  have hCbound : ‖C x‖ ≤ A.singularValues (i : ℕ) := by
    have hdiag := re_inner_map_self_le_of_mem_specSubspace
      (isPositive_abs A).isSymmetric rfl
      (fun j hj => by
        rw [congrFun (eigenvalues_abs A) j]
        exact A.singularValues_antitone hj)
      hxtail
    have hCpos := (isPositive_abs A).nonneg_inner x
    have hCnorm : ‖C x‖ ^ 2 =
        RCLike.re ⟪(C ∘ₗ C) x, x⟫_𝕜 := by
      rw [LinearMap.comp_apply, (isPositive_abs A).isSymmetric,
        inner_self_eq_norm_sq]
    have hCcontract : ‖C x‖ ≤ A.singularValues (i : ℕ) * ‖x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
        (A.singularValues_nonneg _) (norm_nonneg _))).mp
      rw [sq_mul, hCnorm]
      have hdiag2 := re_inner_map_self_le_of_mem_specSubspace
        ((isPositive_abs A).mul_self_isSymmetric) rfl
        (fun j hj => by
          rw [(isPositive_abs A).mul_self_eigenvalues rfl,
            congrFun (eigenvalues_abs A) j]
          exact pow_le_pow_left₀ (A.singularValues_nonneg _)
            (A.singularValues_antitone hj) 2)
        hxtail
      exact hdiag2
    simpa [hxnorm] using hCcontract
  calc
    (hermitianPart_isSymmetric A).eigenvalues rfl i
        ≤ RCLike.re ⟪H x, x⟫_𝕜 := hLlow x hxL hxnorm
    _ = RCLike.re ⟪A x, x⟫_𝕜 := re_inner_hermitianPart A x
    _ ≤ ‖A x‖ * ‖x‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ = ‖C x‖ := by rw [hxnorm, mul_one, norm_abs_apply]
    _ ≤ A.singularValues (i : ℕ) := hCbound

/-- Pinching relative to `U + U orthogonal` is a contraction for every
unitarily invariant norm. -/
theorem uiNorm_pinch_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →ₗ[𝕜] E) : N (pinch U A) ≤ N A := by
  have hpinch : (2 : 𝕜) • pinch U A =
      A + U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap := by
    ext x
    simp [pinch, Submodule.reflection_apply, complementaryProjection]
    module
  have htri := N.add_le A
    (U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap)
  have hinv : N (U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap) = N A := by
    rw [N.unitary_comp, N.comp_unitary]
  rw [← hpinch, N.smul_eq, norm_ofNat, hinv] at htri
  linarith



/-- The Hermitian part of a pinched unitary is a contraction in quadratic
form, so `I - Re(pinch W)` is positive. -/
theorem LinearMap.IsPositive.of_hermitianPart_contraction
    (W : E ≃ₗᵢ[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    (LinearMap.id - hermitianPart (pinch U W.toLinearMap)).IsPositive := by
  intro x
  have hpinch : ‖pinch U W.toLinearMap x‖ ≤ ‖x‖ := by
    have horth : IsOrtho
        (projection U (W (projection U x)))
        (complementaryProjection U (W (complementaryProjection U x))) := by
      exact Submodule.isOrtho_starProjection_starProjection_orthogonal _ _
    rw [pinch, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, horth.norm_add_sq,
      W.norm_map, W.norm_map]
    rw [← U.norm_starProjection_sq_add_norm_starProjection_orthogonal_sq x]
  have hre : RCLike.re ⟪hermitianPart (pinch U W.toLinearMap) x, x⟫_𝕜 ≤ ‖x‖ ^ 2 := by
    rw [re_inner_hermitianPart]
    exact (RCLike.re_le_norm _).trans
      ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hpinch (norm_nonneg x)))
  rw [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_left, map_sub,
    inner_self_eq_norm_sq]
  linarith

/-- Ky Fan sums contract under two-block pinching. -/
theorem kyFanSum_pinch_le
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →ₗ[𝕜] E) (k : ℕ) :
    kyFanSum k (pinch U A) ≤ kyFanSum k A := by
  have hpinch : (2 : 𝕜) • pinch U A =
      A + U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap := by
    ext x
    simp [pinch, Submodule.reflection_apply, complementaryProjection]
    module
  have htri := kyFanSum_add_le k A
    (U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap)
  rw [← hpinch, kyFanSum_real_smul k (pinch U A) (by norm_num),
    kyFanSum_unitary_comp, kyFanSum_comp_unitary] at htri
  linarith

/-- Invertibility makes every finite singular value strictly positive. -/
theorem singularValues_pos_of_isUnit
    {A : E →ₗ[𝕜] E} (hA : IsUnit A)
    (i : Fin (finrank 𝕜 E)) : 0 < A.singularValues (i : ℕ) := by
  rw [A.singularValues_pos_iff_lt_finrank_range]
  have hrange : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective.mp
      (LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hA))
  rw [hrange, finrank_top]
  exact i.isLt

/-- Ky Fan sums of `2(I-C)` are the reversed affine eigenvalue sums of a
positive contraction `C`.  This packages the index reversal caused by the
map `t |-> 2(1-t)`. -/
theorem positive_affine_reverse_kyFanSum
    {C A : E →ₗ[𝕜] E} (hA : A.IsPositive) (hC : C.IsPositive)
    (hAC : A = (2 : 𝕜) • (LinearMap.id - C))
    (k : ℕ) :
    kyFanSum k A =
      ∑ i : Fin (min k (finrank 𝕜 E)),
        2 * (1 - hC.isSymmetric.eigenvalues rfl
          (Fin.rev ⟨(i : ℕ) + (finrank 𝕜 E - min k (finrank 𝕜 E)), by
            have := i.isLt
            omega⟩)) := by
  classical
  let n := finrank 𝕜 E
  let b := hC.isSymmetric.eigenvectorBasis rfl
  let br : OrthonormalBasis (Fin n) 𝕜 E := b.reindex (Equiv.refl _).trans Fin.revEquiv
  have heig : ∀ i : Fin n, A (br i) =
      (((2 * (1 - hC.isSymmetric.eigenvalues rfl (Fin.rev i)) : ℝ)) : 𝕜) • br i := by
    intro i
    rw [hAC]
    simp [br, b, hC.isSymmetric.apply_eigenvectorBasis]
  have hanti : Antitone (fun i : Fin n =>
      2 * (1 - hC.isSymmetric.eigenvalues rfl (Fin.rev i))) := by
    intro i j hij
    have hrev : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    have hλ := hC.isSymmetric.eigenvalues_antitone rfl hrev
    linarith
  have hnonneg : ∀ i : Fin n,
      0 ≤ 2 * (1 - hC.isSymmetric.eigenvalues rfl (Fin.rev i)) := by
    intro i
    have hAi := hA.nonneg_eigenvalues rfl i
    have hAeig := eigenvalues_eq_of_eigenbasis hA.isSymmetric rfl br hanti heig
    simpa [hAeig] using hAi
  have hσ : A.singularValues = fun j =>
      if hj : j < n then
        2 * (1 - hC.isSymmetric.eigenvalues rfl (Fin.rev ⟨j, hj⟩))
      else 0 := by
    ext j
    rcases lt_or_ge j n with hj | hj
    · rw [A.singularValues_of_lt rfl hj]
      have hAeig := eigenvalues_eq_of_eigenbasis hA.isSymmetric rfl br hanti heig
      rw [hAeig]
      simp only [dif_pos hj, Real.sqrt_sq (hnonneg ⟨j, hj⟩)]
    · rw [A.singularValues_of_finrank_le hj, dif_neg (not_lt.mpr hj)]
  rw [kyFanSum_eq_sum_fin]
  simp only [hσ]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr
  · ext j
    simp
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp [hj, n]

/-- If a symmetric contraction has operator norm at most `r`, every
sorted eigenvalue of `I - T^2` is at least `1-r^2`. -/
theorem eigenvalue_id_sub_sq_lower_bound
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ‖T.toContinuousLinearMap‖ ≤ r)
    (i : Fin (finrank 𝕜 E)) :
    1 - r ^ 2 ≤
      (hT.sub (LinearMap.isSymmetric_id (𝕜 := 𝕜) (E := E))).eigenvalues
        (by
          apply LinearMap.ext
          intro x
          simp [LinearMap.comp_apply, hT.adjoint_eq]
          module)
        i := by
  let B := LinearMap.id - T ∘ₗ T
  have hB : B.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_adjoint_eq]
    simp [B, map_sub, LinearMap.adjoint_comp, hT.adjoint_eq]
  let b := hB.eigenvectorBasis rfl
  let x := b i
  have hx : ‖x‖ = 1 := b.orthonormal.norm_eq_one i
  have hTx : ‖T x‖ ≤ r := by
    calc
      ‖T x‖ ≤ ‖T.toContinuousLinearMap‖ * ‖x‖ := T.toContinuousLinearMap.le_opNorm x
      _ ≤ r * 1 := mul_le_mul_of_nonneg_right hr (norm_nonneg x)
      _ = r := by rw [hx, mul_one]
  have heig := hB.apply_eigenvectorBasis rfl i
  have hinner := congrArg (fun y => RCLike.re ⟪y, x⟫_𝕜) heig
  simp only [B, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal,
    inner_self_eq_norm_sq, hx, one_pow, mul_one] at hinner
  rw [hT] at hinner
  nlinarith [sq_nonneg (r - ‖T x‖), norm_nonneg (T x)]

/-- The least cosine is the cosine of the largest principal angle.  Hence the
`pi / 3` bound gives a uniform lower bound `1/2` for the spectrum of the
canonical modulus. -/
theorem cosine_ge_half_of_principalAngle_le_pi_div_three
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hangle : principalAngles U V 0 ≤ Real.pi / 3)
    (i : Fin (finrank 𝕜 E)) :
    (1 / 2 : ℝ) ≤ (canonicalIntertwiner U V).singularValues (i : ℕ) := by
  have hgap : ‖(projection U - projection V).toContinuousLinearMap‖ ≤
      Real.sin (Real.pi / 3) := by
    rw [opNorm_projection_sub_eq_sin_largestAngle U V]
    exact Real.sin_le_sin_of_le
      (principalAngles_nonneg U V 0)
      (by positivity) hangle
  have hsym : (projection U - projection V).IsSymmetric :=
    projection_isSymmetric U |>.sub (projection_isSymmetric V)
  have hgram :
      (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V =
        LinearMap.id - (projection U - projection V) ∘ₗ
          (projection U - projection V) := by
    ext x
    simp [canonicalIntertwiner_adjoint_comp_self,
      complementaryProjection]
    module
  have hλ := eigenvalue_id_sub_sq_lower_bound
    (projection U - projection V) hsym
    (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]))
    hgap i
  rw [(canonicalIntertwiner U V).singularValues_of_lt rfl i.isLt, hgram]
  calc
    Real.sqrt ((canonicalIntertwiner U V).isSymmetric_adjoint_comp_self.eigenvalues rfl i)
        ≥ Real.sqrt (1 - Real.sin (Real.pi / 3) ^ 2) :=
      Real.sqrt_le_sqrt hλ
    _ = 1 / 2 := by
      rw [show Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 by
        rw [← Real.cos_pi_div_six, Real.cos_pi_div_six]]
      nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

/-- Weak majorization of the positive displacement squares.  This is the
operator-theoretic core of Davis--Kahan Proposition 4.3. -/
theorem directRotation_displacementSquare_kyFan
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) (k : ℕ) :
    kyFanSum k (displacementSquare (directRotation U V hacute).toLinearMap) ≤
      kyFanSum k (displacementSquare W.toLinearMap) := by
  classical
  let S := canonicalIntertwiner U V
  let C := ForMathlib.abs S
  let B := pinch U W.symm.toLinearMap
  let H := hermitianPart B
  let A0 := displacementSquare (directRotation U V hacute).toLinearMap
  let A1 := displacementSquare W.toLinearMap
  let P1 := pinch U A1
  have hCeq : ForMathlib.abs B = C := by
    simpa [B, C, S] using
      abs_pinch_competitor_eq_abs_canonicalIntertwiner U V W hmap
  have hA0 : A0 = (2 : 𝕜) • (LinearMap.id - C) := by
    rw [A0, displacementSquare_unitary]
    have hre := two_smul_abs_canonicalIntertwiner U V hacute
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hre x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.add_apply] at hx ⊢
    rw [hx]
    module
  have hP1 : P1 = (2 : 𝕜) • (LinearMap.id - H) := by
    rw [P1, A1, displacementSquare_unitary]
    ext x
    simp [pinch, hermitianPart, LinearMap.comp_apply,
      complementaryProjection]
    module
  have hpositive0 : A0.IsPositive := displacementSquare_positive _
  have hpositiveP : P1.IsPositive := by
    intro x
    rw [P1, pinch, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
    exact add_nonneg (displacementSquare_positive W.toLinearMap).nonneg_inner
      (displacementSquare_positive W.toLinearMap).nonneg_inner
  have hprefix : ∀ j, kyFanSum j A0 ≤ kyFanSum j P1 := by
    intro j
    -- Diagonalize `C` and `H`.  The Fan--Hoffman inequality gives
    -- `lambda_i(H) <= lambda_i(C) = sigma_i(B)`.  Applying the decreasing
    -- affine map `t |-> 2(1-t)` reverses the index order, and summing the
    -- largest `j` transformed eigenvalues gives the desired prefix bound.
    have hλ : ∀ i : Fin (finrank 𝕜 E),
        (hermitianPart_isSymmetric B).eigenvalues rfl i ≤
          (isPositive_abs B).isSymmetric.eigenvalues rfl i := by
      intro i
      rw [congrFun (eigenvalues_abs B) i]
      exact eigenvalues_hermitianPart_le_singularValues B i
    have hA0eig := positive_affine_reverse_kyFanSum
      hpositive0 (isPositive_abs B) (by rw [hA0, hCeq]) j
    have hP1eig := positive_affine_reverse_kyFanSum
      hpositiveP (LinearMap.IsPositive.of_hermitianPart_contraction W.symm U) hP1 j
    rw [hA0eig, hP1eig]
    exact Finset.sum_le_sum fun i _ => by
      have hi := hλ (Fin.rev i)
      linarith
  exact (hprefix k).trans (kyFanSum_pinch_le U A1 k)

/-- Every UI norm inherits the squared-displacement extremum. -/
theorem directRotation_displacementSquare_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (displacementSquare (directRotation U V hacute).toLinearMap) ≤
      N (displacementSquare W.toLinearMap) :=
  N.apply_le_of_kyFanSum_le
    (directRotation_displacementSquare_kyFan U V hacute W hmap)

/-!
The corresponding full-displacement theorem is intentionally absent.  The
valid arbitrary-UI endpoint is `uiNorm_restrictedDisplacement_le`.
-/

end DavisKahanTheory
end ForMathlib
