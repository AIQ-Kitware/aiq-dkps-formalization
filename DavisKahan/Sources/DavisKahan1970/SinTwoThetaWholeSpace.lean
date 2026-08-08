/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Angle.PaperDoubleAngle
import DavisKahan.InfiniteDimensional.DoubleAngleSpectrum
import DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws

/-!
# The whole-space half of the `sin 2Θ` theorem

Section 2 of Davis--Kahan 1970 states the `sin 2Θ` theorem with **two**
conclusions,

`δ ‖sin 2Θ₀‖ ≤ 2‖R‖`  and  `δ ‖sin 2Θ‖ ≤ 2‖H‖`,

for every unitarily invariant norm.  The directed `Θ₀` half is already in the
build.  This module proves the ambient `Θ` half, which is equation (7.5) of the
paper's Section 7 proof.

## The route

Write `X` for the reflection through the second subspace.  `X` is a self-adjoint
unitary, so `X A X` has the *same* compression spectra on the reflected subspace
`X U` that `A` has on `U`, and the `sin Θ` estimate applies verbatim to the pair
`(U, X U)` with perturbation `X A X - A`.  The displacement `X A X - A` equals
`X H X - H` up to sign, hence has gauge at most `2` times that of `H`.  The
geometric input is that the pair `(U, X U)` realises the *doubled* angle,

`|P_{X U} - P_U| = sin 2Θ`,

as an operator identity, proved in
`DavisKahan/Geometry/Angle/PaperDoubleAngle.lean`.  Only the operator-norm form
of that identification was previously available, which is not enough for an
arbitrary unitarily invariant norm.

The two directed estimates are coupled by Lemma 6.1 and contracted by Lemma 6.2,
exactly as in Proposition 6.1 — not by a triangle inequality, so the constant is
the paper's `2` and not `4`.

## Convention

Following the repository's existing `sin 2Θ` development
(`DavisKahan/InfiniteDimensional/DoubleAngleSpectrum.lean`), the internal
spectral gap is carried by `A` on its reducing subspace `U`, and `V` is the
reducing subspace of the comparison operator `B`.  The printed theorem carries
the gap on `A + H` at `QH`; the two readings differ only by exchanging the roles
of the two operators, under which `‖H‖` is unchanged.

## Main results

* `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_all_kyFan`: the Ky Fan form,
  `δ · kyFan_k (sin 2Θ) ≤ 2 · kyFan_k (B - A)` for every `k`.
* `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`: the source form,
  `δ · N (sin 2Θ) ≤ 2 · N (B - A)` for every unitarily invariant norm `N` in the
  paper's sense.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the `sin 2Θ` theorem of Section 2
  and its proof in Section 7, equations (7.1)--(7.5).
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionSinTwoTheta
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-! ### The sharp block form of the bounded `sin Θ` estimate -/

/-- **The bounded `sin Θ` estimate at genuine spectra, before the perturbation
block is contracted.**  `sinTheta_spectrum_gauge` finishes by replacing the
projected perturbation block with the whole perturbation; Lemma 6.1 needs the
estimate one step earlier, block against block, which is what the Sylvester
engine actually produces. -/
theorem sinTheta_spectrum_block_gauge
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    d * N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) ≤
      N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL) :=
  (mem_and_gauge_sylvester_le_of_spectrum_intervalExterior N
    (isSelfAdjoint_compressOperator hB Vᗮ)
    (isSelfAdjoint_compressOperator hA U)
    hd hab hUspec hVspec (compress_sylvester_of_reduces hU hV)
    (N.comp_mem _ _ hMem)).2

/-- The scaled identity block, in coordinates. -/
theorem paperBlockCompression_smul_one (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection] (c : ℂ) :
    paperBlockCompression Ω Γ (c • (1 : E →L[ℂ] E)) =
      c • (Ω.orthogonalProjectionOnto ∘L Γ.subtypeL) := by
  rw [paperBlockCompression, Submodule.adjoint_subtypeL]
  ext x
  simp

/-- A perturbation block, in coordinates. -/
theorem paperBlockCompression_apply (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    paperBlockCompression Ω Γ K =
      Ω.orthogonalProjectionOnto ∘L K ∘L Γ.subtypeL := by
  rw [paperBlockCompression, Submodule.adjoint_subtypeL]

/-- **The sharp block estimate, ambient and at every Ky Fan level.**  This is the
hypothesis shape Lemma 6.1 consumes. -/
theorem sinTheta_spectrum_block_all_kyFan
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x) :
    ∀ k : ℕ,
      kyFanApproximationGauge k
          (paperProjectionBlock Vᗮ U (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E))) ≤
        kyFanApproximationGauge k (paperProjectionBlock Vᗮ U (B - A)) := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hdnorm : ‖((d : ℝ) : ℂ)‖ = d := by simp [abs_of_pos hd]
    have hraw := sinTheta_spectrum_block_gauge
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk).toSymmetricOperatorIdealFamily
      hA hB hU hV hd hab hUspec hVspec
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk (B - A))
    rw [KyFanDominantIdealFamily.toSymmetric_gaugeReal,
      KyFanDominantIdealFamily.toSymmetric_gaugeReal,
      KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at hraw
    have hone := (paperProjectionBlock_same_compression Vᗮ U
      (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E))).kyFanApproximationGauge_eq k
    have hpert :=
      (paperProjectionBlock_same_compression Vᗮ U (B - A)).kyFanApproximationGauge_eq k
    rw [hone, hpert, paperBlockCompression_smul_one, paperBlockCompression_apply,
      kyFanApproximationGauge_smul, hdnorm]
    exact hraw

/-! ### The sharp symmetric `sin Θ` theorem at genuine spectra -/

section Symmetric

variable {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The symmetric bounded `sin Θ` theorem at genuine spectra, sharp.**  Both
directed spectral configurations give `δ · gauge (sin Θ) ≤ gauge (B - A)` for the
*ambient* sine `|P_V - P_U|`, with constant `1`.

`sinTheta_spectrum_gauge_symmetric` proves the same statement with constant `2`,
by a triangle inequality on the two directed cross blocks.  Here the two blocks
are coupled by Lemma 6.1 and contracted by Lemma 6.2 instead, which is the
paper's argument for Proposition 6.1 and loses nothing. -/
theorem symmetric_sinTheta_spectrum_all_kyFan
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hVspec : spectrum ℝ (compressOperator V B) ⊆ Set.Icc a b)
    (hVspec' : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x) :
    ∀ k : ℕ,
      d * kyFanApproximationGauge k
          ((V.starProjection - U.starProjection).modulus) ≤
        kyFanApproximationGauge k (B - A) := by
  intro k
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  have hdnorm : ‖((d : ℝ) : ℂ)‖ = d := by simp [abs_of_pos hd]
  have hpertsa : IsSelfAdjoint (B - A) := hB.sub hA
  have hforward := sinTheta_spectrum_block_all_kyFan hA hB hU hV hd hab
    hUspec hVspec'
  have hreverse := sinTheta_spectrum_block_all_kyFan hB hA hV hU hd hab
    hVspec hUspec'
  -- the identity blocks, computed
  have hid₁ : paperProjectionBlock Uᗮᗮ Vᗮ (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      ((d : ℝ) : ℂ) • (U.starProjection ∘L Vᗮ.starProjection) := by
    simp only [hUperp, paperProjectionBlock]
    ext x
    simp
  have hid₂ : paperProjectionBlock Vᗮ U (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      ((d : ℝ) : ℂ) • (Vᗮ.starProjection ∘L U.starProjection) := by
    simp only [paperProjectionBlock]
    ext x
    simp
  have hswap : U.starProjection ∘L Vᗮ.starProjection =
      (Vᗮ.starProjection ∘L U.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection Vᗮ).adjoint_eq]
  have hcombine := paperLemma61_all_kyFan Uᗮ V
    (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E))
    (B - A) (B - A)
    (fun j => by
      have h := hreverse j
      have hblock : paperProjectionBlock Uᗮ V (A - B) =
          -paperProjectionBlock Uᗮ V (B - A) := by
        rw [paperProjectionBlock, paperProjectionBlock,
          show A - B = -(B - A) from by abel]
        ext x
        simp
      rw [hblock, kyFanApproximationGauge_neg] at h
      exact h)
    (fun j => by
      have h := hforward j
      have hblock : paperProjectionBlock Uᗮᗮ Vᗮ (B - A) =
          (paperProjectionBlock Vᗮ U (B - A)).adjoint := by
        simp only [hUperp, paperProjectionBlock]
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
          (isSelfAdjoint_starProjection U).adjoint_eq,
          (isSelfAdjoint_starProjection Vᗮ).adjoint_eq,
          hpertsa.adjoint_eq]
        rfl
      rw [hblock, kyFanApproximationGauge_adjoint, hid₁, hswap,
        kyFanApproximationGauge_smul, kyFanApproximationGauge_adjoint]
      rw [hid₂, kyFanApproximationGauge_smul] at h
      exact h) k
  -- the two identity blocks add up to the cross sine sum
  have hcross :
      paperProjectionBlock Uᗮ V (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) +
          paperProjectionBlock Uᗮᗮ Vᗮ (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
        ((d : ℝ) : ℂ) • paperCrossSineSum U V := by
    simp only [hUperp]
    ext x
    simp [paperProjectionBlock, paperCrossSineSum, smul_add]
  rw [hcross] at hcombine
  have hpinch := paperDiagonalPair_all_kyFan_le Uᗮ V (B - A) k
  have hsine : kyFanApproximationGauge k (paperCrossSineSum U V) =
      kyFanApproximationGauge k
        ((V.starProjection - U.starProjection).modulus) := by
    rw [(paperCrossSineSum_same_projectionDiff U V).kyFanApproximationGauge_eq k]
    exact ((modulus_hasSameApproximationNumbers
      (V.starProjection - U.starProjection)).kyFanGauge_eq k).symm
  rw [kyFanApproximationGauge_smul, hdnorm, hsine] at hcombine
  exact hcombine.trans hpinch

end Symmetric

/-! ### The whole-space `sin 2Θ` theorem -/

section WholeSpace

variable {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [U.HasOrthogonalProjection] in
/-- The reflected configuration has the transported compression spectrum. -/
private theorem reflected_spectra (A : E →L[ℂ] E) (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (compressOperator
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
        (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator U A) :=
  spectrum_compressOperator_map U A V.reflection

omit [U.HasOrthogonalProjection] in
/-- The reflected configuration on the orthogonal complement. -/
private theorem reflected_spectra_orthogonal (A : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (compressOperator
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ
        (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator Uᗮ A) :=
  (spectrum_compressOperator_congr
      (Submodule.map_orthogonal_equiv U V.reflection).symm _).trans
    (spectrum_compressOperator_map Uᗮ A V.reflection)

omit [U.HasOrthogonalProjection] in
/-- The reflection displacement is bounded by twice the perturbation, at every
Ky Fan level: `X A X - A = X H X - H` up to sign, and `X` is unitary. -/
private theorem kyFan_reflectionDisplacement_le
    (hV : Reduces B V) (k : ℕ) :
    kyFanApproximationGauge k (conjByIsometryEquiv V.reflection A - A) ≤
      2 * kyFanApproximationGauge k (B - A) := by
  have hdefect : conjByIsometryEquiv V.reflection A - A =
      Submodule.reflectionOperator V ∘L (A - B) ∘L
          Submodule.reflectionOperator V - (A - B) := by
    rw [conjByReflection_sub_eq_reflectionDefect,
      reflectionDefect_eq_perturbationDefect A B V hV]
  have hAB : kyFanApproximationGauge k (A - B) =
      kyFanApproximationGauge k (B - A) := by
    rw [show A - B = -(B - A) from by abel, kyFanApproximationGauge_neg]
  have h0 : 0 ≤ kyFanApproximationGauge k (A - B) :=
    kyFanApproximationGauge_nonneg k _
  have h1 : ‖(Submodule.reflectionOperator V : E →L[ℂ] E)‖ ≤ 1 := by
    exact_mod_cast Submodule.norm_reflectionOperator_le_one V
  have hconj : kyFanApproximationGauge k
      (Submodule.reflectionOperator V ∘L (A - B) ∘L
        Submodule.reflectionOperator V) ≤
      kyFanApproximationGauge k (A - B) := by
    refine (kyFanApproximationGauge_comp_le k _ _ _).trans ?_
    calc ‖(Submodule.reflectionOperator V : E →L[ℂ] E)‖ *
          kyFanApproximationGauge k (A - B) *
          ‖(Submodule.reflectionOperator V : E →L[ℂ] E)‖
        ≤ 1 * kyFanApproximationGauge k (A - B) * 1 := by
          gcongr
      _ = kyFanApproximationGauge k (A - B) := by ring
  have hsplit : kyFanApproximationGauge k
      (Submodule.reflectionOperator V ∘L (A - B) ∘L
        Submodule.reflectionOperator V - (A - B)) ≤
      kyFanApproximationGauge k
        (Submodule.reflectionOperator V ∘L (A - B) ∘L
          Submodule.reflectionOperator V) +
        kyFanApproximationGauge k (A - B) := by
    have h := kyFanApproximationGauge_add_le k
      (Submodule.reflectionOperator V ∘L (A - B) ∘L
        Submodule.reflectionOperator V) (-(A - B))
    rwa [← sub_eq_add_neg, kyFanApproximationGauge_neg] at h
  rw [hdefect]
  rw [hAB] at hconj hsplit
  linarith

/-- **The whole-space `sin 2Θ` theorem, Ky Fan form.**  Equation (7.5) of
Davis--Kahan 1970 at every finite Ky Fan gauge. -/
theorem sinTwoTheta_wholeSpace_all_kyFan
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    ∀ k : ℕ,
      d * kyFanApproximationGauge k (paperSinTwoAngleOperatorC U V) ≤
        2 * kyFanApproximationGauge k (B - A) := by
  intro k
  have hkey := symmetric_sinTheta_spectrum_all_kyFan hA
      (isSelfAdjoint_conjByIsometryEquiv V.reflection hA) hU
      (hU.map_isometryEquiv V.reflection) hd hab hUspec hUspec'
      (by rw [reflected_spectra A U V]; exact hUspec)
      (by rw [reflected_spectra_orthogonal A U V]; exact hUspec') k
  rw [← paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub U V] at hkey
  exact hkey.trans (kyFan_reflectionDisplacement_le hV k)

/-- **The whole-space `sin 2Θ` theorem for every source unitarily invariant
norm**: `δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, the second conclusion of the Section 2 `sin 2Θ`
theorem and equation (7.5) of Section 7. -/
theorem sinTwoTheta_wholeSpace_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (paperSinTwoAngleOperatorC U V) ∧
      d * N.gauge (paperSinTwoAngleOperatorC U V) ≤
        2 * N.gauge (B - A) := by
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hscaled : ∀ k : ℕ,
      d * kyFanApproximationGauge k (paperSinTwoAngleOperatorC U V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • (B - A)) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo]
    exact sinTwoTheta_wholeSpace_all_kyFan hA hB hU hV hd hab hUspec hUspec' k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • (B - A)) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hd hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rwa [N.gauge_smul _ hMem, htwo] at hle

end WholeSpace

end

end DavisKahan1970
end TauCeti
