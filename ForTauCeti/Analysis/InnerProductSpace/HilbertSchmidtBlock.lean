/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.SylvesterGroup
import ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Commutant

/-!
# Two-sided blocks on the Hilbert–Schmidt space

`Z ↦ P ∘ Z ∘ Q` is a bounded operator on the Hilbert–Schmidt class, and when
`P` commutes with `U t` and `Q` with `V t` it commutes with the Sylvester flow.

That is the cutting step of the block argument for the Sylvester spectral gap:
`P` and `Q` are spectral projections of the two generators, so they commute with
their own groups, hence the block map commutes with the flow, hence — by
`OneParameterUnitaryGroup.generator_commute` — it preserves the generator's
domain and commutes with the generator.  A block of a vector in `dom 𝒮` is then
again in `dom 𝒮`, with `𝒮` acting blockwise, which is what lets the per-block
estimate be applied and the blocks reassembled.

Boundedness is the two ideal properties of the Hilbert–Schmidt energy applied in
turn: `‖P ∘ Z ∘ Q‖ ≤ ‖P‖ ‖Q‖ ‖Z‖`.

## Provenance

*New.*
-/

open scoped ENNReal NNReal

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section Defs

variable (b : HilbertBasis ι 𝕜 F) (P : E →L[𝕜] E) (Q : F →L[𝕜] F)

theorem energy_block_ne_top (f : lp (fun _ : ι => E) 2) :
    (((P.comp (ofLp b f)).comp Q)).hilbertSchmidtEnergy b ≠ ⊤ := by
  have h1 : ((P.comp (ofLp b f)).comp Q).hilbertSchmidtEnergy b
      ≤ ‖Q‖ₑ ^ 2 * (P.comp (ofLp b f)).hilbertSchmidtEnergy b :=
    ContinuousLinearMap.hilbertSchmidtEnergy_comp_right_le _ _ b b
  have h2 : (P.comp (ofLp b f)).hilbertSchmidtEnergy b
      ≤ ‖P‖ₑ ^ 2 * (ofLp b f).hilbertSchmidtEnergy b :=
    ContinuousLinearMap.hilbertSchmidtEnergy_comp_left_le _ _ b
  have hfin : (ofLp b f).hilbertSchmidtEnergy b ≠ ⊤ := by
    rw [energy_ofLp]; exact ENNReal.ofReal_ne_top
  have hchain : ((P.comp (ofLp b f)).comp Q).hilbertSchmidtEnergy b
      ≤ ‖Q‖ₑ ^ 2 * (‖P‖ₑ ^ 2 * (ofLp b f).hilbertSchmidtEnergy b) := h1.trans (by gcongr)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hfin)) hchain

/-- The two-sided block `Z ↦ P ∘ Z ∘ Q`, in the `ℓ²` model. -/
noncomputable def blockFun (f : lp (fun _ : ι => E) 2) : lp (fun _ : ι => E) 2 :=
  ofOperator b ((P.comp (ofLp b f)).comp Q) (energy_block_ne_top b P Q f)

@[simp] theorem ofLp_blockFun (f : lp (fun _ : ι => E) 2) :
    ofLp b (blockFun b P Q f) = (P.comp (ofLp b f)).comp Q :=
  ofLp_ofOperator _ _ _

theorem blockFun_add (f g : lp (fun _ : ι => E) 2) :
    blockFun b P Q (f + g) = blockFun b P Q f + blockFun b P Q g := by
  refine ofLp_injective b ?_
  rw [ofLp_add, ofLp_blockFun, ofLp_blockFun, ofLp_blockFun, ofLp_add]
  ext x
  simp

theorem blockFun_smul (c : 𝕜) (f : lp (fun _ : ι => E) 2) :
    blockFun b P Q (c • f) = c • blockFun b P Q f := by
  refine ofLp_injective b ?_
  rw [ofLp_smul, ofLp_blockFun, ofLp_blockFun, ofLp_smul]
  ext x
  simp

theorem norm_blockFun_le (f : lp (fun _ : ι => E) 2) :
    ‖blockFun b P Q f‖ ≤ ‖P‖ * ‖Q‖ * ‖f‖ := by
  have hE : ENNReal.ofReal (‖blockFun b P Q f‖ ^ 2)
      ≤ ‖Q‖ₑ ^ 2 * (‖P‖ₑ ^ 2 * ENNReal.ofReal (‖f‖ ^ 2)) := by
    rw [← energy_ofLp b (blockFun b P Q f), ofLp_blockFun, ← energy_ofLp b f]
    refine le_trans (ContinuousLinearMap.hilbertSchmidtEnergy_comp_right_le _ _ b b) ?_
    gcongr
    exact ContinuousLinearMap.hilbertSchmidtEnergy_comp_left_le _ _ b
  have hPe : ‖P‖ₑ = ENNReal.ofReal ‖P‖ := by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  have hQe : ‖Q‖ₑ = ENNReal.ofReal ‖Q‖ := by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  have hrw : ‖Q‖ₑ ^ 2 * (‖P‖ₑ ^ 2 * ENNReal.ofReal (‖f‖ ^ 2))
      = ENNReal.ofReal ((‖P‖ * ‖Q‖ * ‖f‖) ^ 2) := by
    rw [hPe, hQe, ← ENNReal.ofReal_pow (norm_nonneg Q), ← ENNReal.ofReal_pow (norm_nonneg P),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hrw, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
  have hc : (0 : ℝ) ≤ ‖P‖ * ‖Q‖ * ‖f‖ := by positivity
  have hsq := Real.sqrt_le_sqrt hE
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hc] at hsq

/-- The two-sided block as a bounded operator. -/
noncomputable def blockCLM :
    lp (fun _ : ι => E) 2 →L[𝕜] lp (fun _ : ι => E) 2 :=
  LinearMap.mkContinuous
    { toFun := blockFun b P Q
      map_add' := blockFun_add b P Q
      map_smul' := fun c f => blockFun_smul b P Q c f } (‖P‖ * ‖Q‖)
    (fun f => by simpa [mul_assoc] using norm_blockFun_le b P Q f)

@[simp] theorem blockCLM_apply (f : lp (fun _ : ι => E) 2) :
    blockCLM b P Q f = blockFun b P Q f := rfl

end Defs

/-- **A block commutes with the Sylvester flow** when each side commutes with
its own group. -/
theorem blockCLM_comm_sylvesterGroup {ι : Type*} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : TauCeti.OneParameterUnitaryGroup E) (V : TauCeti.OneParameterUnitaryGroup F)
    (b : HilbertBasis ι ℂ F) (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    (hP : ∀ t : ℝ, ∀ y : E, P (U.U t y) = U.U t (P y))
    (hQ : ∀ t : ℝ, ∀ y : F, Q (V.U t y) = V.U t (Q y))
    (t : ℝ) (f : lp (fun _ : ι => E) 2) :
    blockCLM b P Q (sylvesterFun U V b t f) = sylvesterFun U V b t (blockCLM b P Q f) := by
  refine ofLp_injective b ?_
  simp only [blockCLM_apply, ofLp_sylvesterFun, conjOp, ofLp_blockFun]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [hQ (-t) x, hP t]

end HilbertSchmidt
end TauCeti
