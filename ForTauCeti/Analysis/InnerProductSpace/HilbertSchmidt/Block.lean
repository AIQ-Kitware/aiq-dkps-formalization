/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Group
public import ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Commutant
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Pythagoras

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

## Sources

The two-sided block decomposition of a Hilbert--Schmidt operator is the
operator-matrix view of the `ℓ²`-of-columns presentation
(`TauCeti/Analysis/InnerProductSpace/HilbertSchmidt/Columns.lean`, with the
standard references there).  Its use as the carrier of a Sylvester estimate follows
Bhatia--Davis--McIntosh; see
`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`.

## Provenance

*New.*
-/

public section

open scoped ENNReal NNReal

namespace TauCeti
namespace HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section Defs

variable (b : HilbertBasis ι 𝕜 F) (P : E →L[𝕜] E) (Q : F →L[𝕜] F)

/-- Sandwiching a Hilbert--Schmidt operator between two bounded operators keeps its energy finite,
so the block map lands back in the Hilbert--Schmidt class. -/
theorem energy_block_ne_top (f : lp (fun _ : ι => E) 2) :
    (((P.comp (b.columnOperator f)).comp Q)).hilbertSchmidtEnergy b ≠ ⊤ := by
  have h1 : ((P.comp (b.columnOperator f)).comp Q).hilbertSchmidtEnergy b
      ≤ ‖Q‖ₑ ^ 2 * (P.comp (b.columnOperator f)).hilbertSchmidtEnergy b :=
    by simpa only [mul_comm] using
      ContinuousLinearMap.hilbertSchmidtEnergy_comp_le_right (P.comp (b.columnOperator f)) Q b b
  have h2 : (P.comp (b.columnOperator f)).hilbertSchmidtEnergy b
      ≤ ‖P‖ₑ ^ 2 * (b.columnOperator f).hilbertSchmidtEnergy b :=
    ContinuousLinearMap.hilbertSchmidtEnergy_comp_le_left _ _ b
  have hfin : (b.columnOperator f).hilbertSchmidtEnergy b ≠ ⊤ := by
    rw [HilbertBasis.hilbertSchmidtEnergy_columnOperator]; simp
  have hchain : ((P.comp (b.columnOperator f)).comp Q).hilbertSchmidtEnergy b
      ≤ ‖Q‖ₑ ^ 2 * (‖P‖ₑ ^ 2 * (b.columnOperator f).hilbertSchmidtEnergy b) := h1.trans (by gcongr)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hfin)) hchain

/-- The two-sided block `Z ↦ P ∘ Z ∘ Q`, in the `ℓ²` model. -/
noncomputable def blockFun (f : lp (fun _ : ι => E) 2) : lp (fun _ : ι => E) 2 :=
  ⟨fun i => ((P.comp (b.columnOperator f)).comp Q) (b i),
    (((P.comp (b.columnOperator f)).comp Q).hilbertSchmidtEnergy_ne_top_iff_memℓp b).mp
      (energy_block_ne_top b P Q f)⟩

/-- The block map, seen through the operator model. -/
@[simp] theorem columnOperator_blockFun (f : lp (fun _ : ι => E) 2) :
    b.columnOperator (blockFun b P Q f) = (P.comp (b.columnOperator f)).comp Q :=
  b.columnOperator_mk _ _

/-- The two-sided block map is additive. -/
theorem blockFun_add (f g : lp (fun _ : ι => E) 2) :
    blockFun b P Q (f + g) = blockFun b P Q f + blockFun b P Q g := by
  refine b.columnOperator_injective ?_
  rw [map_add, columnOperator_blockFun, columnOperator_blockFun, columnOperator_blockFun, map_add]
  ext x
  simp

/-- The two-sided block map is homogeneous.  With `blockFun_add` this makes it linear on the `lp`
model, which is what lets it be bundled as a continuous linear map. -/
theorem blockFun_smul (c : 𝕜) (f : lp (fun _ : ι => E) 2) :
    blockFun b P Q (c • f) = c • blockFun b P Q f := by
  refine b.columnOperator_injective ?_
  rw [map_smul, columnOperator_blockFun, columnOperator_blockFun, map_smul]
  ext x
  simp

/-- The block map is bounded by `‖P‖ ‖Q‖` -- the two-sided ideal bound, in the form needed to bundle
it continuously. -/
theorem norm_blockFun_le (f : lp (fun _ : ι => E) 2) :
    ‖blockFun b P Q f‖ ≤ ‖P‖ * ‖Q‖ * ‖f‖ := by
  calc
    ‖blockFun b P Q f‖ = (b.columnOperator (blockFun b P Q f)).hilbertSchmidtNorm :=
      (b.hilbertSchmidtNorm_columnOperator _).symm
    _ = ((P.comp (b.columnOperator f)).comp Q).hilbertSchmidtNorm := by
      rw [columnOperator_blockFun]
    _ ≤ ‖P‖ * (b.columnOperator f).hilbertSchmidtNorm * ‖Q‖ := by
      simpa only [ContinuousLinearMap.comp_assoc] using
        ContinuousLinearMap.hilbertSchmidtNorm_comp_comp_le P (b.columnOperator f) Q b (by simp)
    _ = ‖P‖ * ‖Q‖ * ‖f‖ := by rw [b.hilbertSchmidtNorm_columnOperator]; ring

/-- The two-sided block as a bounded operator. -/
noncomputable def blockCLM :
    lp (fun _ : ι => E) 2 →L[𝕜] lp (fun _ : ι => E) 2 :=
  LinearMap.mkContinuous
    { toFun := blockFun b P Q
      map_add' := blockFun_add b P Q
      map_smul' := fun c f => blockFun_smul b P Q c f } (‖P‖ * ‖Q‖)
    (fun f => by simpa [mul_assoc] using norm_blockFun_le b P Q f)

/-- The bundled block map acts as `blockFun`. -/
@[simp] theorem blockCLM_apply (f : lp (fun _ : ι => E) 2) :
    blockCLM b P Q f = blockFun b P Q f := (rfl)

end Defs

/-! ### A block is fixed by its own projections -/

/-- An idempotent left factor fixes the block it cuts.  This is one of the two
hypotheses the per-block Sylvester estimate takes. -/
theorem comp_columnOperator_blockFun_left (b : HilbertBasis ι 𝕜 F) {P : E →L[𝕜] E}
    (hP : P.comp P = P) (Q : F →L[𝕜] F) (f : lp (fun _ : ι => E) 2) :
    P.comp (b.columnOperator (blockFun b P Q f)) = b.columnOperator (blockFun b P Q f) := by
  rw [columnOperator_blockFun, ← ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc, hP]

/-- An idempotent right factor fixes the block it cuts. -/
theorem comp_columnOperator_blockFun_right (b : HilbertBasis ι 𝕜 F) (P : E →L[𝕜] E)
    {Q : F →L[𝕜] F} (hQ : Q.comp Q = Q) (f : lp (fun _ : ι => E) 2) :
    (b.columnOperator (blockFun b P Q f)).comp Q = b.columnOperator (blockFun b P Q f) := by
  rw [columnOperator_blockFun, ContinuousLinearMap.comp_assoc, hQ]


/-! ### Blocks split the norm -/

/-- **Two-sided blocks split the `ℓ²` norm.**  This is the hypothesis
`TauCeti.enorm_ge_of_blocks` takes, for the block family of a pair of
norm-splitting families. -/
theorem tsum_enorm_sq_blockFun {ι' : Type*} (b : HilbertBasis ι 𝕜 F)
    (P : ι' → (E →L[𝕜] E)) (Q : ι' → (F →L[𝕜] F))
    (hP : ∀ v : E, ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (hQ : ∀ v : F, ∑' j, ‖(Q j).adjoint v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (f : lp (fun _ : ι => E) 2) :
    ∑' p : ι' × ι', ‖blockFun b (P p.1) (Q p.2) f‖ₑ ^ 2 = ‖f‖ₑ ^ 2 := by
  have hterm : ∀ p : ι' × ι', ‖blockFun b (P p.1) (Q p.2) f‖ₑ ^ 2
      = (((P p.1).comp (b.columnOperator f)).comp (Q p.2)).hilbertSchmidtEnergy b := by
    intro p
    rw [← b.hilbertSchmidtEnergy_columnOperator (blockFun b (P p.1) (Q p.2) f),
      columnOperator_blockFun]
  rw [tsum_congr hterm, ENNReal.tsum_prod', ENNReal.tsum_comm,
    ← b.hilbertSchmidtEnergy_columnOperator f]
  simpa only [ContinuousLinearMap.comp_assoc] using
    ContinuousLinearMap.tsum_tsum_hilbertSchmidtEnergy_comp (b.columnOperator f) b b P Q hP hQ


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
  refine b.columnOperator_injective ?_
  simp only [blockCLM_apply, columnOperator_sylvesterFun, conjOp, columnOperator_blockFun]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [hQ (-t) x, hP t]

end HilbertSchmidt
end TauCeti
