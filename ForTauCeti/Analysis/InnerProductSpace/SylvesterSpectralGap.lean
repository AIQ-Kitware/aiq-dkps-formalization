/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.SylvesterBlockEstimate
import ForTauCeti.Analysis.InnerProductSpace.BlockLowerBound
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralGrid
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.StoneUniqueness
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralProjectionGroup

/-!
# The Sylvester spectral gap

Separated spectra force a lower bound on the Sylvester operator, hence a spectral
gap at **every** vector of the Hilbert–Schmidt space.

The argument cuts the line into cells of width `ε`, estimates `𝒮` on each
two-sided spectral block, and reassembles.  All of the pieces are proved
elsewhere; this module is the chain:

`grid → blocks → per-block estimate → global lower bound → resolvent point → gap`

## The one place a case split is needed

A block whose left or right projection is **zero** is itself zero, and the
estimate holds trivially.  A block whose projections are both nonzero has cells
meeting both spectra (`exists_mem_spectrum_of_specProjection_ne_zero`), and the
separation hypothesis then applies to actual spectral points — which is what
bounds the *representatives* `kε` and `lε` apart, up to the cell radius.

## Provenance

*New.*  The donor proves the same statement in the tensor model, through joint
projection-valued measures and a product-measure identity whose closure is
~20,000 lines of Born-rule machinery.  Nothing of that appears here.
-/

open scoped InnerProductSpace ENNReal
open TauCeti.OneParameterUnitaryGroup (generator)

namespace TauCeti
namespace HilbertSchmidt

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The zero column vector rebuilds to the zero operator. -/
@[simp] theorem ofLp_zero (b : HilbertBasis ι ℂ F) :
    ofLp b (0 : lp (fun _ : ι => E) 2) = 0 := by
  ext x
  simp [ofLp_apply]

/-- A block with a zero factor is the zero block. -/
theorem blockFun_eq_zero_left (b : HilbertBasis ι ℂ F) (Q : F →L[ℂ] F)
    (f : lp (fun _ : ι => E) 2) : blockFun b (0 : E →L[ℂ] E) Q f = 0 := by
  refine ofLp_injective b ?_
  rw [ofLp_blockFun, ofLp_zero]
  ext x
  simp

/-- A block with a zero right factor vanishes. -/
theorem blockFun_eq_zero_right (b : HilbertBasis ι ℂ F) (P : E →L[ℂ] E)
    (f : lp (fun _ : ι => E) 2) : blockFun b P (0 : F →L[ℂ] F) f = 0 := by
  refine ofLp_injective b ?_
  rw [ofLp_blockFun, ofLp_zero]
  ext x
  simp

section Gap

variable {A : E →ₗ.[ℂ] E} {Bop : F →ₗ.[ℂ] F}

/-- The spectral projection of the `k`-th grid cell. -/
private noncomputable def gridProj (hA : IsSelfAdjoint A) (ε : ℝ) (k : ℤ) : E →L[ℂ] E :=
  TauCeti.LinearPMap.specProjection hA (TauCeti.LinearPMap.gridCell ε k)
    (TauCeti.LinearPMap.measurableSet_gridCell ε k)

/-- The grid projections commute with the group they were built from. -/
private theorem gridProj_comm (hA : IsSelfAdjoint A) (ε : ℝ) (k : ℤ) (t : ℝ) (y : E) :
    gridProj hA ε k ((TauCeti.LinearPMap.genToGroup hA).U t y)
      = (TauCeti.LinearPMap.genToGroup hA).U t (gridProj hA ε k y) :=
  TauCeti.LinearPMap.specProjection_expLimit_apply hA _ _ t y

/-- **The per-block bound, with the shift.**  On a block whose two projections
are both nonzero the separation hypothesis applies to genuine spectral points,
and the block estimate turns it into a bound on `𝒮 - s`.  A block with a zero
projection is zero, where the bound is vacuous.

The group is a parameter rather than `genToGroup hA` so that no `set` has to
rewrite inside the type of `z`. -/
theorem norm_block_ge (U : TauCeti.OneParameterUnitaryGroup E)
    (V : TauCeti.OneParameterUnitaryGroup F)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint Bop)
    (hUA : generator U = A) (hVB : generator V = Bop)
    (b : HilbertBasis ι ℂ F) {δ ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ lam : ℝ, (lam : ℂ) ∈ TauCeti.LinearPMap.spectrum A →
      ∀ alp : ℝ, (alp : ℂ) ∈ TauCeti.LinearPMap.spectrum Bop → δ ≤ |lam - alp|)
    (s : ℝ) (k l : ℤ)
    (hUcomm : ∀ (t : ℝ) (y : E), gridProj hA ε k (U.U t y) = U.U t (gridProj hA ε k y))
    (hVcomm : ∀ (t : ℝ) (y : F), gridProj hB ε l (V.U t y) = V.U t (gridProj hB ε l y))
    (z : (generator (sylvesterGroup U V b)).domain) :
    (δ - |s| - 4 * ε)
        * ‖blockCLM b (gridProj hA ε k) (gridProj hB ε l) (z : lp (fun _ : ι => E) 2)‖
      ≤ ‖blockCLM b (gridProj hA ε k) (gridProj hB ε l)
          (generator (sylvesterGroup U V b) z - (s : ℂ) • (z : lp (fun _ : ι => E) 2))‖ := by
  have hT : ∀ (t : ℝ) (y : lp (fun _ : ι => E) 2),
      blockCLM b (gridProj hA ε k) (gridProj hB ε l) ((sylvesterGroup U V b).U t y)
        = (sylvesterGroup U V b).U t (blockCLM b (gridProj hA ε k) (gridProj hB ε l) y) := by
    intro t y
    simpa using blockCLM_comm_sylvesterGroup U V b (gridProj hA ε k) (gridProj hB ε l)
      hUcomm hVcomm t y
  obtain ⟨hmemW, hcommW⟩ := TauCeti.OneParameterUnitaryGroup.generator_commute
    (sylvesterGroup U V b) (blockCLM b (gridProj hA ε k) (gridProj hB ε l)) hT z
  set W := blockCLM b (gridProj hA ε k) (gridProj hB ε l) (z : lp (fun _ : ι => E) 2) with hW
  have hrewrite : blockCLM b (gridProj hA ε k) (gridProj hB ε l)
      (generator (sylvesterGroup U V b) z - (s : ℂ) • (z : lp (fun _ : ι => E) 2))
      = generator (sylvesterGroup U V b) ⟨W, hmemW⟩ - (s : ℂ) • W := by
    rw [map_sub, map_smul, hcommW]
  rw [hrewrite]
  by_cases hPz : gridProj hA ε k = 0
  · have hz0 : W = 0 := by rw [hW, blockCLM_apply, hPz]; exact blockFun_eq_zero_left b _ _
    have hn : ‖W‖ = 0 := by rw [hz0]; simp
    rw [hn, mul_zero]
    exact norm_nonneg _
  by_cases hQz : gridProj hB ε l = 0
  · have hz0 : W = 0 := by rw [hW, blockCLM_apply, hQz]; exact blockFun_eq_zero_right b _ _
    have hn : ‖W‖ = 0 := by rw [hz0]; simp
    rw [hn, mul_zero]
    exact norm_nonneg _
  obtain ⟨lam, hlamCell, hlamSpec⟩ :=
    TauCeti.LinearPMap.exists_mem_spectrum_of_specProjection_ne_zero hA _ _ hPz
  obtain ⟨alp, halpCell, halpSpec⟩ :=
    TauCeti.LinearPMap.exists_mem_spectrum_of_specProjection_ne_zero hB _ _ hQz
  have hsep : δ ≤ |lam - alp| := hgap lam hlamSpec alp halpSpec
  have hlamNear : |lam - (k : ℝ) * ε| ≤ ε :=
    TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε k hlamCell
  have halpNear : |alp - (l : ℝ) * ε| ≤ ε :=
    TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε l halpCell
  have hrep : δ - 2 * ε ≤ |(k : ℝ) * ε - (l : ℝ) * ε| := by
    have h1 := abs_sub_abs_le_abs_sub (lam - alp) (((k : ℝ) * ε) - ((l : ℝ) * ε))
    have h2 : |(lam - alp) - (((k : ℝ) * ε) - ((l : ℝ) * ε))| ≤ 2 * ε := by
      have heq : (lam - alp) - (((k : ℝ) * ε) - ((l : ℝ) * ε))
          = (lam - (k : ℝ) * ε) - (alp - (l : ℝ) * ε) := by ring
      rw [heq]
      exact (abs_sub _ _).trans (by linarith)
    linarith
  have hest := norm_sylvester_block_sub_smul_le U V b hA hB hUA hVB
    (TauCeti.LinearPMap.measurableSet_gridCell ε k)
    (TauCeti.LinearPMap.measurableSet_gridCell ε l)
    (fun t ht => TauCeti.LinearPMap.abs_le_of_mem_gridCell hε k ht) hε.le
    (fun t ht => TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε k ht)
    (fun t ht => TauCeti.LinearPMap.abs_le_of_mem_gridCell hε l ht) hε.le
    (fun t ht => TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε l ht)
    ⟨W, hmemW⟩
    (by
      change (TauCeti.LinearPMap.specProjection hA (TauCeti.LinearPMap.gridCell ε k)
        (TauCeti.LinearPMap.measurableSet_gridCell ε k)).comp (ofLp b W) = ofLp b W
      rw [hW, blockCLM_apply]
      exact comp_ofLp_blockFun_left b
        (TauCeti.LinearPMap.specProjection_comp_self hA _ _) _ _)
    (by
      change (ofLp b W).comp (TauCeti.LinearPMap.specProjection hB
        (TauCeti.LinearPMap.gridCell ε l) (TauCeti.LinearPMap.measurableSet_gridCell ε l))
        = ofLp b W
      rw [hW, blockCLM_apply]
      exact comp_ofLp_blockFun_right b _
        (TauCeti.LinearPMap.specProjection_comp_self hB _ _) _)
  have hcast : ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ) - (s : ℂ))
      = (((k : ℝ) * ε - (l : ℝ) * ε - s : ℝ) : ℂ) := by push_cast; ring
  have hscal : ‖((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ) - (s : ℂ)) • W‖
      = |(k : ℝ) * ε - (l : ℝ) * ε - s| * ‖W‖ := by
    rw [hcast, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hlow : δ - |s| - 2 * ε ≤ |(k : ℝ) * ε - (l : ℝ) * ε - s| := by
    have h := abs_sub_abs_le_abs_sub ((k : ℝ) * ε - (l : ℝ) * ε) s
    have hs' : |(k : ℝ) * ε - (l : ℝ) * ε| - |s| ≤ |(k : ℝ) * ε - (l : ℝ) * ε - s| := by
      simpa using h
    linarith
  have htri : |(k : ℝ) * ε - (l : ℝ) * ε - s| * ‖W‖
      ≤ ‖generator (sylvesterGroup U V b) ⟨W, hmemW⟩ - (s : ℂ) • W‖
        + ‖generator (sylvesterGroup U V b) ⟨W, hmemW⟩
            - ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ)) • W‖ := by
    rw [← hscal]
    have hid : ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ) - (s : ℂ)) • W
        = (generator (sylvesterGroup U V b) ⟨W, hmemW⟩ - (s : ℂ) • W)
          - (generator (sylvesterGroup U V b) ⟨W, hmemW⟩
              - ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ)) • W) := by
      module
    rw [hid]
    exact norm_sub_le _ _
  have hmul : (δ - |s| - 2 * ε) * ‖W‖ ≤ |(k : ℝ) * ε - (l : ℝ) * ε - s| * ‖W‖ :=
    mul_le_mul_of_nonneg_right hlow (norm_nonneg W)
  linarith [hest, htri, hmul]

end Gap


end HilbertSchmidt
end TauCeti
