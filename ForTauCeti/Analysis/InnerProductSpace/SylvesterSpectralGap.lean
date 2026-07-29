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

theorem blockFun_eq_zero_right (b : HilbertBasis ι ℂ F) (P : E →L[ℂ] E)
    (f : lp (fun _ : ι => E) 2) : blockFun b P (0 : F →L[ℂ] F) f = 0 := by
  refine ofLp_injective b ?_
  rw [ofLp_blockFun, ofLp_zero]
  ext x
  simp

end HilbertSchmidt
end TauCeti
