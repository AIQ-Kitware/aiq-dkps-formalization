/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
import Spectra.Spaces.Tensor.HilbertSchmidt

/-!
# The Spectra tensor model of the paper Hilbert--Schmidt ideal

`vendor/Spectra` realizes the Hilbert--Schmidt operators `F →L[ℂ] E` as the Hilbert tensor
product `Spectra.HilbertSchmidtTensor.Space E F`.  This file is the bridge between that
model and the paper square norm of
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean`:

* finite paper square energy is equivalent to representability by a *unique* tensor;
* the tensor norm is exactly the paper square norm.

## Why this is a separate module

These four declarations are the only place the paper Hilbert--Schmidt development mentions
Spectra's tensor space.  They used to live at the end of
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtBasis.lean`, which forced that
whole module — basis independence, the cutoff comparison, the identification of the
column energy with the singular-value energy — onto `vendor/Spectra` even though none of
it needs Spectra.  Since `dev/tauceti/dependency-layer-allowlist.json` records the removal
of Spectra from the normal build as the migration target, the interop half is isolated
here, where rule 7 of `scripts/check_dependency_layers.py` exempts it by design, and the
mathematics stays Spectra-free upstream.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe vE vF

variable {E : Type vE} {F : Type vF}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Finite paper square energy is equivalent to representation by a unique
Hilbert tensor. -/
theorem isPaperHilbertSchmidt_iff_existsUnique_tensor
    (A : F →L[ℂ] E) :
    IsPaperHilbertSchmidt A ↔
      ∃! z : Spectra.HilbertSchmidtTensor.Space E F,
        Spectra.HilbertSchmidtTensor.toOperator z = A := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ F
  rw [isPaperHilbertSchmidt_iff_summable_basis b A]
  exact
    (Spectra.HilbertSchmidtTensor.existsUnique_tensor_iff_summable_columns b A).symm

/-- The canonical tensor representing a paper Hilbert--Schmidt operator. -/
noncomputable def paperHilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    Spectra.HilbertSchmidtTensor.Space E F :=
  Classical.choose ((isPaperHilbertSchmidt_iff_existsUnique_tensor A).1 hA)

@[simp]
theorem toOperator_paperHilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    Spectra.HilbertSchmidtTensor.toOperator
      (paperHilbertSchmidtTensor A hA) = A :=
  (Classical.choose_spec
    ((isPaperHilbertSchmidt_iff_existsUnique_tensor A).1 hA)).1

/-- The tensor norm is exactly the paper square norm. -/
theorem norm_paperHilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    ‖paperHilbertSchmidtTensor A hA‖ = paperHilbertSchmidtNorm A := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ F
  have hsq := Spectra.HilbertSchmidtTensor.norm_sq_eq_tsum_column_norm_sq
    b (paperHilbertSchmidtTensor A hA)
  rw [toOperator_paperHilbertSchmidtTensor] at hsq
  rw [paperHilbertSchmidtNorm_eq_sqrt_tsum_basis b A hA, ← hsq,
    Real.sqrt_sq (norm_nonneg _)]

/-- Every Hilbert tensor represents a paper Hilbert--Schmidt operator. -/
theorem isPaperHilbertSchmidt_toOperator
    (z : Spectra.HilbertSchmidtTensor.Space E F) :
    IsPaperHilbertSchmidt (Spectra.HilbertSchmidtTensor.toOperator z) := by
  rw [isPaperHilbertSchmidt_iff_existsUnique_tensor]
  refine ⟨z, rfl, ?_⟩
  intro w hw
  exact Spectra.HilbertSchmidtTensor.toOperator_injective hw

/-- The paper square norm of the represented operator is exactly the Hilbert
tensor norm. -/
theorem paperHilbertSchmidtNorm_toOperator
    (z : Spectra.HilbertSchmidtTensor.Space E F) :
    paperHilbertSchmidtNorm (Spectra.HilbertSchmidtTensor.toOperator z) = ‖z‖ := by
  let hZ := isPaperHilbertSchmidt_toOperator z
  have hcanon := norm_paperHilbertSchmidtTensor
    (Spectra.HilbertSchmidtTensor.toOperator z) hZ
  have heq : paperHilbertSchmidtTensor
      (Spectra.HilbertSchmidtTensor.toOperator z) hZ = z := by
    apply Spectra.HilbertSchmidtTensor.toOperator_injective
    rw [toOperator_paperHilbertSchmidtTensor]
  rw [heq] at hcanon
  exact hcanon.symm

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
