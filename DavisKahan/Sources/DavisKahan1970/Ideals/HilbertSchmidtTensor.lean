/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

module

public import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Columns

/-!
# The `ℓ²` model of the paper Hilbert--Schmidt ideal

The Hilbert--Schmidt operators `F →L[ℂ] E` are realised as `lp (fun _ : ι => E) 2`,
the square-summable column families over a Hilbert basis of `F`.  This file is the
bridge between that model and the paper square norm of
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidt.lean`:

* finite paper square energy is equivalent to representability by a *unique* element;
* the model norm is exactly the paper square norm.

## What changed

The model used to be `vendor/Spectra`'s Hilbert tensor product
`Spectra.HilbertSchmidtTensor.Space E F`.  Mathlib supplies `lp`'s inner product and
completeness outright, so the donor closure the tensor product carried — measured at
21,581 lines — is gone. The column representation is now the accepted
`HilbertBasis.columnOperator` in `TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Columns`.
The paper-facing declarations retain their mathematical statements while naming
that canonical operator directly.

## The one design decision

`Space E F` mentions no basis; `lp (fun _ : ι => E) 2` must.  Rather than give every
declaration here a basis parameter — which every downstream consumer would inherit — the
basis is fixed internally to `hSBasis F`.  Nothing depends on *which*
basis it is, because `hilbertSchmidtEnergy_indep` says the energy does not.

`hilbertSchmidtTensor` also stops being a `Classical.choose`: the column family is
available directly, so it is that family.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace ENNReal

noncomputable section

universe vE vF

variable {E : Type vE} {F : Type vF}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The index type of the fixed Hilbert basis of `F`. -/
abbrev HSIndex (F : Type vF) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] : Type vF :=
  ↥(exists_hilbertBasis ℂ F).choose

/-- The fixed Hilbert basis of `F` in which the model is expressed. -/
abbrev hSBasis (F : Type vF) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] : HilbertBasis (HSIndex F) ℂ F :=
  (exists_hilbertBasis ℂ F).choose_spec.choose

/-- Finite paper square energy is equivalent to representation by a unique
element of the `ℓ²` model. -/
theorem approximationNumberEnergy_ne_top_iff_existsUnique_tensor (A : F →L[ℂ] E) :
    approximationNumberEnergy A ≠ ⊤ ↔
      ∃! f : lp (fun _ : HSIndex F => E) 2, (hSBasis F).columnOperator f = A := by
  rw [approximationNumberEnergy_eq_basisEnergy (hSBasis F) A,
    hilbertSchmidtBasisEnergy_eq_hilbertSchmidtEnergy]
  constructor
  · exact (hSBasis F).existsUnique_columnOperator_eq
  · rintro ⟨f, hf, -⟩
    rw [← hf]
    simp

/-- The canonical model element representing a paper Hilbert--Schmidt operator:
its column family. -/
noncomputable def hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) : lp (fun _ : HSIndex F => E) 2 :=
  ⟨fun i => A (hSBasis F i),
    (A.hilbertSchmidtEnergy_ne_top_iff_memℓp (hSBasis F)).mp (by
      simpa only [approximationNumberEnergy_eq_basisEnergy (hSBasis F) A,
        hilbertSchmidtBasisEnergy_eq_hilbertSchmidtEnergy] using hA)⟩

/-- The tensor model's operator, unfolded.  This is the bridge between the tensor presentation of a
Hilbert--Schmidt map and its operator form. -/
@[simp]
theorem toOperator_hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    (hSBasis F).columnOperator (hilbertSchmidtTensor A hA) = A :=
  (hSBasis F).columnOperator_mk A _

/-- The model norm is exactly the paper square norm. -/
theorem norm_hilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    ‖hilbertSchmidtTensor A hA‖ = ContinuousLinearMap.hilbertSchmidtNorm A := by
  rw [← (hSBasis F).hilbertSchmidtNorm_columnOperator (hilbertSchmidtTensor A hA),
    toOperator_hilbertSchmidtTensor]

/-- Every element of the model represents a paper Hilbert--Schmidt operator. -/
theorem approximationNumberEnergy_ne_top_toOperator (f : lp (fun _ : HSIndex F => E) 2) :
    approximationNumberEnergy ((hSBasis F).columnOperator f) ≠ ⊤ := by
  rw [approximationNumberEnergy_eq_basisEnergy (hSBasis F),
    hilbertSchmidtBasisEnergy_eq_hilbertSchmidtEnergy]
  simp

/-- The paper square norm of the represented operator is exactly the model norm. -/
theorem hilbertSchmidtNorm_toOperator (f : lp (fun _ : HSIndex F => E) 2) :
    ContinuousLinearMap.hilbertSchmidtNorm ((hSBasis F).columnOperator f) = ‖f‖ := by
  exact (hSBasis F).hilbertSchmidtNorm_columnOperator f

end

end ExactSinTheta
end DavisKahan
end TauCeti
