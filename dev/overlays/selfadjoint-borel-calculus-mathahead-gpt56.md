# Self-adjoint Borel-calculus mathematics-ahead handoff

## Purpose

This additive batch fills the foundation that the first Sylvester mathematics
pass incorrectly treated as a collection of routine helper lemmas.  The key
finding is that the required real-line bounded Borel calculus already exists in
the vendored Spectra library.  It is not the Cayley-transform calculus for a
unitary operator:

```lean
Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
```

integrates a bounded measurable symbol `g : ℝ → ℂ` against the real spectral
measure of any `OneParameterUnitaryGroup`.  For a bounded self-adjoint map `A`,
the required group is

```lean
genToGroup (boundedSelfAdjointOperator A hA).selfAdjoint
```

Consequently the missing campaign is a bridge and finite-step algebra layer,
not a new construction of scalar spectral measures, bounded forms, and Riesz
representation from first principles.

## Files

```text
DavisKahan/Experimental/MathAhead/Sylvester/SelfAdjointBorelCalculus.lean
DavisKahan/Experimental/MathAhead/Sylvester/FiniteStepCalculus.lean
DavisKahan/Experimental/MathAhead/Sylvester/OrthogonalIdempotentExp.lean
DavisKahan/Experimental/MathAhead/Sylvester/FiniteBlockReconstruction.lean
DavisKahan/Experimental/MathAhead/Sylvester/All.lean
dev/davis-kahan-borel-mathahead-candidates.json
```

The batch is intentionally independent of the existing
`Experimental/InfiniteDimensional/Sylvester/FourierSemigroup.lean`; that file is
currently the consumer being repaired.  Merge declarations only after each new
file elaborates.

## Mathematical architecture

1. Wrap Spectra's bounded Borel calculus for the full-domain self-adjoint
   realization of a bounded symmetric continuous linear map.
2. Zero-extend real symbols off the actual real spectrum.  A bound on the
   spectrum then becomes a global bound, exactly matching Spectra's API.
3. Use support of every scalar Born measure in the real spectrum to prove
   congruence of calculi for symbols agreeing on the spectrum.
4. Derive the sharp operator norm estimate from
   `norm_spectralCalculus_le`.
5. Expand finite measurable step symbols by additivity and homogeneity of the
   calculus, obtaining a finite sum of spectral projections.
6. Prove support congruence, orthogonality, sum-to-identity, and block-selection
   identities for those projections.
7. Prove the exponential of a finite orthogonal idempotent decomposition by
   expanding the Banach-algebra exponential power series coefficientwise.
8. Prove the finite Sylvester reconstruction as a pure rectangular-block
   Fourier calculation, parameterized by the scalar reciprocal identity.

The compact-cover topology construction remains in the compiler agent's
campaign.  It should feed its cells and representatives into the generic
finite-step layer here.

## Important signature correction

The requested signature

```lean
boundedSelfAdjointBorelCalculus A hA f hf
```

for an arbitrary measurable `f : ℝ → ℝ` is not mathematically valid.  A
measurable function need not be bounded on a compact set.  A bounded operator
calculus therefore cannot be defined from measurability alone without an
arbitrary fallback convention.

This batch uses the honest signature

```lean
boundedSelfAdjointBorelCalculus A hA f hf hfb
```

where

```lean
hfb : BoundedOnSpectrum A f
```

Every actual consumer has such a proof:

* the identity is bounded by `‖A‖` on `realSpectrum A`;
* a finite step symbol is bounded by the finite sum of absolute representative
  values;
* differences are bounded by the cell-radius estimate.

Do not remove this hypothesis.  Update the consumer calls instead.

## Compile order

```bash
lake env lean \
  DavisKahan/Experimental/MathAhead/Sylvester/SelfAdjointBorelCalculus.lean

lake env lean \
  DavisKahan/Experimental/MathAhead/Sylvester/FiniteStepCalculus.lean

lake env lean \
  DavisKahan/Experimental/MathAhead/Sylvester/OrthogonalIdempotentExp.lean

lake env lean \
  DavisKahan/Experimental/MathAhead/Sylvester/FiniteBlockReconstruction.lean

lake env lean \
  DavisKahan/Experimental/MathAhead/Sylvester/All.lean
```

Then import the compiled declarations into
`Experimental/InfiniteDimensional/Sylvester/FourierSemigroup.lean` and remove
or replace its phantom helper declarations.

## Suggested consumer rewrites

### `FiniteSpectralStep.sum_projection_eq_one`

Replace the custom finite-PVM-union proof with

```lean
spectralProjection_finset_sum_eq_id
  A hA S.cell S.measurable_cell S.pairwise_disjoint S.covers_spectrum
```

### `FiniteSpectralStep.norm_operator_sub_le`

Use

```lean
boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator
```

to identify the step operator, then

```lean
boundedSelfAdjointBorelCalculus_norm_sub_le
```

with explicit bounded-on-spectrum proofs for the chosen step symbol and the
identity.

### `unitaryGroup_finiteSpectralStep`

Use

```lean
unitaryGroup_finiteDiagonal
```

or directly `exp_finset_orthogonal_idempotents`, with projection idempotence,
pairwise orthogonality, and the finite sum-to-identity theorem.

### `finiteSpectralStep_reconstruction`

The complete algebraic calculation is

```lean
finiteDiagonal_sylvester_reconstruction
```

Instantiate it with the two spectral projection families, representative
functions, the proved scalar kernel, and the separation inequality.  This
avoids repeating a large nested-sum/integral calculation in the consumer.

## Lemma ledger: confirmed in the vendored source

The following names were inspected directly in the pinned repository.
Signatures below omit routine implicit typeclass arguments.

```lean
Spectra.YosidaHille.genToGroup :
  IsSelfAdjoint A → OneParameterUnitaryGroup

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus :
  (U : OneParameterUnitaryGroup) →
  (g : ℝ → ℂ) → Measurable g →
  (∃ C, ∀ x, ‖g x‖ ≤ C) → H →L[ℂ] H

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_add :
  Φ (g₁ + g₂) = Φ g₁ + Φ g₂

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_smul :
  Φ (c * g) = c • Φ g

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_sub :
  Φ (g₁ - g₂) = Φ g₁ - Φ g₂

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_mul :
  Φ h * Φ g = Φ (h * g)

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_congr :
  g₁ = g₂ → Φ g₁ = Φ g₂

Spectra.QuantumMechanics.SpectralTheory.spectralCalculus_congr_ae_forall :
  (∀ ξ, g₁ =ᵐ[borelMeasure U ξ] g₂) → Φ g₁ = Φ g₂

Spectra.QuantumMechanics.SpectralTheory.norm_spectralCalculus_le :
  (∀ x, ‖g x‖ ≤ C) → ‖Φ g‖ ≤ C

Spectra.QuantumMechanics.SpectralTheory.spectralProjection :
  (B : Set ℝ) → MeasurableSet B → H →L[ℂ] H

Spectra.QuantumMechanics.BornRule.Observable.bornMeasure_support_subset_spectrum :
  (bornMeasure A.spectralPVM ξ).support ⊆
    Spectra.Resolvent.spectrum A.toLinearPMap

Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_apply_eq_spectralCalculus_of_bounded
Spectra.QuantumMechanics.SpectralTheory.mem_pmapDomain_id_of_mem_generator
Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_id_eq_generator
Spectra.QuantumMechanics.SpectralTheory.pmapOfPVM_congr_ae

ForMathlib.DavisKahan.Experimental.SpectraBridge.boundedSelfAdjointOperator
ForMathlib.DavisKahan.Experimental.SpectraBridge.boundedSelfAdjointOperator_domain
ForMathlib.DavisKahanExt.boundedSelfAdjointSpectralPVM
ForMathlib.DavisKahanExt.boundedSelfAdjointSpectralProjection

ProjValMeasure.proj_inter
ProjValMeasure.proj_union
ProjValMeasure.proj_congr
ProjValMeasure.proj_univ
ProjValMeasure.proj_empty
ProjValMeasure.proj_idem
```

## Lemma ledger: standard Mathlib names likely needing spelling repair

The mathematics uses only standard finite sums, Banach-algebra exponentials,
and Bochner integrals.  The compiler agent should verify these exact spellings:

```lean
NormedSpace.exp_eq_tsum
NormedSpace.summable_exp
Complex.exp_eq_tsum_div
Complex.summable_pow_div_factorial
tsum_zero_add'
tsum_smul
tsum_finsetSum
integral_finset_sum
integral_smul_const
ContinuousLinearMap.comp_finset_sum
ContinuousLinearMap.finset_sum_comp
ContinuousLinearMap.comp_smul
ContinuousLinearMap.smul_comp
ContinuousLinearMap.comp_sub
ContinuousLinearMap.sub_comp
ContinuousLinearMap.comp_assoc
```

Potentially version-sensitive names:

```lean
ae_mem_support
isClosed_spectrum_of_isSelfAdjoint
spectrum.norm_le_norm_of_mem
mem_pmapDomain_of_bounded
LinearPMap.ext_iff
Fin.exists_fin_succ
Set.PairwiseDisjoint.elim
Measurable.dite
```

No mathematical result depends on those exact spellings.

## Confidence by declaration group

* `boundedSelfAdjointGroup`: complete; direct wrapper.
* `boundedSelfAdjointBorelCalculusC`: complete; direct wrapper.
* real-spectrum bridge and measurability: probably complete; namespace spelling
  may need repair.
* support and spectrum-congruence results: complete argument; Born-measure
  namespace simplification may need repair.
* norm and norm-difference bounds: complete argument.
* identity calculus: complete mathematical argument through the existing
  unbounded calculus/generator bridge; highest elaboration risk in this file.
* finite-step additivity: complete induction; dependent proof arguments and
  `Fin` decomposition are likely repair points.
* PVM support congruence/orthogonality/sum/selection: complete arguments.
* finite orthogonal-idempotent exponential: complete power-series argument;
  interchange spelling is likely repair work.
* finite block reconstruction: complete algebraic/Fourier argument; finite
  integral-sum interchange spelling is likely repair work.

## Divergences and scope

1. The calculus is complex-Hilbert-space only because the production Spectra
   PVM is complex.  Real results still require complexification and descent.
2. The real calculus requires `BoundedOnSpectrum`; this is stronger in syntax
   but exactly the missing mathematical condition in the originally requested
   signature.
3. The finite reconstruction theorem is parameterized by an arbitrary
   integrable reciprocal kernel.  Instantiate it with the already compiled
   Haagerup--Zsidó kernel; no new normalization is introduced here.
4. This batch does not duplicate the compact-spectrum finite-cover topology
   work, which the compiler agent explicitly owns.
5. This batch does not duplicate the already written dominated-convergence
   passage in `FourierSemigroup.lean`.  It supplies the missing finite-step
   foundation on which that passage depends.
6. The general separated estimate remains `π/(2d)`.  Nothing here restores the
   false constant-one claim for arbitrary two-sided spectral separation.

## Promotion criterion

Promote the wrapper and finite-step files only after they compile independently
and their declarations have no admission dependencies.  The existing supported
build should not import this aggregate until the repaired Sylvester theorem is
ready for promotion.
