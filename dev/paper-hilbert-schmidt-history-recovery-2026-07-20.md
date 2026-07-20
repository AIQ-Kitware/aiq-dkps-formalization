# Paper Hilbert--Schmidt Sylvester history recovery

## Result

No completed joint-PVM proof was lost from Git history.  The public theorem
statements are now restored in
`DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean`, using
the completed defect-first and pairwise spectral-gap proof chain.

## Search performed

The search covered:

- all refs in each of the eight source archives available from July 19--20;
- unreachable and dangling Git objects in every archived object database;
- every patch and ZIP overlay available in the session;
- exact-string history for
  `PaperHilbertSchmidtSylvesterSpectralModel`, `rectangularEquiv`,
  `leftSelfAdjointOperator`, and `closedSylvester_jointMultiplier`;
- renamed and moved versions of the file from its original Experimental path
  through the Sources reorganization.

The speculative identifiers first appeared in commit `b303831` and were never
implemented elsewhere.  No archived object database contains an unreachable
implementation.  The only overlay containing them reproduces the same
math-ahead file.

## What was and was not present

The structure `PaperHilbertSchmidtSylvesterSpectralModel` was present in the
original file.  Its initial elaboration failure was caused by the missing
`MeasureTheory` namespace opening, and downstream unknown-identifier reports
were cascading errors.

The constructor was not implemented.  In particular, the following planned
Spectra API never existed in any searched revision:

- `Spectra.HilbertSchmidtTensor.rectangularEquiv`;
- `leftSelfAdjointOperator` and `rightSelfAdjointOperator`;
- `left_right_stronglyCommute`;
- `closedSylvester_jointMultiplier`;
- `jointBornMeasure_supported_on_spectra` in the proposed form.

The underlying square-norm Sylvester theorem was later completed by a different
and stronger repository-supported route:

1. represent a Hilbert--Schmidt defect by its completed Hilbert tensor;
2. derive a vector spectral gap for the left-minus-right tensor flow from the
   pairwise separation of the original spectra;
3. invert the generator on that vector by bounded functional calculus;
4. transport the generator equation back to a closed Sylvester equation;
5. use bounded homogeneous uniqueness to identify the supplied solution.

## Repair

The restored production module provides the three intended public declarations:

- `paperHilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap`;
- `paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap`;
- `paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap`.

The norm theorems expose the completed direct proof under their original public
names.  The extended-energy theorem is derived without assuming finite defect
energy: the infinite case is immediate, while the finite case follows by
squaring the sharp norm estimate and converting the finite extended energies.

The abandoned Lean draft is removed.  This note preserves the provenance and
the distinction between the unrealized joint-PVM design and the completed
Hilbert-tensor proof.

## Acceptance commands

```bash
lake env lean DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean
python3 scripts/generate_all_aggregates.py --check
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/check_library_structure.py
```
