# Drafts that do not elaborate

Files here are written ahead of the mathematics and **do not compile**.  They
are kept for their statements and proof sketches only.  They are deliberately
outside `DavisKahan/` and `ForMathlib/` so that no build target and no
structural check can mistake them for library code.

## `PaperHilbertSchmidtSylvester.lean.draft`

Formerly `DavisKahan/Experimental/InfiniteDimensional/Sylvester/PaperHilbertSchmidt.lean`.

Nothing has ever imported it, so no build target ever elaborated it and its
eighteen errors went unnoticed.  It contains no `sorry`, which made it look
admission-free to a textual scan; it is in fact simply unproved.

**Adding `open MeasureTheory` removes seven of the eighteen errors.**  The
structure `PaperHilbertSchmidtSylvesterSpectralModel` *is* defined in this file
at line 45; it failed to elaborate only because its `measure` field could not
resolve `Measure`, and the "unknown identifier" reports at its use sites were
cascades from that.  An earlier revision of this note claimed the structure was
referenced but never defined.  That was wrong.

What remains after that one-line fix is genuine, and it is the hard part:

- `Spectra.HilbertSchmidtTensor.rectangularEquiv` does not exist anywhere, in
  this repository or in vendored Spectra, and never has in any commit.  It is
  the rectangular Hilbert--Schmidt Plancherel isometry that the file's own
  docstring identifies as the hard construction; the surrounding calls
  (`leftSelfAdjointOperator`, `left_right_stronglyCommute`) are written against
  an API that was planned rather than built;
- `RealComplexification.complexify` and `ENNReal.mul_lintegral` likewise do not
  exist;
- two proofs end in unsolved goals and one elaboration exceeds the heartbeat
  limit.

So recovering the file means supplying the Plancherel isometry in vendored
Spectra first.  The *statement* of the square-norm Sylvester theorem it targets
is already available in compiled form through
`DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise` and
`HilbertSchmidtDefectFirst`.
