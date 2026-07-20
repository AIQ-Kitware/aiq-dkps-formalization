# Drafts that do not elaborate

Files here are written ahead of the mathematics and **do not compile**.  They
are kept for their statements and proof sketches only.  They are deliberately
outside `DavisKahan/` and `ForMathlib/` so that no build target and no
structural check can mistake them for library code.

## `PaperHilbertSchmidtSylvester.lean.draft`

Formerly `DavisKahan/Experimental/InfiniteDimensional/Sylvester/PaperHilbertSchmidt.lean`.

Nothing has ever imported it, so no build target ever elaborated it and its
eighteen errors went unnoticed.  It contains no `sorry`, which made it look
admission-free to a textual scan; it is in fact simply unproved.  The gaps are
real mathematics, not import drift:

- `PaperHilbertSchmidtSylvesterSpectralModel` is referenced but never defined —
  it is the rectangular Hilbert--Schmidt Plancherel theorem for the commuting
  left and right spectral measures, the hard construction the file's own
  docstring isolates;
- `Spectra.HilbertSchmidtTensor.rectangularEquiv` and
  `RealComplexification.complexify` do not exist;
- two proofs end in unsolved goals and one elaboration exceeds the heartbeat
  limit.

Recovering it means proving the Plancherel model first.  The *statement* of the
square-norm Sylvester theorem it targets is already available in compiled form
through `DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise`
and `HilbertSchmidtDefectFirst`.
