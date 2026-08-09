# Grounding

The bounded `tan 2Theta` result is grounded in the production `DavisKahan` tree,
not in a private finishing stack. The compatibility shim imports the promoted
theorem directly.

The canonical bounded endpoint is
`TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm` in
`DavisKahan/InfiniteDimensional/TanTwoTheta/PaperFaithfulUINorm.lean`.

Historical donor/import migrations (including Spectra retirement and earlier
Riccati path moves) remain available in Git history. They are intentionally not
repeated as a live pin table here because that table became stale after each
promotion.

`FinishTanTwoTheta/scripts/verify_grounding.py` predates the separate unbounded
research target and recursively scans every Lean file in this package. The
unbounded file intentionally remains outside the package aggregate and contains
open research proof debt, so the script's exit status is not a valid gate for the
completed bounded theorem. Validate the bounded endpoint through the production
Davis--Kahan build/gates instead.
