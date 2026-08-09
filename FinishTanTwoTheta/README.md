# FinishTanTwoTheta

This package is now a compatibility/regression surface for the bounded sharp
`tan 2Theta` work that was promoted into the production `DavisKahan` tree.

The unrestricted bounded theorem is
`TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm` in
`DavisKahan/InfiniteDimensional/TanTwoTheta/PaperFaithfulUINorm.lean`. It has no
finite-carrier hypothesis, derives the quarter-acute branch from the paper-shaped
form-gap assumptions, and proves the canonical ambient tangent estimate in the
source unitary-invariant ideal family.

The local `FinishTanTwoTheta.DavisKahan.PaperFaithful` module is a shim that keeps
the former namespace available while importing the promoted theorem. The finite
alternate derivation is retained as a regression proof rather than as the canonical
endpoint.

`FinishTanTwoTheta/DavisKahan/Unbounded.lean` is a separate research target. It is
not imported by the package aggregate and must not be conflated with the completed
bounded theorem.

Build the compatibility target explicitly when changing it:

```bash
lake build FinishTanTwoTheta
```
