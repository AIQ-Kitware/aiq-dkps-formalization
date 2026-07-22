# Targeted Davis--Kahan mathematical repair overlay

Base commit: `d5e54a708c014d97c4124036d332c6d7caa2a10e`

This overlay is the narrow replacement for the reverted bulk-facade patch.
It preserves the existing infinite-dimensional source tree and changes only
specific declarations or dependency placements justified by the mathematics.

## Mathematical changes

- Replace the nonexistent vendored import
  `Spectra.SpectralTheory.SpectralTheorem` with the actual Spectra PVM and
  bounded-calculus infrastructure.
- Move the genuine bounded complex spectral PVM/projection/subspace API to
  `Core/SpectralProjection.lean`; the contour-identification module now reuses
  that core instead of defining it again.
- Remove the full infinite continuation hierarchy from the finite
  `Generalized.lean` dependency closure. Its two complex continuation wrappers
  retain the same names and statements in `ContinuationWitnessGraph.lean`.
- Retain the valid field-generic displacement-square direct-rotation
  majorization.
- Remove the false real `pi / 3` arbitrary-UI full-displacement theorem family.
  Equal principal-angle multiplicities admit mixing competitors with smaller
  trace displacement.
- Replace that endpoint with the valid unrestricted theorem
  `N ((I - R) P_U) <= N ((I - W) P_U)` for every unitarily invariant norm.
- Restore the `DirectRotation.All` imports for `PrincipalPlanes` and
  `Majorization`.
- Make the Experimental status checker compile each registered active root
  before the full aggregate.

## Static validation

- Full Part III static contract: 39 guarded declarations match the manifest.
- No unfinished proof terms outside the 18 intentional Challenge placeholders.
- Generated aggregates are current.
- Experimental registry: 4 active roots, 0 parked.
- `git diff --check` is clean.
- Structural check 3 remains at the inherited 116 violations; checks 1, 2, 4,
  and 5 remain clean.

Lean compilation was not available in the mathematics-ahead environment. The
four registered roots remain candidate code for compiler elaboration repair.
