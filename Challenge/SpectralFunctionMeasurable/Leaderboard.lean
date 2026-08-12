/-
# Measurable spectral h-transform -- solution / dependency audit

This directory carries a `Leaderboard.lean` and **no `Conformance.lean` and no
`comparator/*.json`, deliberately**: it is a leaderboard-only dependency audit,
pending a statement/API review before the theorem is posed as a challenge.

"Unused" means unused *in code*.  `TauCeti.Matrix.measurable_specTransform` has
no call site anywhere in the repository; `Acharyya2025/SpectralMeasurability.lean`
names it only in prose, explaining that its own route avoids needing eigenvector
measurability at all.  The theorem belongs to roadmap topic **T19** (matrix
spectra and spectral measurability), and the API review should settle whether it
is the right general statement before a conformance pins it.
-/
import ForTauCeti.Analysis.Matrix.SpectralFunctionMeasurable

#print axioms TauCeti.Matrix.measurable_specTransform
