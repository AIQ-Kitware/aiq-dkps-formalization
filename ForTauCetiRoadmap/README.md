# `ForTauCetiRoadmap/` — roadmap drafts for Tau Ceti

[Tau Ceti](https://github.com/TauCetiProject/TauCeti) admits new mathematics against an
accepted roadmap. This directory holds our drafts, laid out the way the upstream
[`TauCetiRoadmap`](https://github.com/TauCetiProject/TauCetiRoadmap) repository lays out
its own: a family directory with an index `README.md`, and one subdirectory per roadmap
holding a definitive `README.md` and a `Suggested.lean` of representative target
signatures.

## The family

- [**Hilbert-space operator theory**](HilbertSpaceOperatorTheory/README.md) — six
  roadmaps covering bounded operators on Hilbert spaces, functional calculus and polar
  decomposition, majorization and principal angles, symmetric operator ideals, bounded
  and unbounded self-adjoint spectral theory, spectral-subspace perturbation, and the
  matrix spectral statistics that consume them.

## Reading and editing

The `README.md` of a roadmap is its specification and is definitive. `Suggested.lean`
records representative target signatures with `sorry` bodies; the bodies are the point of
the file, since `ForTauCetiRoadmap.lean` makes the directory a Lean library and so turns a
signature that no longer elaborates into a build failure. Build the library with
`lake build ForTauCetiRoadmap`; it is not a default target.

Specify mathematics intrinsically. A roadmap says what should be true and what the public
API should look like; it does not describe this repository's file layout, and identifiers
from the staged implementation belong in the short provenance section at the end of each
document, if anywhere.

## Internal notes

[`internal/`](internal/README.md) holds this repository's own bookkeeping — the
module-level topic partition and the map from topics to roadmaps. It is not part of the
family, and nothing in the roadmaps refers to it.
