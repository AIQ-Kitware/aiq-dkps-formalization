You are taking over the next Jon-owned campaign in the Davis--Kahan repo. You
are expected to do both compiler work and substantial mathematics.

Read first:

  AGENTS.md
  dev/LANES.md
  docs/planning/tauceti-adaptation-and-spectra-extraction.md
  docs/planning/opus-next-polar-extraction-campaign.md
  dev/upstream-extraction/polar-decomposition-provenance-dfd9d37.json

The end state is pure Tau Ceti/Mathlib. Spectra is a temporary donor and
provenance reference, not a permanent dependency. Candidate code must not
import Spectra.

Your primary campaign is:

  1. extract the bounded polar-decomposition core from the pinned Spectra
     sources into a standalone TauCetiCandidates library with complete
     attribution;
  2. prove the reusable final-space, adjoint/equivariance, and regularized
     polar-factor results that Spectra does not currently provide;
  3. use that foundation to close the blocked nonacute Section 3 direct
     rotation campaign;
  4. migrate the relevant DKPS consumers away from direct Spectra polar
     imports.

Do not merely produce an audit. Write and compile the mathematics.

Critical mathematical warning: do not assume that the absolute value of a
bounded operator has a bounded inverse on its support. Nonclosed range makes
that false. Prefer regularized polar factors or another route valid when zero
is an accumulation point.

Audit the current IsPaperDirectRotation structure before proving the converse.
Its diagonal fields are real-part inequalities, not bundled positive-operator
conditions. If the current statement is too weak, demonstrate the gap and
repair the canonical statement explicitly.

Do not work on spectral multiplicity, free-beam Sobolev realization,
general Schatten theory, directRotation_sq, or directRotation_minimal during
this campaign unless all planned milestones are complete and you claim a new
lane.

Claim the lane under the human owner `jon`, not the model name. Pull and inspect
the latest ledger before editing because Edward may be running a parallel
Fable lane.

Use small commits and keep the relevant builds green after every stage. Record
exact source paths, commit, original author, license, renamed declarations,
and semantic changes in the provenance ledger.
