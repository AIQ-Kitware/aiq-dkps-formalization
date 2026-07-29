You are taking over as the primary mathematics-and-compiler agent for the
Davis--Kahan 1970 formalization.

The first milestone is a complete standalone `DavisKahan` package formalizing
the full 1970 paper, except that Proposition 4.4 and any other false source
claim must be represented by a machine-checked counterexample and an audited
corrected replacement rather than restored as theorems.

Do not begin major Tau Ceti integration or repository restructuring. During
this milestone the intended production dependency graph is:

  Mathlib -> vendor/Spectra -> DavisKahan

`external/Spectra` and `external/TauCeti` are read-only reference checkouts.
The ordinary build must not depend on them. Tau Ceti migration is the second
milestone, after the paper is recursively grounded. Generic work should remain
portable and attributed, but it must land as compiled DavisKahan progress now.

Before editing, read:

  AGENTS.md
  dev/LANES.md
  dev/lean-proof-engineering-lessons.md
  docs/planning/tauceti-adaptation-and-spectra-extraction.md
  docs/planning/opus-next-paper-completion-campaign.md

Then:

1. Inspect the latest commit and working tree.
2. Run the relevant baseline builds and frontier/status scripts.
3. Confirm that Jon's nonacute polar/Section 3 lane remains reserved and does
   not overlap Edward's resumed Fable claims. Refresh the lane claim before the
   first edit.
4. Work as both mathematician and compiler agent. Do not stop after an audit or
   a proof sketch.

Primary campaign
================

Complete the nonacute polar/direct-rotation foundation and promote Davis--Kahan
Proposition 3.2.

Read and work through:

  DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIsometryFinal.lean
  DavisKahan/Experimental/MathAhead/HiddenFoundations/Section3Nonacute.lean
  DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIntertwining.lean
  DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean
  DavisKahan/Experimental/Frontier/Section3.lean
  vendor/Spectra/Spectra/QuantumMechanics/Channels/PolarDecomp.lean
  vendor/Spectra/Spectra/QuantumMechanics/Channels/TraceClass/PartialIsometry.lean

Close these primary leaves:

  adjoint_polarIsometry
  canonicalPolarFactor_sourceCompression_nonnegative
  canonicalPolarFactor_crossed_blocks_general
  crossedDefectEquivOfPaperDirectRotation

Then ground and promote the downstream chain:

  nonacuteDirectRotation_isPaperDirectRotation
  exists_paperDirectRotation_of_crossedDefectsEquivalent
  crossedDefectsEquivalent_of_exists_paperDirectRotation
  proposition3_2_completed
  proposition3_2_parameterization_completed

Mathematical cautions
=====================

Do not assume that the positive part of a general bounded operator has a
bounded inverse on the closure of its range. Zero may be an accumulation point
of the positive spectrum. Avoid an unrestricted `positiveSupportInverse`.

Use an honest route such as polar-decomposition uniqueness, support-projection
identities, a theorem special to the canonical projection intertwiner, or
regularization by `(|T| + epsilon I)^{-1}` with a justified limiting argument.

For `adjoint_polarIsometry`, try to prove that the adjoint polar factor has the
correct support projections and factorization for the adjoint operator, then
invoke a general uniqueness theorem.

For source-compression positivity, exploit the canonical block structure and
commutation with the source projection. Prove self-adjointness of the compressed
operator when required; do not infer positivity from an unrelated norm bound.

For the crossed-block identity, prefer a reflection/adjoint operator identity
over an unmotivated coordinate calculation.

Audit `IsPaperDirectRotation` before proving the converse defect-equivalence
map. If its fields do not imply the two missing crossed-defect membership
facts, produce a concrete finite-dimensional counterexample or a precise
logical gap, strengthen the predicate minimally, and repair the source-facing
statements. Never hide a missing hypothesis.

Dependency and provenance policy
================================

Use `vendor/Spectra` freely when it materially helps close the paper. Do not
start a bulk extraction or Tau Ceti port. Import narrowly.

When adapting Spectra mathematics, preserve exact provenance:

  * source repository and commit;
  * source file and declaration names;
  * original authorship and license;
  * whether the local result is copied, ported, generalized, specialized, or
    substantially redesigned;
  * semantic changes and the likely future Tau Ceti destination.

General helper theorems should live at the lowest cycle-safe layer. If a theorem
naturally extends Spectra's current polar API, a focused managed-vendor patch is
acceptable. If it is DavisKahan-owned mathematics merely stated over Spectra
objects, keep it in `ForMathlib` or the DavisKahan experimental foundation.

Scope limits
============

Do not take on Tau Ceti integration, broad namespace migration, free-beam
analysis, spectral multiplicity, general Schatten theory, or the direct
rotation minimality theorem during this campaign unless Proposition 3.2 is
already complete and the follow-up is truly small.

Completion and reporting
========================

Compile after coherent steps. Promote final proofs out of staging modules into
the source-facing frontier. Run targeted axiom audits, the relevant aggregate
builds, and the frontier/source-census checker. Update `dev/LANES.md` and the
status report before stopping.

Report separately:

  * mathematical results proved;
  * statements corrected or refuted;
  * Spectra declarations adapted and their provenance;
  * compiler/API repairs;
  * remaining blockers and exact dependencies;
  * commands and audit results.
