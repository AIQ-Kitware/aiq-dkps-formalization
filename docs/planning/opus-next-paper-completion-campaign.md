# Next Opus campaign: complete nonacute direct rotations inside DavisKahan

**Baseline:** `dfd9d37ebc86`  
**Owner:** Jon's next Opus session  
**Dependency policy:** current DavisKahan package with `vendor/Spectra`  
**Primary source target:** Davis--Kahan 1970, Section 3

## Mission

Act as both a mathematics agent and a compiler agent. Close the remaining
nonacute direct-rotation foundation and promote it into the source-facing
Section 3 endpoints. Do this in the existing repository architecture.

This is not a Tau Ceti migration campaign. It is allowed to use and extend the
managed Spectra vendor when that is the shortest honest route to the paper.
Generic results should be portable and attributed, but the deliverable is a
compiled DavisKahan theorem chain.

## Why this campaign is next

The repository has already completed much of the surrounding geometry:

- crossed-defect spaces and their quarter-turn construction;
- the canonical intertwiner and its kernel;
- the regular/crossed-defect orthogonal splitting;
- initial and final projection identities for the canonical polar factor;
- the nonacute unitary assembly once the remaining polar facts are available;
- the generic Halmos cosine/sine operators and Pythagorean identity.

The remaining leaves block Proposition 3.2 and feed later direct-rotation
classification statements. They are a concentrated foundational campaign with
large source-level payoff.

## Authoritative files and declarations

Read these first:

```text
AGENTS.md
dev/LANES.md
dev/lean-proof-engineering-lessons.md
DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIsometryFinal.lean
DavisKahan/Experimental/MathAhead/HiddenFoundations/Section3Nonacute.lean
DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIntertwining.lean
DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean
DavisKahan/Experimental/Frontier/Section3.lean
vendor/Spectra/Spectra/QuantumMechanics/Channels/PolarDecomp.lean
vendor/Spectra/Spectra/QuantumMechanics/Channels/TraceClass/PartialIsometry.lean
```

Primary open declarations:

```lean
adjoint_polarIsometry
canonicalPolarFactor_sourceCompression_nonnegative
canonicalPolarFactor_crossed_blocks_general
crossedDefectEquivOfPaperDirectRotation
```

The downstream goal is to ground and promote:

```lean
nonacuteDirectRotation_isPaperDirectRotation
exists_paperDirectRotation_of_crossedDefectsEquivalent
crossedDefectsEquivalent_of_exists_paperDirectRotation
proposition3_2_completed
proposition3_2_parameterization_completed
```

Also inspect the acute `DirectRotation.lean` polar leaves. Reuse any general
foundation produced here, but do not expand the campaign into
`directRotation_sq` or `directRotation_minimal` until Proposition 3.2 is green.

## Mathematical constraints

### Do not assume a bounded inverse on the support

For a general bounded operator, the positive spectrum may accumulate at zero.
The restriction of `|T|` to the closure of its range need not have a bounded
inverse. Do not introduce a globally bounded `positiveSupportInverse` without a
closed-range hypothesis.

Viable routes include:

- uniqueness of polar decomposition;
- spectral regularization such as
  `T (|T| + ε I)⁻¹` followed by strong or pointwise convergence;
- direct identities special to the canonical projection intertwiner;
- support-projection arguments that avoid an inverse;
- a bounded transform defined only when the required range is closed, with an
  honest additional hypothesis if that is sufficient for a particular lemma.

### `adjoint_polarIsometry`

Try to characterize `star (polarIsometry T)` as the polar factor of `star T`.
A promising route is to prove that it has the correct initial/final support
projections and factors `star T` with the appropriate positive part, then use a
uniqueness theorem. Add the general uniqueness lemma at the lowest cycle-safe
layer. If the proof substantially adapts Spectra's polar construction, record
that relationship in the provenance ledger.

### Source-compression positivity

The target is positivity of

```text
P_U * polarFactor * P_U
```

for the canonical projection intertwiner. Prefer a theorem special to this
intertwiner over an invalid general support inverse. Investigate:

- commutation of the positive part with `P_U`;
- the block formula for the canonical intertwiner;
- regularized polar factors whose source diagonal compression is visibly
  positive;
- a direct identity with the positive square root of a projection compression,
  stated carefully on the ambient space or source subspace.

Prove self-adjointness of the compression if it is needed to convert a real-part
inequality into operator positivity.

### Crossed-block relation

Derive the skew-adjoint crossed-block identity from a canonical reflection or
adjoint relation. Do not prove it by coordinates unless the operator route is
blocked and the coordinate decomposition is already available and auditable.

### Converse defect equivalence

Audit whether `IsPaperDirectRotation` contains enough information to force a
paper direct rotation to map the crossed defects to each other. First attempt a
proof from:

- unitarity;
- projection intertwining;
- positivity of both diagonal compressions;
- the crossed-block relation.

If the current predicate is insufficient, do not conceal the gap. Produce a
finite-dimensional counterexample or a precise independence argument, then
strengthen the predicate or source-facing statement minimally and repair its
consumers.

## Working policy

1. Claim or refresh the lane in `dev/LANES.md` before editing.
2. Start from a green build and record the exact commands.
3. Search the pinned Mathlib and vendored Spectra sources for exact APIs before
   inventing theorem names.
4. Put general helper results at the lowest import layer that avoids cycles.
5. Use `vendor/Spectra` when the theorem belongs naturally to its current polar
   API; otherwise keep the result in the DavisKahan tree.
6. Preserve original Spectra headers and add declaration-level provenance for
   adapted mathematics.
7. Compile after every coherent lemma, not only at the end.
8. Promote completed proofs into the source-facing frontier rather than leaving
   the final result only in `MathAhead` or `Scratch`.
9. Run targeted axiom checks on all newly grounded headline declarations.
10. Update the source census/frontier report and lane ledger before stopping.

## Scope control

Do not perform these tasks during this campaign:

- required Tau Ceti integration;
- bulk Spectra extraction;
- namespace restructuring;
- spectral-multiplicity classification;
- free-beam Sobolev realization;
- general Schatten or trace-class construction;
- direct-rotation square/minimality unless Proposition 3.2 is already complete
  and the remaining work is a small direct corollary.

If the polar campaign reaches a genuine missing-foundation wall, document the
minimal missing theorem, prove as much dependency-closed infrastructure as
possible, and ask for reassignment rather than wandering into another large
campaign.

## Completion criteria

The campaign is complete when:

- the four primary open declarations compile without proof escapes;
- the nonacute direct rotation satisfies the audited paper predicate;
- both directions of Proposition 3.2 compile;
- the parameterization theorem is compiled if its current statement remains
  correct;
- source-facing Section 3 endpoints are promoted and recursively grounded;
- targeted axiom audits show only accepted foundational axioms;
- provenance entries cover every adapted Spectra declaration;
- `DavisKahan.All` and the relevant experimental/frontier aggregate build green;
- no Tau Ceti dependency or broad restructuring was introduced.

## Follow-on work

After Proposition 3.2 is complete, rerun the full frontier checker. Choose the
next unclaimed source-critical campaign from the updated report. Likely options
are the remaining Section 3 classification endpoints, Section 9 analytic
realization, or ideal-valued sine/double-angle leaves, but the ledger and new
recursive grounding report decide the order.
