Inspect the latest commit. A large additive shared-foundation scratch campaign
has already been applied on top of `dfd9d37ebc86`.

This work is independent of the active nonacute polar/Section 3 Opus lane. Do
not edit or claim:

  DavisKahan/Experimental/MathAhead/HiddenFoundations/PolarIsometryFinal.lean
  DavisKahan/Experimental/MathAhead/HiddenFoundations/Section3Nonacute.lean

Read first:

  dev/overlays/shared-hard-foundations-dfd9d37-gpt56.md
  dev/shared-hard-foundations-candidates-dfd9d37.json
  dev/upstream-extraction/shared-hard-foundations-provenance-dfd9d37.json

Compile the modules in the order listed in the handoff, one at a time, ending
with:

  lake env lean \
    DavisKahan/Experimental/Scratch/SharedFoundations/All.lean

Work as both a mathematician and compiler agent. Repair exact API names,
coercions, associativity normal forms, scalar casts, and `letI` handling, but
preserve the mathematical architecture and the statement audits.

Important mathematical constraints:

1. Do not try to prove the existing arbitrary-gauge equality between the full
   absolute projector difference and the one-sided double-angle block. Their
   nonzero singular values have different multiplicities in the basic
   two-dimensional line model. Promote the directed-block theorem instead,
   then repair the source statement explicitly.

2. Do not prove the current Banach Theorem 5.1 from a lower norm bound alone by
   inventing a bounded inverse. A closed range in a Banach space need not be
   complemented. The scratch proof uses explicit bounded-left-inverse data.
   Audit the paper hypotheses and choose an honest repair: invertibility,
   complemented range, or a Hilbert/self-adjoint specialization.

3. Do not restore the malformed generic spectral-subspace definition. The
   genuine construction must retain bounded self-adjointness and measurable
   set data.

4. Do not remove the double-cosine denominator from the tangent Section 7
   wrapper. The compiled theorem contains it. Determine whether the source has
   an additional hypothesis or a different tangent object before changing the
   frontier.

5. Preserve Spectra attribution in the operator-modulus file and provenance
   ledger.

Recommended promotion sequence after compilation:

  a. isometric range projection and Ritz residual algebra;
  b. complex reflection-defect residual bound;
  c. old complex symmetric-ideal operator-modulus transport;
  d. exact Section 7 sine wrapper;
  e. reviewed statement repairs for directed mirror angle, Theorem 5.1,
     spectral selection, and tangent Section 7.

Report separately:

  * declarations compiled unchanged;
  * declarations needing API-only repairs;
  * mathematical statements changed after audit;
  * counterexamples or finite-dimensional multiplicity checks;
  * promoted source endpoints;
  * remaining dependencies and exact build/audit commands.
