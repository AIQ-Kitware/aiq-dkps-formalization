# Overnight plan: finish FLAWLESS sine-theta and reorganize the library

Base commit: `0c1372acdf24d7d3d7bcc6e83e07177eaeefd0e2`.

This document is the execution prompt for the next Lean-enabled agent. The
hard pairwise-spectrum Hilbert--Schmidt Theorem 6.2 chain is compiler-accepted
and must be preserved. The remaining job is to make the complete literal-paper
surface compile, close its exactness gaps, quarantine all admission-dependent
work, and reorganize the package so an ordinary build exposes every claimed
proof.

## Non-negotiable finish line

After all file moves and import changes, the renamed successor of
`scripts/audit_full_paper_sine_theta.py` must print:

`Full paper sine-theta build and dependency audit: CLEAN`

Do not weaken the script. Update paths and declaration names only as required by
the reorganization. It must still:

1. build the complete literal Davis--Kahan 1970 sine-theta source facade;
2. run the declaration-level dependency audit;
3. reject any dependency on an admitted declaration;
4. reject proof bypasses in the source-faithful closure.

A green individual theorem is not sufficient. A green wrapper over an admitted
or unbuilt dependency is not sufficient.

## Current compiler state

The following hard front is closed and axiom-clean. Do not redesign it:

- arbitrary-disjoint-spectrum homogeneous Sylvester uniqueness;
- rectangular Stone/Borel functional-calculus intertwining;
- the Hilbert--Schmidt tensor/operator dictionary;
- pure-tensor difference-pushforward spectral measures;
- pairwise tensor spectral support;
- the reciprocal spectral-gap inverse;
- the generator bridge;
- the defect-first complex and real Theorem 6.2 endpoints.

The exact-paper audit currently fails in four paper-facing modules:

- `PaperCosineAngle.lean`;
- `PaperCommonDomainTheorems.lean`;
- `PaperSymmetric.lean`;
- `PaperSharpness.lean`.

The supplied failure log is authoritative. Repair every error serially from the
repository root. Never run concurrent Lake builds against the same build tree.

### Known failure classes

`PaperSymmetric.lean` currently has:

- subtype/domain equalities that require explicit coercion or `Subtype.ext` in
  the correct direction;
- missing `CompleteSpace` instances for closed subspaces `P.U` and `P.V`;
- scalar placement mismatches between `gap * gauge K` and
  `gauge (gap • K)`;
- block identities whose scalar must be moved through
  `paperProjectionBlock`, `paperCrossSineSum`, and `paperDiagonalPair` before
  applying Lemma 6.1 and the gauge transport results.

Do not change Proposition 6.1. Establish the exact operator identities and use
the existing homogeneity lemmas.

For the other three failing modules, capture the complete serial error output
before editing. Fix proof terms and instances, not theorem statements.

## New mathematics-ahead files in this overlay

Compile and repair these after the existing four red modules are understood:

- `PaperAngleIdentity.lean` proves equality of the literal cosine-defined angle
  with the angle reconstructed by applying `arcsin` to the positive sine
  modulus, including the real canonical-complexification form.
- `PaperCommonCore.lean` proves the graph-closed extension from a residual
  identity on a graph core to the full trial domain.
- `PaperCommonCoreTheorems.lean` supplies complex and real Theorems 6.1 and 6.2
  under the graph-core formulation.
- `PaperCorrespondenceMathAheadAudit.lean` audits those new endpoints.
- `ForMathlib/Analysis/InnerProductSpace/OrthogonalSeries.lean` is a
  Mathlib-only general orthogonal-series development.
- `DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean`
  preserves the independent orthogonal-series proof of the tensor column
  expansion. The accepted vendored proof remains canonical.

These are mathematical candidates, not compiler-accepted facts. Repair them
without weakening their statements. If the graph-core reading is not literally
needed by the paper, retain it as a useful strengthening but document that the
full common-domain theorem is the source-faithful endpoint.

## Universe polymorphism

This overlay generalizes:

- `SameApproximationSingularSequence`;
- `paperHilbertSchmidtEnergy`;
- `IsPaperHilbertSchmidt`;
- `paperHilbertSchmidtNorm`;
- their transport, composition, basis, and reconstruction results;

to independent domain and codomain universes.

This restriction was incidental. Rectangular maps between spaces in different
universes must be expressible. Fix all fallout, including paper representatives
and `result_across` statements. Do not retreat to a shared universe merely to
make a dependent file compile.

## Exact-paper completion checklist

The reorganized source root is complete only when all of the following compile
and have only `[propext, Classical.choice, Quot.sound]` dependencies:

1. normalized source unitarily invariant norms and the concrete nuclear witness;
2. literal cosine-defined directed angles;
3. exact equality with the arcsine-of-sine construction;
4. arbitrary coordinate representatives with the same full singular sequence;
5. the original sine theorem;
6. Lemma 6.1;
7. Lemma 6.2;
8. Proposition 6.1;
9. Theorem 6.1;
10. pairwise-spectrum constant-one Theorem 6.2;
11. the full common-domain appendix form;
12. the graph-core extension as a separately identified strengthening or source
    form, according to the paper text;
13. planar equality and optimality of constant one;
14. a genuine finite-multiplicity extremal construction, not only scalar
    homogeneity of an arbitrary supplied operator;
15. the printed one-gap counterexample;
16. complex and real endpoints for every source theorem that is stated over both
    scalar fields.

The current `paperFiniteMultiplicity_equality` only proves scalar homogeneity.
Either build the actual orthogonal direct-sum extremizer with all problem data
and hypotheses, or correct the public documentation if the paper does not make
the stronger claim. Do not leave the current name implying more than it proves.

## Reorganization principle

Organize stable code by mathematical role, not by development history.

`Experimental` means exactly one thing: the module contains an unresolved
admission or its advertised result transitively depends on one. It is an API
test bed. A proof intended to be valid belongs in the normal tree even while it
is red; the ordinary build must expose it to the compiler agent.

Do not use `Experimental` for:

- difficult code;
- new code;
- uncompiled candidates that are claimed as proofs;
- roadmaps or audit commands;
- alternate complete proofs;
- compatibility adapters.

## Target native repository structure

Use the following structure as the destination, adjusting file granularity when
an existing module naturally splits:

```text
DavisKahan.lean
DavisKahan/
  All.lean
  Geometry/
    Angle/
    Subspace/
    GraphSubspace/
    DirectRotation/
  SpectralTheory/
    ClosedOperator/
    Complexification/
    FunctionalCalculus/
    ReducingSubspace/
    SpectralProjection/
    Real/
  Interop/
    Spectra/
  OperatorIdeal/
    ApproximationNumbers/
    UnitarilyInvariant/
    HilbertSchmidt/
  Sylvester/
    Bounded/
    Unbounded/
    Pairwise/
    HilbertSchmidt/
  SinTheta/
    General/
    Bounded/
    Unbounded/
    Real/
    Natural/
    Symmetric/
  TanTheta/
  DoubleAngle/
  TanTwoTheta/
  DirectRotation/
  Riccati/
  BoundedOperator/
  FiniteDimensional/
  Sources/
    Davis1963/
    DavisKahan1970/
      SineTheta/
      SineTheta.lean
      PartIII.lean
      All.lean
  Specialized/
  Alternative/
```

Keep `ForMathlib/` as the repository's existing top-level Mathlib-staging
library. Keep `vendor/Spectra/` physically stable until the exact-paper build is
green, then perform provenance-aware extraction as described below.

### Literal paper layer

Move the present `Paper*.lean` source-correspondence files into:

```text
DavisKahan/Sources/DavisKahan1970/SineTheta/
  Norms.lean
  Angles.lean
  Representatives.lean
  Lemma61.lean
  Lemma62.lean
  OriginalTheorem.lean
  Theorem61.lean
  Proposition61.lean
  Theorem62.lean
  CommonDomain.lean
  CommonCore.lean
  Sharpness.lean
  Counterexample.lean
  All.lean
```

The reusable theorem engines belong under `DavisKahan/SinTheta`,
`DavisKahan/Sylvester`, and `DavisKahan/OperatorIdeal`. The source directory
should contain only exact source definitions, correspondence, and theorem
facades.

### Namespaces

First move modules with `git mv` and preserve declarations and namespaces.
Create clean public aliases. Do not combine a mass namespace rewrite with the
module migration. Rename implementation namespaces only in a later green
change.

The public source facade should provide stable names such as:

- `DavisKahan.DavisKahan1970.Theorem6_1`;
- `DavisKahan.DavisKahan1970.Proposition6_1`;
- `DavisKahan.DavisKahan1970.Theorem6_2`.

## Lake and build topology

The ordinary `lake build` must build every claimed proof and all retained
alternative proofs. It must not rely on agents knowing hidden roots.

Admission-dependent modules must be in a separate nondefault Lean library or
source root. Do not leave them inside the production library's recursive module
set if Lake would still build them by default. Preserve the logical namespace
`DavisKahan.Experimental` if useful, but configure a distinct physical source
root and nondefault target so production builds and future Lean Pool exports are
warning-free.

Required public surfaces:

- `import DavisKahan`: curated supported API plus the headline exact sine-theta
  source facade;
- `import DavisKahan.All`: every claimed admission-free production module,
  including alternatives;
- an explicit nondefault Experimental target: only admission-dependent work;
- audit modules under `dev/audit`, invoked explicitly and never imported by the
  production root.

Add structural checks:

1. every production `.lean` file is reachable from `DavisKahan.All` or the
   corresponding `ForMathlib` root;
2. no production module imports Experimental;
3. every Experimental module has an admission in its dependency closure;
4. every source facade is reachable from the curated `DavisKahan` root;
5. the full paper audit follows moved paths without dropping targets.

## Promotion out of the current mixed Experimental tree

A textual file scan is not enough because many completed declarations live in
files that also contain legacy admitted tails. For every current module:

1. compute its import closure;
2. run declaration-level dependency audits for public endpoints;
3. split mixed files into clean definitions/lemmas and admitted tails;
4. move the clean part into the production tree;
5. leave only the actual unresolved tail in Experimental;
6. ensure production imports never cross back into Experimental.

Do not solve this by copying declarations and leaving duplicates. Move or
extract them, update imports, and preserve one canonical declaration.

## Spectra and ForMathlib policy

Native development keeps `vendor/Spectra/` for now. The dependency direction is
strict:

```text
Mathlib
  -> ForMathlib
  -> Vendor/Spectra
  -> DavisKahan/Interop/Spectra
  -> DavisKahan theory
```

`ForMathlib` may never import `Vendor/Spectra`.

Classify every locally used Spectra module as:

- unchanged or lightly modified vendored Spectra representation machinery;
- a substantial general improvement now expressible with Mathlib-only imports;
- Davis--Kahan-specific infrastructure;
- thin compatibility glue;
- unused by the final closure.

When a Spectra-derived result has been genuinely generalized and rewritten so
that it is Mathlib-only and useful independently, move it to `ForMathlib` and
preserve its Spectra provenance in the file header. The vendored Spectra layer
must then import or wrap the `ForMathlib` result, never the reverse.

Davis--Kahan-specific Sylvester flow, gap, or operator-ideal material should move
into the corresponding DavisKahan package rather than remain disguised as
upstream Spectra.

Preserve vendored provenance in `vendor/Spectra/README.md`, a local modification
manifest, and file headers. Record the upstream repository, source commit,
license, whether the file was modified or locally added, and the substantive
changes.

## Lean Pool export shape

Prepare for a later self-contained export shaped as:

```text
LeanPool/DavisKahan.lean
LeanPool/DavisKahan/
  ForMathlib/
  Vendor/
    Spectra/
  Interop/
    Spectra/
  Geometry/
  SpectralTheory/
  OperatorIdeal/
  Sylvester/
  SinTheta/
  Sources/
  Alternative/
```

`LeanPool/DavisKahan/ForMathlib` is an established Lean Pool convention for
Mathlib-adjacent support. `LeanPool/DavisKahan/Vendor/Spectra` makes provenance
unambiguous. For the initial export, preserve declaration namespaces while
rewriting module paths; do not combine export relocation with a namespace
rewrite.

The export must be a minimal self-contained Mathlib-only closure. Do not copy
unused Spectra modules. Build it independently without the native repository's
`vendor/` directory. Preserve all licenses and provenance.

## Alternative proof policy

Keep an alternate proof only when it offers a genuinely different argument,
weaker dependencies, a stronger reusable intermediate theorem, pedagogical
value, or a useful upstream candidate. Canonical code must never import
`Alternative`; `DavisKahan.All` should import both canonical and retained
alternative proofs so both remain checked.

The orthogonal-series column expansion added in this overlay is the first test
case for this policy.

## Execution order

Work serially in the following order:

1. Save the current audit output and run each of the four failing modules
   directly to get complete, non-cascaded errors.
2. Repair `PaperCosineAngle`, `PaperCommonDomainTheorems`, `PaperSymmetric`, and
   `PaperSharpness` without statement changes.
3. Compile the universe-polymorphic ideal files and repair all fallout.
4. Compile the new exact-angle and graph-core files and their focused audit.
5. Compile and audit the concrete norm witness through the full source root.
6. Build the genuine finite-multiplicity equality model or correct its public
   naming/documentation based on the paper.
7. Make the pre-migration full-paper audit clean.
8. Inventory modules and admission closures; write a move manifest before any
   bulk move.
9. Reorganize in small `git mv` batches, compiling after each batch.
10. Split mixed admitted files and configure Experimental as a separate
    nondefault build target.
11. Create `DavisKahan.All`, update `DavisKahan.lean`, and make ordinary
    `lake build` cover every claimed theorem and alternative proof.
12. Update the audit script paths and declaration names only; rerun it and
    require the same semantic checks.
13. Run the complete default build, source roots, all audits, import-cycle
    checks, proof-bypass scan, and `git diff --check`.
14. Produce a correspondence matrix with no open sine-theta row.

Do not attempt all moves in one untested edit. Preserve compiler-accepted files
and use serial checkpoints.

## Reporting standard

Report separately:

- compiler-accepted facts;
- newly compiled candidates;
- structural migration progress;
- mathematical defects, if any;
- remaining obligations.

Never claim FLAWLESS sine-theta until the full renamed audit is clean and the
correspondence matrix has no open row.

## Commit message

Use this when the complete overnight work is genuinely finished:

```text
Finalize flawless Davis Kahan sine theta and promote the stable theory

Repair the complete source-faithful sine theta aggregate, certify its trusted dependency closure, and expose every claimed theorem through the default build.

Reorganize stable geometry, operator ideal, Sylvester, and source correspondence modules while quarantining only admission-dependent work in the Experimental API test bed.

Preserve Spectra provenance, extract Mathlib-only general results into ForMathlib, and retain valuable alternative proofs.

Co-authored-by: GPT-5.6 Thinking <noreply@openai.com>
```

## Continuation update at `7b9d230f50ad`

The compiler agent completed the angle, common-domain, graph-core, symmetric,
and universe-polymorphism work.  The only remaining full-paper audit failure is
the counterexample section of `PaperSharpness.lean`.  Read
`dev/paper-sharpness-frobenius-repair-note-2026-07-20.md` before continuing.
The new finite-dimensional Frobenius bridge and real-complexification reduction
in that patch are the preferred repair.  Do not revive the old direct unfolding
of the infinite square-energy definition, and do not restore the overclaiming
finite-multiplicity theorem name.
