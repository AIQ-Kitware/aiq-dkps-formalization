> **CAMPAIGN COMPLETE — 2026-08-27 (Claude Opus 5).**
>
> All nine tasks below are done.  `DavisKahan/Frontier/`, `DavisKahan/MathAhead/`,
> `DavisKahan/Experimental/MathAhead/` and `DavisKahan/Experimental/InfiniteDimensional/`
> are deleted; no production declaration lives in a `Frontier` namespace; the
> frontier audit tooling is retired.  Everything below is the handoff as written,
> kept unedited as the record of what was asked; read the Git log from `270239ac`
> for what was done, one commit per lane.

You are taking over a Davis–Kahan cleanup and promotion campaign in
aiq-dkps-formalization.

Read AGENTS.md first.

This is a mature formalization. The Davis–Kahan mathematical program is
effectively complete. The remaining work is primarily architectural cleanup,
promotion of finished mathematics out of old staging areas, removal of obsolete
experimental paths, namespace cleanup, and final polish.

The key principle is;

    preserve mathematics:
    preserve genuinely independent proof strategies:
    remove obsolete staging architecture.

Do NOT interpret this campaign as "deduplicate every Davis–Kahan theorem".

In particular, low-dependency finite-dimensional proofs, finite Sylvester
proofs, arbitrary-dimensional bounded proofs, and the full unbounded proof are
intentionally valuable independent proof roots. Do not collapse those merely
because a stronger theorem exists.

The main suspects are instead paths and namespaces labeled;

    Frontier
    MathAhead
    Experimental

because these were staging areas while the formalization was incomplete.

However, some of those files still contain finished mathematics that has not
yet been promoted. Therefore;

    DO NOT bulk-delete suspicious directories.

For each island;

    identify unique mathematical content:
    move reusable mathematics to its natural stable owner:
    move paper-facing statements to Sources/DavisKahan1970:
    delete obsolete wrappers and staging files:
    update active audits and metadata:
    then validate.

Git history is the archive. We do not need to keep dead forwarding modules just
to preserve historical names.

=======================================================================
CURRENT BASELINE
=======================================================================

The snapshot you are starting from is around commit;

    6d8abf954f72

Verify the exact current HEAD before editing because concurrent cleanup may have
landed after this handoff was written.

A substantial amount of cleanup has ALREADY happened.

Do not redo these migrations.

Completed work includes;

1. Section 4 staging removed

    DavisKahan/Frontier/Section4.lean

and;

    DavisKahan/MathAhead/Section4/

are gone.

Section 4 reusable mathematics is owned by stable Geometry / OperatorIdeal
modules, and source-facing statements live under;

    DavisKahan/Sources/DavisKahan1970/Section4*.lean

2. MathAhead Sylvester work promoted

The useful arbitrary-Hilbert-space finite-Ky-Fan Sylvester theorem was promoted
out of Experimental MathAhead.

Stable machinery now includes;

    ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFanBochner.lean

and;

    DavisKahan/InfiniteDimensional/Sylvester/GeneralSeparationKyFan.lean

The complex and real arbitrary-Hilbert-space endpoints exist in production.

Do not redo this work or merge it into the finite-dimensional Sylvester proof.

3. Spectral multiplicity promoted

Deleted;

    DavisKahan/Frontier/Core.lean
    DavisKahan/Frontier/Section3Real.lean

Generic spectral-multiplicity theory now lives in;

    ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/
        SpectralMultiplicityEquiv.lean

Real classification lives in;

    DavisKahan/SpectralTheory/Real/
        SpectralMultiplicityClassification.lean

Source-facing Theorem 3.1 multiplicity statements live in;

    DavisKahan/Sources/DavisKahan1970/
        Section3Classification.lean

4. Fixed-cosine / Proposition 3.5 foundation promoted

A large block formerly in Frontier Section 3 moved to;

    DavisKahan/Geometry/Halmos/FixedCosineSubspace.lean

Stable Proposition 3.5 geometry no longer imports Frontier for that machinery.

5. Principal-square-root / Proposition 3.3 machinery promoted

A large block moved to;

    DavisKahan/Geometry/Polar/PrincipalSquareRoot.lean

6. Proposition 3.4 / direct-rotation block machinery substantially promoted

Reusable block/reflection machinery moved out of Frontier into stable Polar
geometry, including;

    DavisKahan/Geometry/Polar/DirectRotationBlocks.lean

Source-facing Proposition 3.4 material is now under Sources.

Inspect current HEAD for exact declaration names rather than assuming this
handoff lists every promoted helper.

7. Generic trial-residual identity promoted

The generic residual identity that had lived under Frontier Section 8 was moved
to;

    DavisKahan/BoundedOperator/TrialResidual.lean

Section 1 no longer needs to reach into Frontier for that identity.

8. Section 8 central-band machinery promoted

A large set of generic central-band / perturbation declarations moved into;

    DavisKahan/SpectralTheory/CentralBand.lean

Do not move them again.

9. Generic subspace approximation-number transport promoted

The backwards dependency from generic Polar geometry into a source-facing
Davis–Kahan file was fixed by moving the generic approximation-number
subspace-transport facts into ForTauCeti.

Keep that ownership direction.

10. Free-beam application moved out of generic spectral theory

The concrete Section 9 free-beam family moved from;

    DavisKahan/SpectralTheory/FormMethod/Beam*

to;

    DavisKahan/Specialized/FreeBeam/

Generic FormMethod infrastructure remains under SpectralTheory.

This eliminated the previous generic-to-source dependency violations.

11. Yu–Wang–Samworth declaration drift was repaired.

12. Dependency-layer checker is currently clean.

At the latest review;

    scripts/check_dependency_layers.py

reported zero violations.

Do not regress that.

13. Declaration-name drift was also clean at the latest review.

=======================================================================
CAMPAIGN END STATE
=======================================================================

The desired end state is;

- no production mathematics owned by `DavisKahan/Frontier`:
- no obsolete `MathAhead` staging tree:
- no obsolete `Experimental/InfiniteDimensional` proof attempt if it carries no
  unique useful mathematics:
- no stable modules declaring generic APIs in a `Frontier` namespace:
- reusable mathematics owned by ForTauCeti, Geometry, SpectralTheory,
  BoundedOperator, InfiniteDimensional, or another natural stable layer:
- source-faithful Davis–Kahan statements owned under
  `DavisKahan/Sources/DavisKahan1970`:
- concrete applications owned under `Specialized` rather than generic theory:
- no compatibility facade kept solely because an old staging name existed:
- current audits and manifests point at canonical surviving declarations:
- dependency-layer, namespace, source-audit, and structure checks green:
- documentation and `[expose]` debt substantially reduced after structural
  ownership is stable.

There are two LARGE migrations that are intentionally OUTSIDE this campaign;

    DavisKahanExt.ClosedOperator -> LinearPMap

and the retirement of legacy rectangular / old ideal-family abstractions.

Do not start those while cleaning Frontier/MathAhead/Experimental.

They are separate later campaigns.

=======================================================================
EXECUTION DISCIPLINE
=======================================================================

You are one agent.

Do not attempt the entire roadmap in one giant diff.

Treat each numbered task below as an atomic cleanup lane.

For every lane;

1. capture a baseline before editing:
2. inspect every declaration in the suspect file(s):
3. classify declarations as;
       already duplicated by a stable theorem,
       reusable mathematics that must move,
       source-facing theorem that must move to Sources,
       implementation helper that can become private,
       obsolete wrapper that can disappear:
4. complete the entire lane:
5. update active metadata/audits:
6. build and run relevant checks:
7. commit the lane separately:
8. only then begin the next lane.

Never leave a half-migrated ownership boundary simply to get more files touched.

If a lane unexpectedly turns into substantial new mathematics, stop and report
the discrepancy rather than expanding scope indefinitely.

If you are committing, use the repository's existing commit conventions and
include your actual model/version as co-author.

=======================================================================
TASK 1 — FINISH PROPOSITION 3.2 AND THE BILATERAL-SHIFT EXAMPLE
=======================================================================

THIS IS THE IMMEDIATE NEXT TASK.

Start here.

Relevant current files include;

    DavisKahan/Frontier/Section3.lean
    DavisKahan/Frontier/Section3BilateralShift.lean
    DavisKahan/Geometry/Polar/Section3Nonacute.lean
    DavisKahan/Geometry/Polar/Section3Elementary.lean
    DavisKahan/Sources/DavisKahan1970/Section3Proposition32Crossing.lean
    DavisKahan/Sources/DavisKahan1970/Section3AcuteCounterexample.lean

Inspect exact current imports and declarations before editing.

GOAL

Get Proposition 3.2 source ownership and the bilateral-shift example completely
out of Frontier.

The generic nonacute geometry is already largely stable under;

    Geometry/Polar/Section3Nonacute

and neighboring Polar modules.

Do not reprove that theory.

A. Proposition 3.2 source statements

Identify the remaining Frontier declarations corresponding to;

- existence of a direct rotation / nonacute criterion:
- nonuniqueness in the nonacute case:
- crossed-defect / crossing-subspace conditions:
- source-facing Proposition 3.2 statements.

Move generic helper lemmas into;

    Geometry/Polar/Section3Nonacute.lean

or another already-natural Polar owner.

Move paper-facing Proposition 3.2 statements to the existing source tree.

Prefer to consolidate around;

    DavisKahan/Sources/DavisKahan1970/
        Section3Proposition32Crossing.lean

or an adjacent clearly named Section3Proposition32 module.

Do not create two competing source owners for the same printed proposition.

There is currently a library-structure complaint that
Section3Proposition32Crossing exists but is not reached correctly by the
curated source aggregate.

This lane should fix that if possible by integrating the actual source owner,
not by suppressing the checker.

B. Bilateral shift

`Frontier/Section3BilateralShift.lean` contains a genuine infinite-dimensional
example, not disposable scratch work.

Preserve the generic example.

Preferred stable owner;

    DavisKahan/Geometry/Halmos/BilateralShiftExample.lean

The stable example should own things like;

- the bilateral shift model:
- the coordinate half-spaces:
- crossed-defect computations:
- asymmetric directed-gap facts:
- reusable geometric statements independent of Davis–Kahan source numbering.

The paper-facing Remark / Proposition 3.2 counterexample belongs under;

    Sources/DavisKahan1970

`Section3AcuteCounterexample.lean` currently depends on the Frontier example.
After this lane it should depend on the stable example or source theorem instead.

Do not keep a forwarding `Frontier/Section3BilateralShift.lean`.

C. Avoid duplicate abstractions

Some old Frontier declarations now have stable equivalents.

For example inspect whether old claims such as;

    crossed_intersections_are_halmos_defects

are already represented by stable Section3Elementary / Halmos geometry.

If so, delete the wrapper rather than promoting another copy.

D. End condition

After this lane;

- `Frontier/Section3BilateralShift.lean` is gone:
- source Proposition 3.2 ownership is under Sources:
- reusable nonacute/bilateral geometry is under stable Geometry:
- `Section3AcuteCounterexample` no longer imports Frontier:
- `Section3Proposition32Crossing` is correctly integrated into the source
  aggregate:
- the corresponding portion of `Frontier/Section3.lean` is removed.

Commit this as one bounded cleanup.

=======================================================================
TASK 2 — FINISH AND DELETE FRONTIER/SECTION3.LEAN
=======================================================================

Only start this after Task 1 is fully green.

`Frontier/Section3.lean` was once more than three thousand lines and has already
shrunk substantially, to roughly sixteen hundred lines at the latest review.

Do not assume every remaining declaration deserves promotion.

Much of the deep mathematics already has stable owners.

Important existing stable modules include;

    DavisKahan/Geometry/Halmos/TwoProjectionOperatorClassification.lean
    DavisKahan/Geometry/Halmos/GenericReconstruction.lean
    DavisKahan/Geometry/Halmos/CompactClassification.lean
    DavisKahan/Geometry/Halmos/Realization.lean
    DavisKahan/Geometry/Halmos/AngleSequenceRealization.lean
    DavisKahan/Geometry/Halmos/FixedCosineSubspace.lean

and stable Polar modules added during prior cleanup.

Source-facing classification is already partly owned by;

    DavisKahan/Sources/DavisKahan1970/Section3Classification.lean

That file currently imports Frontier Section3 temporarily.

The purpose of this lane is to eliminate that temporary dependency and finally
delete;

    DavisKahan/Frontier/Section3.lean

A. Audit remaining declarations

Classify the remaining contents into;

1. obsolete source wrappers:
2. stable reusable geometry:
3. compact classification:
4. realization:
5. source-facing Theorem 3.1 / Corollary 3.1 assembly:
6. historical intermediate predicates that no longer justify a public API.

B. Classification abstractions

Pay particular attention to old structures such as;

    SameHalmosTrivialDimensions
    SameHalmosOperatorInvariant

Compare them with the already-stable;

    SameHalmosCosineBlockInvariant

and the actual reconstruction/classification engines.

Do not preserve another abstraction solely because old Frontier proofs used it.

If the stable invariant already expresses exactly what downstream mathematics
needs, remove the old wrapper structure.

If one old structure genuinely has a cleaner or stronger reusable statement,
move it to the appropriate Halmos module only after verifying that distinction.

C. Compact classification and realization

Do not duplicate;

    CompactClassification
    Realization
    AngleSequenceRealization
    GenericReconstruction

Move only source-facing assembly to;

    Sources/DavisKahan1970/Section3Classification.lean

or a neighboring source module.

The Sources module should ultimately contain the paper-shaped statements,
while stable Geometry owns the mathematical engine.

D. Old Proposition 3.1 / 3.4 wrappers

Inspect whether remaining Frontier versions are now weaker historical
intermediate theorems.

The exact source endpoints already have stable/source owners.

If a Frontier theorem is strictly weaker and has no independent downstream
value, delete it.

Do not retain aliases for historical names.

E. Source import cleanup

At the end;

    Sources/DavisKahan1970/Section3Classification.lean

must no longer import;

    DavisKahan.Frontier.Section3

F. Delete

Once no unique mathematics remains;

    DavisKahan/Frontier/Section3.lean

must be deleted.

Update Frontier aggregates and active metadata accordingly.

=======================================================================
TASK 3 — RETIRE SPECTRALMULTIPLICITYFOUNDATION IF IT IS NOW DEAD
=======================================================================

Do this adjacent to Task 2 because the concepts overlap.

Inspect;

    DavisKahan/SpectralTheory/SpectralMultiplicityFoundation.lean

At the latest review;

- `SpectralMultiplicityFoundation` appeared to have no real consumer:
- `CompactPositiveListFoundation` likewise appeared confined to that file:
- aggregate files imported the module, but downstream theorem code did not
  appear to depend on the structures:
- its module documentation already admits that the proved multiplicity
  classification has superseded the old interface:
- it contains yet another spelling of bounded-operator unitary equivalence.

Verify that on current HEAD.

If it truly has no substantive consumer;

    delete it.

Remove it from aggregates and hidden-foundation metadata.

Do not retain an abstract interface whose only reason for existence was a proof
plan that has now been replaced by an actual theorem.

If `CompactPositiveListFoundation` still has a unique useful role, move that
small piece to its natural compact-classification owner and then delete the
staging foundation file.

Do not turn this into a redesign of multiplicity theory.

=======================================================================
TASK 4 — PROMOTE CIRCLE CONTOUR AND DELETE MATHAHEAD
=======================================================================

The remaining MathAhead lane is small.

Relevant files include approximately;

    DavisKahan/MathAhead/HiddenFoundations/ContourReuseBridge.lean
    DavisKahan/Experimental/MathAhead/HiddenFoundations/
        CircleContourGeometry.lean
    DavisKahan/Frontier/CircleContour.lean

plus the corresponding MathAhead aggregates.

The actual finished circle-contour construction is primarily in Frontier.

The older MathAhead files represent an earlier proof route.

GOAL

Give the finished reusable circle-contour mathematics one stable owner, then
delete both MathAhead trees.

A. Stable owner

Inspect existing continuation / Riesz / circle spectral modules before creating
anything new.

Likely stable homes are under;

    DavisKahan/SpectralTheory/

or the existing;

    DavisKahan/InfiniteDimensional/SinTheta/Continuation/

hierarchy.

The reusable object includes things like;

- circle contour construction:
- proof that it separates the required spectra:
- winding behavior:
- quantitative spectral margin:
- resolvent estimates:
- construction of a continuation witness from a circle gap.

Do not create another `Frontier`-named API.

B. Compare the MathAhead route

Compare;

    ContourReuseBridge
    CircleContourGeometry

against the promoted stable implementation.

Preserve only genuinely absent useful mathematics.

Do not preserve an alternative obsolete construction merely because it is a
different proof route unless it provides a real low-dependency or mathematical
benefit analogous to the intentionally preserved finite Davis–Kahan proofs.

This particular MathAhead continuation lane is expected to be largely
disposable.

C. Source Section 8 Riesz-circle ownership

Inspect;

    DavisKahan/Sources/DavisKahan1970/Section8RieszCircle.lean

Some generic circle/Riesz mathematics may currently live in a source file or
still use a Frontier namespace.

Generic Riesz-circle facts belong in stable SpectralTheory.

Paper-facing aliases belong under Sources.

D. Delete MathAhead

Once all useful content has stable ownership, delete;

    DavisKahan/MathAhead/
    DavisKahan/Experimental/MathAhead/

including now-empty aggregates.

Update hidden-foundation metadata accordingly.

Git history is sufficient for the abandoned route.

=======================================================================
TASK 5 — SECTION 8 CLEANUP
=======================================================================

This is the largest remaining Frontier island.

DO NOT DO IT AS ONE COMMIT.

Split it into the following bounded lanes.

-----------------------------------------------------------------------
5A. SECTION8KREIN
-----------------------------------------------------------------------

Inspect;

    DavisKahan/Frontier/Section8Krein.lean

The important reusable endpoint is the ambient norm-preserving
self-adjoint-completion theorem.

ForTauCeti already has the lower-level normalized completion machinery in its
self-adjoint completion development.

Preferred owner for the general capstone;

    ForTauCeti/Analysis/InnerProductSpace/Polar/
        SelfAdjointCompletion.lean

or whatever exact existing stable module owns that construction at current
HEAD.

Move the genuinely generic theorem there.

Make implementation helpers private when possible.

Section 8 should consume the stable theorem.

Delete the Frontier file.

Do not duplicate the existing ForTauCeti construction.

-----------------------------------------------------------------------
5B. CONTINUATION WITNESS FROM FRONTIER/SECTION8.LEAN
-----------------------------------------------------------------------

Inspect the first part of;

    DavisKahan/Frontier/Section8.lean

The reusable layer includes things like;

    CircleContinuationData
    construction of the spectral continuation witness
    endpoint identification
    quantitative circle estimates
    canonical gap-circle construction
    construction of the common witness from off-diagonal half-gap hypotheses

This belongs in stable continuation / spectral theory.

Prefer the existing;

    DavisKahan/InfiniteDimensional/SinTheta/Continuation/

hierarchy where appropriate.

Do not move source theorem wording into the generic continuation layer.

Once the reusable continuation engine is stable, leave only source theorem
assembly for the later Section 8 source lane.

-----------------------------------------------------------------------
5C. RESIDUAL / PERTURBATION GENERIC MACHINERY
-----------------------------------------------------------------------

`CentralBand` has already been extracted.

Continue inspecting;

    DavisKahan/Frontier/Section8Perturbation.lean
    DavisKahan/Frontier/Section8Residual.lean

Move generic spectral perturbation / band / restriction / residual facts into
stable;

    SpectralTheory
    BoundedOperator
    Geometry
    ForTauCeti

as appropriate.

Do not re-move facts already promoted to;

    SpectralTheory/CentralBand.lean
    BoundedOperator/TrialResidual.lean

The final Theorem 8.2 source statements belong under;

    Sources/DavisKahan1970/Section8/

Do not leave source theorem wrappers in Frontier.

-----------------------------------------------------------------------
5D. THEOREM 8.1 PART II / PART III
-----------------------------------------------------------------------

Inspect the current files corresponding to;

    Section8PartII
    Section8PartIII
    and their real counterparts

These contain finished mathematics.

Separate;

- reusable block inequalities:
- sandwich / approximation-number facts:
- majorization facts:
- source-specific operators and theorem wording.

Generic mathematics gets stable owners.

The printed Theorem 8.1 statements move under;

    Sources/DavisKahan1970/Section8/

Do not create a second permanent theorem hierarchy just to preserve the old
PartII / PartIII Frontier file split.

-----------------------------------------------------------------------
5E. SOURCE DICTIONARY / THEOREM 8.2 / SOURCE SURFACE
-----------------------------------------------------------------------

Inspect;

    Frontier/Section8SourceDictionary.lean
    Frontier/Section8SourceTheorem82.lean
    Frontier/Section8SourceTheorem82Real.lean
    Frontier/Section8SourceSurface.lean

The source dictionary is source material and belongs under;

    Sources/DavisKahan1970/Section8/

Generic facts embedded in it should be extracted first.

The final source theorem files should move or merge into the existing Section 8
source tree.

`Section8SourceSurface` should not survive as a Frontier facade once Sources
owns the actual public paper API.

The existing low-level source surface currently contains documentation that
points to Frontier as the final facade.

Update that once the migration is complete.

=======================================================================
TASK 6 — DELETE FRONTIER
=======================================================================

After Tasks 1–5, inspect the remaining;

    DavisKahan/Frontier/

directory.

The target is ZERO unique mathematics.

If every remaining file is a forwarding/import facade;

    delete the directory.

Remove;

    DavisKahan.Frontier.All

from;

    DavisKahan.All

and any Experimental aggregate.

Do not replace it with another compatibility directory.

The fact that a historical declaration name contained `.Frontier.` is not a
reason to keep a module.

Retarget active migration metadata instead.

=======================================================================
TASK 7 — REMOVE THE FRONTIER NAMESPACE FROM STABLE MODULES
=======================================================================

Physical promotion happened faster than namespace cleanup.

Even after `DavisKahan/Frontier/` disappears, several stable modules may still
declare APIs inside;

    TauCeti.DavisKahan.Frontier

At the latest review, examples included stable modules related to;

    Geometry/Halmos/GenericRotationPredicates
    Geometry/Halmos/UnitaryEquivalence
    Geometry/Halmos/CrossedDefectGap
    SpectralTheory/CircleRieszProjection
    SpectralTheory/CircleRieszEndpoints
    Rosenblum existence / related Sylvester infrastructure

and downstream code such as tangent theorems still referred to things like;

    DavisKahan.Frontier.CrossedDefectsEquivalent

This is deferred namespace debt.

Do it AFTER file ownership is settled.

Classify each declaration;

- generic stable Davis–Kahan theorem;
      move to TauCeti.DavisKahan or its natural narrower namespace:

- paper-facing theorem;
      move to TauCeti.DavisKahan1970:

- generic TauCeti fact;
      move farther upstream if appropriate.

Update consumers.

Do not add aliases unless there is a demonstrated external compatibility need.

The goal is that a grep for active production declarations under
`DavisKahan.Frontier` returns zero.

=======================================================================
TASK 8 — AUDIT AND RETIRE EXPERIMENTAL/INFINITEDIMENSIONAL
=======================================================================

Only begin this after production Frontier ownership is gone or nearly gone.

Current suspicious tree;

    DavisKahan/Experimental/InfiniteDimensional/

At the latest review it contained roughly;

    17 Lean files
    about 4700 lines
    two actual `sorry`s

and it was not imported by production.

Its own documentation describes older infrastructure associated with the now
superseded route to the infinite-dimensional theorem.

The canonical unbounded theorem is complete.

Do NOT automatically delete the tree.

First produce a declaration-level audit.

For every substantive theorem classify it as;

A. already superseded by a production theorem at equal or stronger scope:

B. an independently useful proof route worth preserving:

C. genuinely unique mathematics missing from production:

D. abandoned/incomplete scratch work.

For B or C;

    promote to a stable owner.

For A or D;

    delete.

The finite-dimensional, finite Sylvester, arbitrary-dimensional bounded, and
full unbounded proof roots that we deliberately value live outside this
Experimental tree. Do not confuse them with this old unfinished route.

Once no useful unique content remains;

    delete Experimental/InfiniteDimensional.

Update Experimental aggregates and coverage metadata.

=======================================================================
TASK 9 — FINAL STRUCTURAL / DOCUMENTATION POLISH
=======================================================================

Do this only after the ownership moves, because deletions will reduce the
surface automatically.

At the latest review the important gate state was approximately;

    dependency layers;
        CLEAN

    declaration-name drift;
        CLEAN

    library structure;
        two violations

    docstring coverage;
        184 undocumented public declarations
        across about 29 files

    expose ratchet;
        zero blanket exposes
        about 167 per-declaration exposes
        across about 71 ForTauCeti modules

Preserve the clean gates.

-----------------------------------------------------------------------
9A. LIBRARY STRUCTURE
-----------------------------------------------------------------------

The two known violations were;

    Section3Proposition32Crossing
    Section7SwapAsymmetry

Task 1 should naturally resolve the first.

Inspect and correctly integrate;

    Section7SwapAsymmetry

into the appropriate source aggregate.

Do not suppress the checker.

The final goal;

    scripts/check_library_structure.py

green.

-----------------------------------------------------------------------
9B. DOCSTRINGS / PUBLIC API
-----------------------------------------------------------------------

Run;

    python3 scripts/check_docstring_coverage.py

Do not respond by writing meaningless comments for every declaration.

For each undocumented public declaration ask;

    should this actually be private?

If yes, make it private/local where possible.

Document only genuine public API.

Known concentrations at the last review included;

    Specialized/FreeBeam
    SpectralTheory/CentralBand
    Sources/.../Section3AcuteCounterexample

plus other files listed by the checker.

Do this in subsystem-sized commits.

-----------------------------------------------------------------------
9C. EXPOSE DEBT
-----------------------------------------------------------------------

Run;

    python3 scripts/check_expose_ratchet.py

There should be no blanket exposure.

There are still many individual `[expose]` declarations.

Review these deliberately.

Prefer;

- explicit application lemmas:
- elimination/introduction lemmas:
- public API theorems:
- reducibility-independent proofs:

over relying on definitional unfolding.

Do not simply raise the baseline.

Prioritize high-density modules such as;

    Complexification/Basic
    OperatorIdeal/Family/Basic
    AngleGeometry
    Spectral/Subspace
    LinearPMap-related modules

but follow the actual current checker output.

Some exposes have legitimate compiler-representation reasons and should stay.
Require a concrete reason rather than deleting mechanically.

-----------------------------------------------------------------------
9D. STALE SPECTRA / ARCHITECTURE PROSE
-----------------------------------------------------------------------

Production no longer imports the retired Spectra package, but old comments may
still say that Spectra is the current implementation or that proved theorems are
open.

Search present-tense production documentation.

Preserve historical attribution.

Correct false current architectural claims.

Do not rewrite dated historical reports.

-----------------------------------------------------------------------
9E. FILE CHECKLIST
-----------------------------------------------------------------------

`dev/audit/FILE-CHECKLIST.md` has intentionally not been regenerated during the
preceding small cleanup commits because its generator currently creates a large
repository-wide diff accumulated over many commits.

Once structural cleanup is stable;

    regenerate it in ONE dedicated commit.

Use its intended generator.

Do not hand-edit the generated file.

Review the large diff for obvious classification regressions before committing.

=======================================================================
OUTSIDE THIS CAMPAIGN — DO NOT START YET
=======================================================================

The following remain important, but they are separate campaigns.

1. ClosedOperator -> LinearPMap

There are still many production uses of;

    DavisKahanExt.ClosedOperator

despite `LinearPMap` being the canonical unbounded carrier.

This migration is large and should have its own roadmap.

2. Legacy rectangular / ideal-family cleanup

The old;

    RectangularSymmetricIdealFamily

and broader legacy;

    KyFanDominantIdealFamily

surface still has migration debt.

Again, separate campaign.

3. Do not deduplicate independent Davis–Kahan proof roots.

Keep;

- elementary finite eigenbasis/Parseval proof:
- finite Sylvester proof:
- arbitrary-dimensional bounded proof:
- full unbounded proof:

unless a later review establishes that two implementations are genuinely
redundant at the same abstraction/dependency layer.

=======================================================================
ACTIVE METADATA / AUDIT POLICY
=======================================================================

Whenever declarations move or disappear, inspect active current metadata,
including as applicable;

    dev/davis-kahan-1970-frontier.json
    dev/davis-kahan-1970-statement-map.json
    dev/davis-kahan-1970-formalization-result-inventory.json
    dev/davis-kahan-1970-full-source-census.json
    dev/production-namespace-migration-map.json
    dev/davis-kahan-hidden-foundations.json
    DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean

and maintained semantic-review documents.

Rules;

- active/current references must point at surviving canonical declarations:
- historical migration keys may remain as keys but should target current
  declarations:
- clearly dated historical prose can retain old paths:
- do not rewrite chronology to make the repository look cleaner:
- generated Markdown should be regenerated from its JSON source where the repo
  provides a renderer:
- do not preserve aliases solely to avoid updating metadata.

=======================================================================
VALIDATION POLICY
=======================================================================

Before each lane, capture baseline outputs.

At minimum, after a substantive lane run relevant builds such as;

    lake build DavisKahan.All
    lake build

and targeted modules.

Run relevant checks from this list;

    python3 scripts/check_dependency_layers.py
    python3 scripts/check_library_structure.py
    python3 scripts/check_namespace_policy.py
    python3 scripts/check_declaration_name_drift.py
    python3 scripts/check_davis_kahan_frontier.py
    python3 scripts/check_davis_kahan_1970_source_census.py
    python3 scripts/check_davis_kahan_1970_statement_map.py
    python3 scripts/check_davis_kahan_1970_result_inventory.py
    python3 scripts/check_docstring_coverage.py
    python3 scripts/check_expose_ratchet.py
    python3 scripts/check_experimental_coverage.py
    python3 scripts/export_for_tauceti.py --check

Also elaborate;

    DavisKahan/Sources/DavisKahan1970/Audits/
        ResultSemanticSurface.lean

when source-facing declarations move.

Do not use the ForTauCeti export write path or update the TauCeti submodule
unless explicitly asked.

Compare failures to baseline.

Do not absorb unrelated pre-existing failures into a bounded cleanup commit.

However, if the lane naturally resolves a pre-existing failure, keep the fix
and explain it.

=======================================================================
QUALITY BAR
=======================================================================

This campaign is about making ownership truthful.

A successful migration is NOT;

    old file deleted,
    same theorem copied wholesale to a new arbitrary file.

A successful migration asks;

    What is the reusable mathematical core?
    What is source-specific?
    What is only implementation plumbing?
    What already has a canonical theorem?
    What can disappear entirely?

Prefer one canonical owner.

Prefer stable theorem engines plus thin source-facing wrappers.

Prefer private helpers over accidental API growth.

Avoid compatibility facades.

Avoid aliases unless required by actual external consumers.

Avoid proof duplication.

Avoid large unrelated formatting or generated-file churn inside theorem-moving
commits.

Keep each commit reviewable.
