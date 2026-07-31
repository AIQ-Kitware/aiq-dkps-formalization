# Review — the `ApproximationNumber/` cluster

**Status: COMPLETE for the 10 Lean files.** Written 2026-07-31 by
`edward (aiq-gpu-docs)`, lane `COORD` item (b), closing the largest of the four
clusters in the audit tail.

These ten were the biggest unreviewed block left on the checklist — eleven files
in one directory, in topic **T09**, which at 21 modules is the largest topic on
the submission ladder. That combination is the shape worth reading as a group:
the same directory hid two independently-drafted duplicates earlier the same day,
in `EnergyComparison.lean`.

Reviewed:

- [x] `CompactHilbert.lean` (178 lines, 3 declarations)
- [x] `Core.lean` (686, 46)
- [x] `DiagonalSequence.lean` (227, 14)
- [x] `FinitePVMSelection.lean` (215, 3)
- [x] `FiniteValueFibers.lean` (162, 14)
- [x] `FiniteValueSeparation.lean` (125, 2)
- [x] `GramBandPolar.lean` (243, 4)
- [x] `GramSpectralRank.lean` (508, 15)
- [x] `LeadingCutoff.lean` (95, 4)
- [x] `MinMaxReal.lean` (305, 10)

**What the review consisted of, stated so the tick means something.** Structural
measurement across all ten (declaration density, longest proof, primed names,
escapes, TODOs); a cross-file duplicate scan; verification that every
backticked cross-reference in every docstring resolves to something that exists;
and a full read of `Core.lean` and `MinMaxReal.lean`, the anchor and the one
carrying the longest proof. The other eight were read at the level of docstring,
signatures and proof shape, not line by line.

## Finding AN-1 — a docstring apologising for debt that has been paid `{lane:COORD}`

`Core.lean` carried a `## Namespace` section reading, in the present tense:

> The enclosing namespace is still `TauCeti.DavisKahan.Experimental.ExactSinTheta`,
> which is a paper's name and a staging word inside a library staged for Tau Ceti.
> That is **recorded debt, not a decision** […] It is not renamed in the same
> change as the move because the name has 359 references across four libraries.

**The file declares `TauCeti.ApproximationNumber`.** The rename happened; the
paragraph explaining why it had not survived it.

This is worth separating from an ordinary stale comment. A reviewer's question
about this library is *"does the submission still carry the paper's staging
vocabulary?"* — it is finding AT-1's whole subject — and this module answered
**yes** in a section headed `## Namespace`, while its own first line of code
answered no. **A paragraph apologising for a defect that no longer exists is
worse than no paragraph**, because it is written in the voice of someone who
checked.

Fixed here, and the same sentence pattern was measured repo-wide before fixing
rather than after: **exactly 2 modules assert in the present tense a namespace
they do not have.** The other is
`Challenge/MathlibPending/ApproximationNumbers/Leaderboard.lean`, and it is
**correct** — it says two statements are still in the paper library's namespace,
and they are. So this was a single instance, not a pattern, and no gate is
warranted.

## Finding AN-2 — a pointer to a module this library does not have `{lane:COORD}`

The sentence beside it read *"The public aggregate and downstream ideal-family
construction remain in `ApproximationNumbers`."* There is no
`ApproximationNumbers` in `ForTauCeti`. The plural name belongs to
`DavisKahan/OperatorIdeal/ApproximationNumbers/`, a **different library**, and
the downstream construction a reader of this module actually wants is
`ForTauCeti.Analysis.OperatorIdeal.Family`.

Both AN-1 and AN-2 are the residue of a **moved** module — `Core.lean`'s own
provenance block says *"Extraction class: moved, not restated"* — and they are
the specific failure mode of that class: the mathematics transplants cleanly and
the prose keeps describing where it used to live. Worth naming, because eight of
the ten files here are `moved`.

## No finding

`MinMaxReal.lean` is the strongest file in the group and is the counter-example
to AN-1/AN-2 from the same extraction class. Its provenance block is specific
rather than formulaic — it records that **317 lines came off on the way in**,
being a `private` copy of thirty transport lemmas that duplicated the public API
the module already imported, and it says which namespace became which and why the
`_real` suffix survives. Every one of the five names in its `## Main results` list
resolves, as does `kyFanGauge_add_le_of_exists_finiteRestriction`, the theorem it
cites as its consumer. Its longest proof is 129 lines, the longest in the group,
and it is the real Courant–Fischer localization — earned length, not accumulated.

`GramSpectralRank.lean` (508 lines, 15 declarations, longest proof 76) and
`GramBandPolar.lean` (243, 4, 64) are the other two with real proof weight and
are sound; the ratio in `GramBandPolar` is four declarations to 243 lines, which
in most files would be a finding and here is not — the four are one construction
and its three properties.

`FiniteValueFibers.lean` is 14 declarations in 162 lines with no proof over 9
lines, which is what a well-factored support file looks like.

**Mechanically clean across all ten**: no `sorry`, no `TODO`, no primed name
(*"a prime hides a duplicate from every name-based check"* has been this
session's most repeated finding, and this cluster has none), and
`audit_scan --dup --mirrors` reports **no near-duplicate statement anywhere in
the cluster** — neither internally nor against the rest of the repository.

**Recording "no finding" deliberately**, per the precedent in
`review-audit-tail.md`: eight of these ten would otherwise be indistinguishable
from eight files nobody opened.
