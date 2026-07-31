# Review — the audit tail

**Status: the 22 files this was reopened for are COMPLETE.** The checklist now
reads **1144/1199, not 1175/1175**, and that is not a regression: 25 files landed
or moved on 2026-07-31 — the `Schatten`/`EnergyComparison` split, `ENNRealLiminf`,
the `FinishTanTwoTheta` promotions into `Sources/DavisKahan1970/`, and this
document — and `audit_checklist.py` correctly lists a new file as unreviewed.
**An audit of a moving tree is never "done"; it is "current as of".**

**Status: COMPLETE for the 13 Lean files.** Written 2026-07-31 by
`edward (aiq-gpu-docs)`, lane `AUDIT`, closing the 22 entries
`jon (toothbrush)` enumerated when they reopened the row.

These files did not form a group; they are what was left when every group was
otherwise done, which is why they are reviewed together here rather than in a
`review-<group>.md`. Three of the findings below are visible **only** because
the files were read side by side, which is the argument for finishing a file
pass rather than declaring it substantially complete.

Reviewed:

- [x] `DavisKahan/BoundedOperator/Compat.lean`
- [x] `DavisKahan/Experimental/InfiniteDimensional/Sylvester/OrderedEngineLegacy.lean`
- [x] `DavisKahan/Experimental/InfiniteDimensional/Sylvester/CutoffInterface.lean`
- [x] `DavisKahan/SinTheta/Unbounded/Gauge.lean`
- [x] `DavisKahan/SinTheta/Unbounded/OpNorm.lean`
- [x] `DavisKahan/SinTheta/Natural/Generalized.lean`
- [x] `DavisKahan/Sylvester/Spectrum.lean`
- [x] `DavisKahan/Sylvester/FiniteStepCalculus.lean`
- [x] `DavisKahan/TanTheta/Spectrum.lean`
- [x] `DavisKahan/TanTheta/UnboundedSpectrum.lean`
- [x] `ForTauCeti/Analysis/Normed/Operator/FiniteRankCompact.lean`
- [x] `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/DiagonalExample.lean`
- [x] `ForTauCeti/Analysis/InnerProductSpace/ReducedExtension.lean`

## Finding AT-1 — 54 production modules carry the staging namespace `{lane:RUB-NS-PAPER}`

**`DavisKahan/SinTheta/`, `DavisKahan/Sylvester/` and `DavisKahan/TanTheta/` are
production paths, and 54 of their modules open
`namespace TauCeti.DavisKahan.Experimental.ExactSinTheta`** — a paper's name and
a staging word, in the tree that is not staging.

Three of the thirteen files here do it (`SinTheta/Unbounded/{Gauge,OpNorm}.lean`,
`SinTheta/Natural/Generalized.lean`) and reading them together is what made the
count worth taking; each file alone reads as consistent with its neighbours.

This is `{lane:RUB-NS-PAPER}`'s subject and that lane is closed, so the finding
is that **its measurement was of a different set**: the closed lane renamed
declarations, and the namespace on these 54 survived it. A reviewer reads
`Experimental` in a path called `Sylvester/` as a warning about the mathematics,
and it is not one.

**Related and worse, from lane `{lane:DK-EXPCOVER}` the same day:** the structure
`ClosedOperator` is *declared* in `TauCeti.DavisKahanExt` from
`DavisKahan/SpectralTheory/ClosedOperator/Basic.lean`. A namespace on a theorem
is a naming defect; a namespace on a structure is one every projection inherits.

## Finding AT-2 — a legacy leaf that nothing uses and nothing compiles `{lane:DK-EXPCOVER}`

`Experimental/InfiniteDimensional/Sylvester/OrderedEngineLegacy.lean` says in its
own docstring that **"the canonical engine does not import or use this leaf"**,
and it is right: nothing imports it. It also does not compile — it reaches
`Core/Unbounded.lean`, which projects eight fields off `ClosedOperator` that
exist nowhere.

**A file that is unused, unbuilt and self-described as superseded is three
independent reasons to retire it, and it has survived all three** because no
gate looked: it is outside `defaultTargets` and outside the experimental root's
closure. `scripts/check_experimental_coverage.py` now names it.

## Finding AT-3 — a docstring promising a dependency that was deleted `{lane:COORD}`

`Experimental/InfiniteDimensional/Sylvester/CutoffInterface.lean` ends its
docstring with **"The production implementation comes from the vendored Spectra
calculus instead."**

`vendor/Spectra` does not exist. It was retired and removed by lane
`{lane:SPECTRA-FORK}`, and this sentence now points a reader at a directory that
is not there, to explain why the file they are reading is the *non*-production
route. The file is the only implementation there is.

## Finding AT-4 — a module named for one that no longer exists `{lane:DK-NAME}`

`SinTheta/Natural/Generalized.lean` opens: *"The compiler-accepted `NaturalGenuine`
module contains the canonical isometric specialization. This separate leaf adds
the lower-frame result without modifying that verified module."*

**There is no `NaturalGenuine` module.** `SinTheta/Natural/` holds `All`,
`Bounded`, `Examples`, `GapConvenience`, `Generalized`, `Real`, `Reducing` and
`SpectralSubspace`. `Natural/Real.lean` cites it too, so the dangling reference
is in two files.

Two further things are wrong with that sentence and are worth separating.
`Genuine` is a name asserting its own quality — the checklist names that pattern
explicitly, alongside `PaperFaithful` and `LiteratureComplete`. And **"without
modifying that verified module" is a rationale for a file's existence that is
about the author's caution rather than the mathematics**: the split is not a
mathematical boundary, and a reviewer inheriting this cannot tell what belongs on
which side of it.

## Finding AT-5 — a bundled/raw twin in each of two files `{lane:RUB-DUP-STMT}`

`SinTheta/Unbounded/Gauge.lean` proves `sinTheta_unbounded_gauge` and
`linearPMap_sinTheta_unbounded_gauge`; `SinTheta/Unbounded/OpNorm.lean` proves
`sinTheta_unbounded_opNorm` and `linearPMap_sinTheta_unbounded_opNorm`. The
`linearPMap_` member of each pair is the same theorem for Mathlib's raw
`LinearPMap` rather than the bundled `ClosedOperator`.

**This is not flagged as duplication — it is flagged as a pattern that should be
one adapter and is currently four theorems.** `ForTauCeti/Analysis/-
InnerProductSpace/LinearPMap/{Sylvester,GraphCore}.lean` already describe
themselves as bridging *"bundled DKPS `ClosedOperator` to raw Mathlib
`LinearPMap`"*. If that bridge is complete, each `linearPMap_` twin is a
corollary; if it is not, the four twins are the evidence of what it still needs.
Either way the answer is one place, not two files each with a pair.

## Finding AT-6 — six gates exit 0 on a finding, and the suite is run without `--check` `{lane:COORD}`

**`check_conflict_markers.py:93` is `return 1 if args.check else 0`.** So does
`check_lane_format.py`, `check_expose_ratchet.py`, `check_submission_prose.py`,
`check_namespace_policy.py` and `check_private_shadows_public.py` — six of the
twenty `check_*.py`. The other fourteen return non-zero on a finding regardless.

The split is defensible as report-versus-enforce. **What is not defensible is
that it is undocumented, inconsistent, and that nothing runs the suite knowing
which is which** — there is no runner script; every caller writes its own loop.

**This is evidenced from the reviewer's own session rather than argued.** Twice
on 2026-07-31 a regression passed a green run of the whole suite because the loop
tested exit codes: `check_tauceti_readiness` went from *over 1000 lines: 0* to
*1* when a module I had written crossed the limit, and `check_submission_prose`
picked up a lane id from a merged docstring. Both printed the finding and both
exited 0. **A gate that reports a defect and exits 0 is indistinguishable from a
gate that found nothing, to everything except a human reading the output.**

`check_conflict_markers.py`'s own docstring is the sharpest illustration: *"There
is no baseline. A committed marker is never acceptable and never becomes
technical debt to be paid down later."* That is a strict policy, and the script
implementing it exits 0 when it finds one.

**The fix is small and belongs to whoever owns the tooling:** either make the six
strict by default and add `--report` for the soft form, or add one runner that
passes `--check` to all of them. The first is better — the default should be the
safe one.

## No finding

`Sylvester/Spectrum.lean` (573 lines, 12 declarations), `Sylvester/-
FiniteStepCalculus.lean` (418, 17), `TanTheta/Spectrum.lean` (281, 4) and
`TanTheta/UnboundedSpectrum.lean` (215, 5) are `sorry`-free, in the right place,
and their longest proofs are well short of the group's worst — the four longest
proofs in `DavisKahan/Sylvester/` are all in `Unbounded/Neumann.lean` and
`ShiftedInverse.lean`, which are already reviewed and already carry findings.

`ForTauCeti/Analysis/Normed/Operator/FiniteRankCompact.lean` (2 theorems),
`…/ApproximationNumber/DiagonalExample.lean` (1) and
`…/InnerProductSpace/ReducedExtension.lean` (2) are small, single-purpose and
consumed. **`ReducedExtension.lean` is named in `{lane:FTC-UNIVPAIR}`'s finding**
— two `private` wrappers elsewhere restate its `re_inner_reducedExtension_self`
in different presentations — and that finding stands as written there; the module
itself is not at fault and needs no change.

`dev/audit/measure-expose-conversion.md` and `dev/audit/measure-expose-rfl.md`
are honest reports of what was measured on 2026-07-30 and are **superseded, not
wrong** — recorded here rather than as a finding because a dated measurement
that says what it measured is doing its job. Both state *"70 of 167 modules"*
and the first adds *"the tree is unchanged and `check_expose_ratchet.py` reads
70 of 167"*; today it reads **0 of 187**, the conversion having landed. **If
either document is ever cited as current state, that is the defect** — the
numbers are a snapshot and both say so in their opening lines.

`scripts/lane.py`, `scripts/tests/test_check_lane_graph_state.py` and
`scripts/tests/test_audit_scan_defn.py` are sound; both test files pass.

**Recording "no finding" deliberately.** Nine of thirteen files here would
otherwise be indistinguishable from nine files nobody opened, which is the state
this lane was reopened to fix.
