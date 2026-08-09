# Developer notes — `dev/`

Long-running engineering memory and status instrumentation for the AIQ DKPS Lean
formalization. Anything that **isn't** the formalization itself, the comparator
challenge package (`Challenge/`, `comparator/`), or paper-facing planning
(`docs/`) lives here. The contents are deliberately agent-readable: an agent
arriving cold should be able to read this folder, understand the project's
pattern of past mistakes, and take fewer of them.

## If you are starting work right now

Read `../AGENTS.md` first, then route by task instead of reading `dev/` linearly:

| File | What it answers |
|---|---|
| [`SEARCH.md`](SEARCH.md) | How to search engineering memory by symptom or subsystem. |
| [`tauceti/README.md`](tauceti/README.md) | Current Tau Ceti engineering authorities and the boundary between maintained status and migration history. |
| [`davis-kahan-1970-full-source-census.md`](davis-kahan-1970-full-source-census.md) and [`davis-kahan-1970-frontier-status.md`](davis-kahan-1970-frontier-status.md) | Current Davis--Kahan source coverage and the remaining proof frontier. |

`LANES.md` is only a retirement notice for the former multi-agent lane system.

The governing policy is in [`../AGENTS.md`](../AGENTS.md), not here. It defines
the dual-track split (Tau Ceti extraction primary, Davis--Kahan source fidelity
maintenance), the dependency firewall, and the completion-claim discipline.

## Layout

```text
dev/
  LANES.md                          # Retirement notice for the former lane system
  SEARCH.md                         # How to search engineering memory
  lean-proof-engineering-lessons.md # Recurring Lean elaboration/API/parser traps
  mathlib-proof-polishing.md        # Reference: "folding" proofs to Mathlib style
  mathlib-quality-adapter.md        # Reference: adapting local API to reviewer standard
  external-lean-references.md       # Registry of external Lean repos consulted
  external-literature-references.md # External *mathematics* we cite or must import; source errata

  tauceti/                    # Tau Ceti engineering records and generated status
  journals/                   # Postmortems of bugs that took real effort to diagnose
  benchmark-candidates/       # Hard questions distilled from real formalization mistakes
  overlays/                   # Promotion manifests for the surviving Scratch/** sketches
  alternates/                 # Non-building Lean files kept for proof-strategy comparison
  upstream-extraction/        # Provenance JSON for extracted material
  retired-full-part-iii-ambient-route-2026-07-21/   # Compressed archive of a retired route
```

Alongside those, `dev/` holds the Davis--Kahan source-fidelity ledgers:
the maintained census/frontier data and generated views, plus historical design
records that explain how difficult gaps were closed.  Dated completion plans are
not current queues. Several `.json` files are read or written by
`scripts/check_*.py` — do not hand-edit one without running its checker.

### Where a new note goes

- A *current status claim* belongs in the source-owning README or a generated/checkable status artifact, not in `LANES.md`.
- A *postmortem* of a bug that took effort → `journals/`.
- A *transferable trap* another model would also fall into → `benchmark-candidates/`.
- *Tau Ceti engineering history or generated status* -> `tauceti/`; current package policy -> `../ForTauCeti/README.md`.
- *Paper-facing scope and roadmap* → `../docs/planning/`.
- Anything that is only useful with the user in the loop → agent auto-memory,
  not a file here.

Resist adding a dated one-off note. The tree accumulated about ninety of them
between 2026-07-18 and 07-24, they went stale within days, and reading them as
current cost a later session two reversed lanes. They now sit in
[`topurge/`](topurge/MANIFEST.md), which **stays** — jon decided on 2026-07-30
not to delete it. Treat those files as a labelled archive, not as pending work. If a note is worth
writing, it is worth putting in the file that already owns the topic.

## `dev/benchmark-candidates/`

A corpus of self-contained Lean 4 / Mathlib / comparator questions distilled
from real mistakes made while building and upstreaming this project. Each
question captures a *pre-error* setup — the context an agent had at the moment
of the mistake — so a different model facing the same setup can be tested for
the same failure mode.

This domain has an unusually rich supply of these: a Lean proof either checks or
it doesn't, the comparator either matches or it doesn't, and `#print axioms`
gives a crisp pass/fail. That makes the traps **mechanically checkable**, which
is exactly what a benchmark needs.

- **Read** these before a task that resembles one catalogued here (slimming a
  conformance, restating a theorem, choosing a leaf, minimizing imports,
  matching a comparator export). The "Why this was easy to miss" section names
  the cognitive trap so you can recognise it in your own reasoning.
- **Write** here when you cause, watch, or resolve a mistake whose root cause is
  a transferable invariant. The bar is: *another model in the same situation
  could plausibly make the same mistake without this question written down.*

[`benchmark-candidates/README.md`](benchmark-candidates/README.md) is required
reading before adding a question: write the failure evidence first, then distil;
pick the right Level A/B/C prompt; tag by *failure-class invariant*, not by
surface API. Spin off a standalone `topic-YYYY-MM-DD.md` file (linked from
`index.md`) only when a question is substantial and focused, or when parallel
agents are editing `lean-questions.md` concurrently.

## `dev/journals/`

Postmortems of bugs that took real effort to diagnose. Newest-first, written in
the moment so the symptom language matches what a future debugger would search
for.

- **Read** here first when you hit a confusing symptom in the same area as a
  past entry. The grep target is the *symptom* — "statement do not match",
  "motive is not type correct", "failed to synthesize" — written the way you'd
  search for it from *inside* the bug, before you know the technically-correct
  vocabulary.
- **Write** here after a fix that took effort. Skip the narrative; the canonical
  shape is **Symptom / What it was NOT / Root cause / Fix / Takeaway**.

## `dev/overlays/`

Promotion manifests for the proof sketches under
`DavisKahan/Experimental/Scratch/**`. Per `AGENTS.md`, a scratch file is **not
required to build** — the task is to promote the sketch into its source-facing
home module and fix it *there*. The manifest states what each declaration
proves, where it should land, and the likely elaboration seams.

Only the manifests whose sketches are still unpromoted remain here; the delivery
receipts for overlays already applied were purged. Two of these are load-bearing
beyond documentation: `pending-mathahead-rebased-53297a4-gpt56.manifest.txt` is
checked by `scripts/check_davis_kahan_rebased_mathahead.py` — which treats a
sketch **promoted** out of `Experimental/` as success and fails only when a
module is nowhere, so an entry may record a rename with `<scratch> -> <target>` — and
`lemma63-promotion-scratch-7f9f562-gpt56.md` is cited from two Lean sources.

## Quality bar

Don't record trivia. These subtrees are curated; an over-long file is a worse
signal than a short one, because future readers won't believe the important
entries hidden between filler. The strongest entries are the ones where the code
*built green and looked correct* but a downstream check — comparator,
`#print axioms`, kernel — still rejected it. Those are the non-obvious,
transferable traps. If unsure whether something belongs, write it in scratch
first; if a week later you still think the lesson is durable, move it in.

---

## Retired tooling — the Spectra lifecycle scripts

**Sixteen scripts were deleted on 2026-07-29** when the Spectra dependency was
retired. They are listed here because a reader who finds them cited in an older
document should know they are gone on purpose, not missing by accident:

`apply_spectra_submodule_overlay.py`, `bootstrap_spectra_submodule.sh`,
`restore_spectra_reference_submodule.sh`, `finalize_vendored_spectra_snapshot.sh`,
`spectra_compatibility_patch.py`, `spectra_import_smoke.sh`,
`verify_spectra_reference.py`, `verify_vendored_spectra.py`,
`check_spectra_vendor_authorship.py`, `enable_spectra_lake_dependency.py`,
`disable_spectra_lake_dependency.py`, `spectra_port_surface.py`,
`check_spectra_parent_only_bridge.sh`, `ExportSpectraDeclClosure.lean`,
`ExportSpectraUsage.lean`, `remove_redundant_mathlib_vendor_snapshots.py`.

Three had stopped telling the truth rather than failing, which is the worse
mode: `verify_spectra_reference.py` printed the *superproject* commit as the
submodule's pin (it reported this repository's own HEAD as Spectra's SHA),
`verify_vendored_spectra.py` diffed `vendor/Spectra`, a tree that no longer
exists, and `check_spectra_vendor_authorship.py` refused to classify anything
because its `external/Spectra` reference checkout was gone. One was actively
dangerous: `apply_spectra_submodule_overlay.py` regenerates the managed
`Spectra collaboration policy` block in `AGENTS.md`, so running it would have
reinstated the retired policy over the notice that replaced it.

**One is kept and still has a job:** `scripts/check_spectra_namespace.py`. The
rule it enforces — never declare into `namespace Spectra` — *outlives* the
dependency. With the imports gone, a DKPS theorem parked in the donor namespace
is no longer distinguishable from donor material by anything, so the attribution
ledger would silently credit Spectra for our work. `namespace SpectraBridge` is
the correct pattern and is not a violation.

Attribution survives all of this: `retired/Spectra.UPSTREAM.md`,
`tauceti/spectra-provenance-map.md`, `tauceti/spectra-vendor-authorship-baseline.json`,
and the provenance headers in nine Lean modules.

---

## Build cache on slow filesystems

If your checkout sits on a network or shared-folder filesystem (on the AIVM
setup the repo is a **virtiofs** mount from the host, `/mnt/aivm-persistent`),
`.lake` is the wrong thing to leave there. Lake stats every one of ~128k build
artifacts on each invocation, and that metadata traffic — not compilation — is
what the shared filesystem taxes.

Measured 2026-07-29 on this VM, same tree, same 9269-job **fully cached** build:

| `.lake` on | no-op `lake build` |
| --- | --- |
| virtiofs (repo default) | 47.9s |
| ext4 (VM-local disk) | 10.5s |

**4.6x**, paid back on every invocation including the ones that compile nothing.

Fix — move the cache to VM-local storage and symlink it back:

```sh
cp -a .lake ~/.lake-cache/<repo>/.lake     # verify: du -sh, and find -type f | wc -l
mv .lake .lake.old && ln -s ~/.lake-cache/<repo>/.lake .lake
lake build                                 # must report all jobs cached, not rebuilt
rm -rf .lake.old                           # only after the line above
```

Copy-verify-swap rather than `mv`, because a partially-moved cache costs a
~90-minute cold rebuild. Check `findmnt -T . -o FSTYPE` first; if it already
says `ext4`, there is nothing to do.

**Two traps.**

- `.gitignore` listed `.lake/` **with a trailing slash, which matches
  directories only.** The moment `.lake` becomes a symlink it stops being
  ignored and shows up as untracked — a machine-specific absolute path one
  `git add -A` away from being committed. Both spellings are now in
  `.gitignore`; leave them.
- The VM-local disk is *not* the host-persistent mount. This cache does not
  survive a VM rebuild, which is correct — it is regenerable — but do not put
  anything there that isn't.

---

## Davis--Kahan 1970 full source census

The full-paper theorem-by-theorem source ledger:

- `davis-kahan-1970-full-source-census.json` — authoritative structured source ledger;
- `davis-kahan-1970-full-source-census.md` — generated human-readable view;
- `davis-kahan-1970-frontier.json` / `davis-kahan-1970-frontier-status.md` —
  maintained proof-frontier graph and generated status;
- `davis-kahan-1970-private-source-workflow.md` — rules for using the local
  transcription without redistributing it.

Do not revive dated `*-completion-plan*`, `*-handoff*`, or
`missing-statements-*` files as current work queues.  Their useful history is in
Git; the census and frontier own present-tense status.

Validate with:

```bash
python3 scripts/render_davis_kahan_1970_source_census.py --check
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/probe_census_declarations.py           # do the names resolve?
```

The first two validate *structure* — generated view in sync, fields present,
statuses in the allowed set. Neither can tell you the declarations named by
`lean_declarations` exist; the census reported `CLEAN (48 items)` throughout the
period when **none of its 87 declarations resolved**. The probe compiles a
`#check` of every fully-qualified name against `DavisKahan.All` and is the only
one of the three that answers that question.

The fast checker prints the current source-obligation summary and explicitly says
when Lean/Lake declaration resolution was unavailable. When Lean is available,
`probe_census_declarations.py --verify` checks the recorded verification state
against declarations reachable from the production aggregate. Use `--sync` only
when intentionally refreshing those verification fields, then re-render the
markdown view. Do not copy the resulting counts into prose here.

## Yu--Wang--Samworth 2015 full source census

The same instrument for the second paper the campaign carries end to end: Yu,
Wang & Samworth, *A useful variant of the Davis--Kahan theorem for
statisticians*, Biometrika 102(2), 2015.

- `yu-wang-samworth-2015-full-source-census.json` — authoritative structured data;
- `yu-wang-samworth-2015-full-source-census.md` — generated human-readable view.

```bash
python3 scripts/check_yu_wang_samworth_source_census.py            # fast gate
python3 scripts/check_yu_wang_samworth_source_census.py --probe    # + build resolution
python3 scripts/check_yu_wang_samworth_source_census.py --probe --sync
```

**It is keyed on the paper, not on the Lean tree**, so every result the paper
proves has a row whether or not anything formalizes it. A census assembled from
the Lean side enumerates what someone happened to write and cannot report an
absence; this one can, and does.

The checker prints the current source-obligation summary. `FinishYuWangSamworth`
is now a default target, so old notes describing its proved theorems as unguarded
are historical. Use `--probe` when Lean is available to verify declaration
resolution, and do not duplicate the current counts in this README.

Three things this gate does that a name-grep cannot, each of which changed a
row when it was first run:

1. **It distinguishes `private` from missing.** Both fail a `#check`
   identically and mean opposite things. Three declarations the census
   initially cited are `private`; two have public siblings, and one does not —
   the Section 1 complement identity `‖V_1ᵀV̂‖_F = ‖sin Θ‖_F` is proved and
   uncitable, so its row reads `absent`, which is the only honest reading.
2. **It carries a canary.** A name that must never resolve is appended to every
   probe; if it does resolve, the diagnostic parser is broken and the run
   refuses to report rather than reporting universal success. It fired on the
   first run — the path anchor was wrong — which is precisely the failure a
   canary exists to catch.
3. **It separates `status` from `verification`.** The first is a judgement about
   the printed source, the second is measured from the build and is rewritten by
   `--sync`. Hand-maintaining the second is how a census drifts.

Two source-level findings are recorded in the census's `gaps` table and are
worth knowing before quoting this paper:

- **The printed equation (4) is false.** It omits a square on `2 - ‖v̂ - v‖²`.
  The corrected identity and a `norm_num` refutation of the printed polynomial
  are both formalized.
- **The repository carries two incompatible numberings for this paper.** The
  Lean names and `FinishYuWangSamworth` use a flat sequence (Theorem 1,
  Theorem 2, Corollary 3, Theorem 4, Lemma 5); the distilled tex restarts the
  counter per environment type and calls the same results Corollary 1,
  Theorem 3 and Appendix Lemma 1. They agree only on Theorems 1 and 2.
  Resolving it needs one look at the published article.

## The `@[expose]` ratchet

`scripts/check_expose_ratchet.py` enforces the completed conversion away from
file-wide body exposure in `ForTauCeti`.

```sh
python3 scripts/check_expose_ratchet.py           # report
python3 scripts/check_expose_ratchet.py --check   # gate; exit 1 above the baseline
python3 scripts/check_expose_ratchet.py --list    # name the modules
```

**The conversion is complete.** `BASELINE = 0`, so file-wide `@[expose] public
section` is prohibited rather than managed as a declining migration count.

**Per-declaration exposure has its own ratchet.** `PER_DECL_BASELINE` in the
script is the source of truth; do not mirror its numeric value here. Findings fall
into three categories:

| kind | what to do |
|---|---|
| **clean carve-out** — a consumer genuinely must unfold | leave it; the rubric permits this |
| **recorded debt** - avoidable with a `_def` lemma plus rewiring | lower the ratchet in the same commit as the cleanup |
| **compiler limitation** — `Elem`, `Elem.val`, `Elem.mk` | no fix at this toolchain; revisit on a bump |

The third kind is not a defect and must not be filed as debt. Those three failed
*compilation*, not typechecking, and the compiler says so itself: *"locally
inferred compilation type differs from type that would be inferred in other
modules … This is a current compiler limitation for `module`s that may be lifted
in the future."*

**Why a ratchet rather than a snapshot.** The Tau Ceti API rule is that bodies
stay hidden and `@[expose]` is attached only to declarations a consumer must
unfold, with a docstring explaining why. The gate makes regressions visible
without requiring this README to track a moving count.

**Lowering the baseline is the point.** When avoidable exposure is removed,
lower the corresponding baseline in the same commit.

## Paper-library grounding audits

`FinishYuWangSamworth/scripts/verify_grounding.py` checks that package's recorded
repository pins. The similarly named `FinishTanTwoTheta` script is legacy: it
recursively scans the deliberately separate unbounded research file and therefore
its exit status is not a bounded-target completion gate. The promoted bounded
tan-two-theta theorem is guarded through the production Davis--Kahan build/gates.

## Namespace policy

`scripts/check_namespace_policy.py` is an older tripwire that still permits a
small allowlist of root Mathlib namespaces. It is not the policy authority. The
current package direction is owned by `AGENTS.md` and `ForTauCeti/README.md`: new
reusable declarations should carry their intended `TauCeti.*` names. Do not
expand the legacy allowlist merely because this checker permits that mechanism.

## Docstring coverage

`scripts/check_docstring_coverage.py` gates the one quality invariant that had no
check: every public declaration on the submission surface carries a docstring.
Docstrings are a Tau Ceti reviewer gate, so this sits on the critical path.

```sh
python3 scripts/check_docstring_coverage.py           # gate; exit 1 on new findings
python3 scripts/check_docstring_coverage.py --list    # show every finding
python3 scripts/check_docstring_coverage.py --json    # machine-readable
python3 scripts/check_docstring_coverage.py --write-baseline
```

**Why a gate rather than another sweep.** Measured 2026-07-29: two sweep lanes drove
`ForTauCeti/**` and production `DavisKahan/**` to *zero* undocumented, and merges from
other agents put the count back to six **within the hour**. Sweeps cannot hold a line
that four agents are moving.

**Three things it gets right that a naive scan does not.** Each is here because it
already cost a mistake:

- **It tracks `/-` … `-/` depth.** Module-docstring prose that wraps so a line begins
  with `theorem`/`instance`/`structure`/`lemma` at column 0 is not a declaration.
  Missing this inflated a reported figure from 46 to 96 — and the inflated numbers
  were published before the cause was found.
- **It reports anonymous `instance`s** as `<anonymous>`. A scan keyed on declaration
  names cannot see them; six of one lane's 91 were anonymous.
- **Its exclusions are rules with reasons, not a hand-list**, so they survive tree
  movement. `DavisKahan/Experimental/**` is outside `defaultTargets`. The other two
  exclusions are gone, both because their reason was discharged rather than revised:
  `DavisKahan/Interop/Spectra/**` and `DavisKahan/SpectralTheory/Compatibility.lean`
  (the `abbrev` migration shim, excluded so documenting its 45 declarations would not
  entrench a file scheduled for deletion) have both been deleted, and the rules with
  them.

**The baseline** (`dev/docstring-coverage-baseline.json`) exists only to make the
gate adoptable without a flag day. Treat any tolerated finding as debt: shrink
the baseline when a finding is fixed, and do not mirror its current count here.

**Verified to fail, not merely to pass:** injecting an undocumented theorem *and* an
anonymous instance makes it exit 1 and name both, while prose beginning with a keyword
inside a block comment is correctly ignored.

---

## Tau Ceti submission ladder

`scripts/derive_tauceti_submission_ladder.py` derives the rungs in
`tauceti/submission-ladder.md` from the `ForTauCeti` import graph, so the
document cannot silently go stale the way it did within hours of being written.

```sh
python3 scripts/derive_tauceti_submission_ladder.py          # report
python3 scripts/derive_tauceti_submission_ladder.py --check  # exit 1 if the document disagrees
python3 scripts/derive_tauceti_submission_ladder.py --json   # machine-readable
```

Rungs are defined by **seed** modules in the script's `RUNGS` table; everything
else — the `new` count, the cumulative closed slice, what is off the ladder — is
computed. Add a rung by adding seeds, not by writing a number.

The script output is the source of truth for current ladder coverage. Do not
copy module counts or off-ladder counts into prose; they change as the package
grows and rungs are added.

---

## Tau Ceti submission readiness

`scripts/check_tauceti_readiness.py` measures, **per roadmap topic**, the four
parts of the Tau Ceti standard that are checkable from the sources without a
build: a `## Provenance` section on every module (`ForTauCeti/README.md` §5),
no proof escapes, the 1000-line new-file limit (§4), and that every module is
placed in a topic at all.

```sh
python3 scripts/check_tauceti_readiness.py           # per-topic table
python3 scripts/check_tauceti_readiness.py --check    # exit 1 on a blocker
python3 scripts/check_tauceti_readiness.py --json
```

Topic assignment is imported from `check_tauceti_roadmap_topics.py`, so the two
tools share one classification. **Per-topic is the point**: a library-wide
average hides where the debt is. The readiness script output owns the current
provenance, oversize-file, proof-escape, and unplaced-module counts; do not
duplicate them here. `--check` remains the gate for criteria the script treats as
blockers.

---

## Declaration-name drift

Three places in this repository assert declaration names as **data**, where no
compiler checks them: the `theorem_names` lists in `comparator/*.json`; the
`#print axioms` lines in `Challenge/**/Leaderboard.lean` (`Challenge` is not in
`defaultTargets`, so `lake build` does not compile it); and the
`lean_declarations` entries in `dev/davis-kahan-1970-full-source-census.json`.
A rename that is green across the whole default build can therefore still leave
the conformance gate pointing at nothing — which is exactly what happened after
the Wave-1 CourantFischer dedup, again after the §9.2 sorted-eigenvalue rename,
and again in the census, where the `ForMathlib` → `TauCeti` move left **all 87**
named declarations unresolvable while every gate stayed green.

Run after any rename or namespace move:

```bash
python3 scripts/check_declaration_name_drift.py            # fast, build-free
python3 scripts/check_declaration_name_drift.py --verbose  # plus informational notes
```

It resolves names by parsing the sources, not by asking Lean, so it is fast and
works on a tree that does not compile — but for the same reason a pass is a
tripwire, not a proof. `scripts/check_comparator_signatures.py` (which does
invoke Lean) remains ground truth.

Note the precise question each tool answers: the drift check asks only whether a
declaration with the recorded name exists somewhere in the tree. It does not
prove that the declaration is reachable from the intended aggregate or default
build. Use the Lean-backed signature/probe tools for reachability.
