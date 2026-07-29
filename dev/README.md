# Developer notes — `dev/`

Long-running engineering memory and live coordination for the AIQ DKPS Lean
formalization. Anything that **isn't** the formalization itself, the comparator
challenge package (`Challenge/`, `comparator/`), or paper-facing planning
(`docs/`) lives here. The contents are deliberately agent-readable: an agent
arriving cold should be able to read this folder, understand the project's
pattern of past mistakes, and take fewer of them.

## If you are starting work right now, read these three

| File | What it answers |
|---|---|
| [`LANES.md`](LANES.md) | Who holds what. **Claim your row, commit it, and push it before your first edit** — unpushed is invisible to the other agents. Unlisted means unclaimed. Its `Branch and sync protocol` covers fetching, merging and conflict resolution across agent branches. |
| [`tauceti/README.md`](tauceti/README.md) | The active migration: polishing foundations into `ForTauCeti`, retiring `vendor/Spectra`, converging three operator-theory stacks. |
| [`SEARCH.md`](SEARCH.md) | How to *search* this memory instead of reading it all. Grep patterns and routing rules by symptom. |

The governing policy is in [`../AGENTS.md`](../AGENTS.md), not here. It defines
the dual-track split (Tau Ceti extraction primary, Davis--Kahan source fidelity
maintenance), the dependency firewall, and the completion-claim discipline.

## Layout

```text
dev/
  LANES.md                          # Live lane claims — read and claim before editing
  SEARCH.md                         # How to search engineering memory
  lean-proof-engineering-lessons.md # Recurring Lean elaboration/API/parser traps
  mathlib-proof-polishing.md        # Reference: "folding" proofs to Mathlib style
  mathlib-quality-adapter.md        # Reference: adapting local API to reviewer standard
  external-lean-references.md       # Registry of external Lean repos consulted

  tauceti/                    # The Tau Ceti migration working set (start at its README)
  journals/                   # Postmortems of bugs that took real effort to diagnose
  benchmark-candidates/       # Hard questions distilled from real formalization mistakes
  overlays/                   # Promotion manifests for the surviving Scratch/** sketches
  alternates/                 # Non-building Lean files kept for proof-strategy comparison
  upstream-extraction/        # Provenance JSON for extracted material
  retired-full-part-iii-ambient-route-2026-07-21/   # Compressed archive of a retired route
```

Alongside those, `dev/` holds the Davis--Kahan source-fidelity ledgers
(census, correspondence matrix, frontier status, gap-closure and completion
plans) and their paired `.json` data files. Several of the `.json` files are
read or written by `scripts/check_*.py` — do not hand-edit one without running
its checker.

### Where a new note goes

- A *lane claim or status* → a row in `LANES.md`, not a new file.
- A *postmortem* of a bug that took effort → `journals/`.
- A *transferable trap* another model would also fall into → `benchmark-candidates/`.
- *Migration planning* → `tauceti/`, and record the decision in
  `tauceti/convergence-matrix.md` where it belongs to a declaration.
- *Paper-facing scope and roadmap* → `../docs/planning/`.
- Anything that is only useful with the user in the loop → agent auto-memory,
  not a file here.

Resist adding a dated one-off note. The tree accumulated about ninety of them
between 2026-07-18 and 07-24, they went stale within days, and reading them as
current cost a later session two reversed lanes. They now sit in
[`topurge/`](topurge/MANIFEST.md) awaiting deletion. If a note is worth
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
existence-checked by `scripts/check_davis_kahan_rebased_mathahead.py`, and
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

- `davis-kahan-1970-full-source-census.json` — authoritative structured data;
- `davis-kahan-1970-full-source-census.md` — generated human-readable view;
- `davis-kahan-1970-missing-statements-math-ahead-2026-07-20.md` — the exact
  missing-statement and Section 9 work plan;
- `davis-kahan-1970-private-source-workflow.md` — rules for using the local
  transcription without redistributing it.

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

It currently reports **78/87**. The nine that do not resolve are the
`DavisKahan1970.Section8.*` names backing `DK-8.1-thm` and `DK-8.2-thm`, which
live under `Experimental/**`, outside the `DavisKahan.All` closure; their rows
are marked `candidate_under_repair` / `not_compiling`, so that is the expected
answer, not a defect.

**Use `--verify`, not `--check`, as the gate.** `--check` exits non-zero on any
unresolved name and so fails permanently on those nine. `--verify` is the mode
that understands them: it *derives* each row's verification from what the build
actually resolves and compares it with the recorded value, treating
`not_compiling` as a standing judgement — while refusing to let that judgement
survive its declarations becoming reachable, so a package that gets fixed cannot
stay under-reported. It currently exits 0 with `all 48 rows agree with the
build`.

`--sync` writes the derived values back, which is how `verification` and
`declarations_outside_build` should be maintained: deriving beats
hand-maintaining, because a recorded status drifts the moment someone moves a
module and nobody notices. Run it after any namespace move, then re-render the
markdown view.

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

It currently reports **22 items; 18 formalized, of which 9 are guarded by the
default build; 3 unformalized and still proof debt.** The gap between 18 and 9
is the finding: `FinishYuWangSamworth` is a `lean_lib` but **not a default
target**, so Theorem 1's three norm forms, most of Theorem 4, Lemma 5 and the
corrected equation (4) are proved and unprotected — a refactor can break them
while CI stays green. Adding one target closes most of that gap with no new
mathematics.

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
  movement. `DavisKahan/Experimental/**` is outside `defaultTargets`;
  `DavisKahan/Interop/Spectra/**` is being deleted; and
  `DavisKahan/SpectralTheory/Compatibility.lean` is a migration shim of `abbrev`
  re-exports — **documenting its 45 declarations would entrench a file scheduled for
  deletion**, which is why "undocumented" is the wrong metric for it.

**The baseline** (`dev/docstring-coverage-baseline.json`) tolerates findings that
existed when the gate landed, so it could be adopted without a flag day. It currently
holds 7, all in a file with a live lane row. Shrink it; do not grow it.

**Verified to fail, not merely to pass:** injecting an undocumented theorem *and* an
anonymous instance makes it exit 1 and name both, while prose beginning with a keyword
inside a block comment is correctly ignored.

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

Note the precise question each tool answers, because a green tripwire reads as a
stronger claim than it is. The drift check asks **"does a declaration with this
name exist anywhere in the tree"**. It does *not* ask whether the declaration is
reachable from `DavisKahan.All`. For the census those differ: the nine
`DavisKahan1970.Section8.*` names exist under `Experimental/**` and so pass the
drift check, while `scripts/probe_census_declarations.py` correctly reports them
unresolved against the default build target. Renames are the tripwire's job;
reachability is the probe's.
