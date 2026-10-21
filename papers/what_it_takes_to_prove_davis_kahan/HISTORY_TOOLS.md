# Historical source archaeology for the Davis--Kahan reconstruction

This document covers **Git history**, not the history of operator theory. It
complements [TOOLS.md](TOOLS.md), which describes compiler-derived theorem
closures, source correspondence, and the mathematics/literature registers.

The Git history can answer what this repository contained at any *accessible*
revision: old theorem formulations, deleted research notes, changes in result
inventories, when a particular hypothesis appeared in source, and how the
implementation's proof dependencies changed after rebuilding two revisions.
It cannot establish which mathematics Davis and Kahan knew in 1970, nor can an
old census row certify that the old revision compiled. Both remain separate
review obligations.

## Start with a case packet

Run from the `aiq-dkps-formalization` checkout. No Lake build is needed for the
Git archaeology commands:

```bash
cd ~/code/aiq-dkps-formalization
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py status
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py collect-case --case sine_theta
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py collect-case --case direct_rotation
```

Output:

```text
build/what-it-takes-dk/history/sine_theta/HISTORY_EVIDENCE.md
build/what-it-takes-dk/history/sine_theta/manifest.json
build/what-it-takes-dk/history/sine_theta/timelines/*.json
build/what-it-takes-dk/history/sine_theta/ledgers/*.json
```

The config `data/history_targets.json` specifies paths and literal search
terms. These are *places to investigate*, not historical ancestry or verified
mathematical dependencies. A missing path at HEAD may still have a Git history.
The collected packet is revision-pinned and includes JSON hashes. Outputs go
under `build/` rather than the tracked source registry.

Add a slower, full-tree search for each case's key theorem names:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  collect-case --case sine_theta --include-pickaxe --limit 0
```

`--limit 0` requests all locally accessible matching records. Normal limits
truncate *matches*, not the amount of Git history searched. On very large
histories the unlimited searches may be expensive. `--all-refs` includes
branches/tags available in this clone; it does not recover unreachable commits
or automatically fetch remote branches.

## Retrieve source evidence at any commit

First identify candidate commits from a timeline, `git log`, or a pickaxe query.
Then pin the exact lines by full commit and blob object identifiers. For
example, with the current HEAD:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  excerpt --rev HEAD \
  --path DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean \
  --needle sinTheta_unbounded_formGap_whereDefinedUIN_rclike --context 8 \
  --out build/what-it-takes-dk/history/current-sine-signature.json
```

The output records a full commit SHA, Git blob object ID, complete file SHA256,
exact line interval, excerpt SHA256, and the excerpt itself. For older commits,
replace `HEAD` by the SHA reported by the history packet. If the text is absent
or repeated on several lines, use `--start 123 --end 145` rather than choosing
an arbitrary match. `--needle` is literal, not a mathematical statement parser.

To retrieve a source revision from a deleted or renamed file, use the *path that
existed in that commit*; the timeline includes candidate rename paths. Git's
similarity-based rename detection can miss short files or substantial rewrites;
its guesses must not be treated as theorem-identity evidence.

To compare the source of two revisions without checking either one out:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  diff --old HEAD~1 --new HEAD \
  --path DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean \
  --out build/what-it-takes-dk/history/latest-sine-diff.json
```

This is a source patch, **not** a comparison of elaborated Lean types.

To find candidates where a named lemma or a hypothesis was added/removed:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  pickaxe --case sine_theta \
  --needle FormBoundedSylvesterGap --limit 0 \
  --out build/what-it-takes-dk/history/form-gap-pickaxe.json
```

This uses `git log -S` (literal occurrence count changes). Add `--regex` for
`git log -G` (patch-line regex matches). A commit containing the same number
of occurrences before and after can be omitted. A matching commit is not proof
of first mathematical use, and merges, rebases, date differences, and
cherry-picks can complicate chronology.

## Reconstruct the history of the **claims**

The source-result inventory and source census are ledgers maintained by people
and tools. Investigate their claims *as they stood at past commits*:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  ledger --row S2-sin-theta --limit 0 \
  --out build/what-it-takes-dk/history/sine-inventory-evolution.json

python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  ledger --row DK-4.4-prop \
  --path dev/davis-kahan-1970-full-source-census.json --limit 0 \
  --out build/what-it-takes-dk/history/prop44-census-evolution.json
```

The output records changes to the selected row, with the exact old JSON value,
full commit SHA, and fields that changed. It follows detectable file renames.
This is particularly useful for source-scope reopening episodes: identify the
old acceptance claim, read the changed source proof, and compare the next
revision's exact Lean statement. **Never translate a historical status reversal
into a count of incorrect Lean proofs without direct evidence.**

## Trace a file that moved or disappeared

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  timeline --path dev/davis-kahan-1970-completion-handoff.md --limit 0 \
  --out build/what-it-takes-dk/history/handoff-lineage.json
```

The events have commit dates and `R*`, `M`, `D`, or `A` path statuses. Git
`--follow` is a *heuristic*, useful for finding candidates rather than proving
that two renamed theorem files contain the same theorem. To include other
available refs, add `--all-refs`; interpret branch histories separately.

## Compare the mathematical proof graphs from different revisions

The Git tools **cannot** reconstruct old Lean proof graphs from Git text. To
study the actual change in elaborated dependencies, build each chosen revision
in its own isolated working tree using its pinned `lean-toolchain` and
`lake-manifest.json`. `lake exe cache get` must precede `lake build`.

An example after the two revisions have been built and independently indexed:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/graph_compare.py \
  --old build/what-it-takes-dk/old/sine_theta/slices/full.json \
  --new build/what-it-takes-dk/new/sine_theta/slices/full.json \
  --out build/what-it-takes-dk/history/sine-graph-change.json
```

The tool produces both JSON and Markdown, recording new/removed declarations,
new/removed direct proof dependencies, changes to `type` vs `proof` edge roles
(when available), and changes in the distribution across `ForTauCeti` and the
Davis--Kahan source layer. Graph input SHA256 hashes are recorded.

When two versions of the existing `research.py` statement-closure sidecar are
available, use `--old-statement` and `--new-statement` as well. This additionally
compares Lean's structural and printed type hashes, the displayed theorem
signature, binders, and the named-definition closure. Hash equality is evidence
about *elaborated terms in their respective environments*, not a proof that
every imported definition retained the same meaning. The two dependency graphs
and the two statement sidecars must each come from their corresponding pinned
builds.

If a declaration was renamed, do **not** equate them automatically. After
reviewing the exact mathematical statements, pass a deliberate mapping:

```bash
# Illustration only; replace names with a pair you have mathematically reviewed.
# --alias Old.Namespace.lemma=New.Namespace.lemma
```

Alternatively maintain `data/declaration_aliases.csv` with `old,new,evidence_id,
review_status,reason`, then pass `--alias-file` to the comparer. Only rows
marked `reviewed` with an evidence ID are accepted. The mapping asserts an
investigator-supplied correspondence; it does not mechanically prove equivalent
theorem types.

Git archives alone cannot attest the graph came from the stated revision:
record the actual commit, Lean toolchain, library manifest and graph digest in
the associated research notebook. `--old-commit` and `--new-commit` are
*declared labels*, not independently attested by the comparator.

## Immutable citations and reviewer separation

`data/reviewed_git_evidence.csv` has one row for each selected Git source
excerpt. Use the hash and line metadata from `excerpt` to fill `commit`,
`path`, `line_start`, `line_end`, `blob_oid`, and `excerpt_sha256`. Set
`review_status` to `candidate`, `reviewed`, or `rejected`; only mark a
mathematical interpretation reviewed after actual mathematical inspection.

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py verify
```

The verification command checks that the Git object and quoted bytes are still
available and agree with the pinned hashes. It **does not** verify the meaning
of the interpretation or certify mathematical influence. For citations about
Jordan, Rosenblum, Davis, Kahan, or later authors, continue to use
`data/history_claims.csv` and the page/theorem in the **original mathematical
publication**. Git repository history is evidence of the *formalization
project's* development, not nineteenth- or twentieth-century mathematical
priority.

## Accessing another repository's history

The optional `--repo` argument points to a different Git checkout, such as a
local Tau Ceti or former Spectra checkout. It **does not fetch or discover**
other repositories. Supply that repository's own path/revision with `excerpt`,
`timeline`, `pickaxe`, or `diff`; all records should identify both the owning
repository and full commit when later cited in the paper. For example:

```bash
python3 papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  --repo ~/code/TauCeti status
```

This is useful for distinguishing code reused through a former dependency from
proofs originally constructed in the Davis--Kahan project. Repository commits
are *formal code provenance*; actual mathematical ancestry still requires
published sources and precise theorem comparison.

## Integrity and failure cases

- All commands are read-only with respect to Git: no branch switching, reset,
  checkout, worktree creation, fetch, or automatic commit.
- `status` reports whether this clone is shallow or has promisor remotes. An
  empty historical result in such a clone is *not* evidence that the theorem or
  source was absent in the full history. Full older objects must be supplied
  separately; this tool never fetches them.
- With unavailable/missing historical objects, use the error or incomplete
  packet report; do not replace missing evidence with a guessed source path.
- A current theorem declaration may not exist at earlier revisions; provide
  historical paths and names deliberately.
- Git authorship/commit dates are evidence about the repository record, not
  mathematical authorship or first discovery.
- Reproduce results by pinning commits and tool input hashes. Run the
  repository's source census and Lean checks independently for claims about
  **current** formal verification.

## Research-tool validation

During authoring, the Git reader and graph comparer were exercised against
synthetic repositories with three or more commits, renamed and deleted files,
historical ledger transitions, SHA-pinned excerpts, and shallow-clone gaps.
The fixtures were not added to this checkout: these are research-only tools,
not new maintenance gates or generic library replacements. The scripts can be
syntax-checked in place with:

```bash
python3 -m py_compile \
  papers/what_it_takes_to_prove_davis_kahan/tools/git_history.py \
  papers/what_it_takes_to_prove_davis_kahan/tools/graph_compare.py
```
