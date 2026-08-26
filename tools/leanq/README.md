# leanq

Query a built Lean 4 library from the elaborator instead of from regexes.

## Why

Counting "how many definitions are stubbed with `sorry`" by grepping source is harder than it
looks. Three attempts at it in one sitting gave three different answers:

| method | stubbed `def`s found |
|---|---|
| regex, span-based | 22 — attributed the *next* declaration's `sorry` to the preceding `def` |
| regex, `:=`-based | 0 — mis-parsed multi-line signatures |
| regex, line-based | 19 — right shape, wrong denominator |
| **`leanq`** | **22 of 129** |

The failure is not carelessness, it is that the question is semantic. Whether a declaration is a
`def` or a `theorem`, whether it *returns* `Prop`, and whether its proof term reaches `sorryAx`
are facts about the elaborated environment. `leanq` imports the built library and reads them off,
using the same `collectAxioms` that backs `#print axioms`.

## Install

```bash
pip install -e tools/leanq        # or: uv pip install -e tools/leanq
```

No required runtime dependencies. It shells out to `lake`, so it needs a project that has been built.
Optional Python line profiling is available through the `profile` extra.

## Use

```bash
cd /path/to/some-lean-project

leanq libs                       # which libraries have build artifacts
leanq index                      # build the index (cached at .leanq/<Lib>.jsonl)
leanq stats                      # def/theorem stub counts per module
leanq stubs --kind def           # every definition reaching sorryAx
leanq stubs --prop-valued        # predicates stubbed out: `def Foo : X → Prop := sorry`
leanq query --name Schatten --json
leanq axioms myTheorem           # the axiom closure of one declaration
leanq deps myDef --local         # helpers from *this* library that myDef needs
leanq deps myDef --transitive    # everything it reaches, Mathlib included
leanq rdeps myDef                # who references myDef
leanq query --uses myDef         # same, composable with the other filters
leanq graph FinalTheorem --transitive-reduction --json
```

`deps --local` answers "what would I have to bring along to restate this somewhere else": it
follows only declarations from the same library, since Mathlib is available wherever you land.
That question came up as "which of these stubbed definitions could I fill in without dragging
in scaffolding", was first answered with a regex over source text, and was wrong.

`--lib` picks the library when a project builds more than one; `--project` points at a project
other than the working directory. Every subcommand takes `--json`, and `query`/`stubs` take
`--names` for a bare list, so output drops straight into a pipeline.

## Proof dependency graphs

`leanq graph` is the semantic backend and interactive viewer for declaration-level proof
architecture. It resolves each target declaration to its live source module, imports only those
module roots, merges the elaborated declarations from the local libraries in that real import
closure, and keeps the graph direction **dependency → consumer** so the picture reads from
mathematical foundations toward the requested conclusion.

Target-scoped imports are intentional. A Lake build tree can retain optional or historical
`.olean` files from an older Lean toolchain even after the ordinary project build is green. Those
artifacts are irrelevant to a target proof and must not make graph extraction fail. The target
module's real import closure remains authoritative: if an incompatible artifact is actually on that
closure, `leanq` reports it and suggests rebuilding the target module.

```bash
# Exact JSON for the full project-local ancestor closure.
leanq graph DkpsQuench2026.QueryEfficiency.infiniteFixedSubset \
  --transitive-reduction \
  --out build/quench-proof-graph.json

# The same exact graph as one self-contained offline HTML file.
leanq graph DkpsQuench2026.QueryEfficiency.infiniteFixedSubset \
  --html build/quench-proof-graph.html

# A narrower explicit library scope remains useful while iterating. The same
# target module is imported for each selected library; unrelated library artifacts
# are never bulk-imported.
leanq graph Some.Quench.Theorem \
  --include-lib ForTauCeti \
  --include-lib DavisKahan \
  --include-lib YuWangSamworth2015 \
  --include-lib Acharyya2025 \
  --include-lib DkpsQuench2026 \
  --html build/proof-graph.html

# Source lookup is normally automatic. For generated/ambiguous declaration names,
# give the defining module explicitly.
leanq graph Some.Generated.Declaration \
  --root-module DkpsQuench2026.Geometry.AlignedCMDS \
  --html build/proof-graph.html
```

The graph command uses separate target-scoped caches named like
`<Library>.roots-<TargetModule>.graph.jsonl`. This also prevents an older whole-library graph cache
from being mistaken for the current target environment. Graph mode is deliberately more complete
than ordinary inventory mode: it retains Lean internal/private constants and their dependencies.
That prevents a public dependency path from being severed merely because it passes through private
proof support. Internal nodes are marked with `"internal": true` so the viewer can collapse them
*after* reachability has been established.

Lake `srcDir` settings are honored when resolving source modules, including the nested
`YuWangSamworth2015` package layout. The source import walk is used only to choose graph scope;
all declaration edges are still extracted from Lean's elaborated environment.

The JSON payload contains the exact project-local direct edges plus `reducedEdges` when requested
(or automatically when HTML is rendered). The latter is a reachability-preserving transitive
reduction. Ordinary declaration DAGs get the unique DAG reduction; rare generated-constant cycles
are condensed into strongly connected components first. Dependencies outside the indexed local
libraries, normally Mathlib or Lean, are summarized by prefix; `--include-unresolved` includes
their full boundary names.

### Interactive HTML viewer

The generated HTML has no server or JavaScript-package requirement. Graph data, CSS, and vanilla
JavaScript are embedded into one file that can be opened directly in a browser. The viewer provides:

- **Presentation**, **reduced**, and **direct** graph modes;
- reachability-preserving collapse of private/internal support declarations;
- search by full declaration name, short name, or module;
- pan, wheel zoom, fit-to-view, and library emphasis;
- node details with module/library/kind/source-line and direct degree counts;
- edge details showing the exact witness path behind every collapsed presentation edge;
- interactive promotion/removal of headline nodes; and
- export of the current headline selection as a reusable exact-name presentation JSON file.

The browser never guesses mathematical roles. It can change which exact declarations are displayed,
but every edge is derived from the elaborated graph and every collapsed edge retains a witness path
back to that graph.

### Curated presentation views

A presentation JSON is the human-owned layer over compiler facts. It can provide graph targets,
labels, groups, descriptions, and the declaration names that should survive in the headline graph.
Names are resolved exactly or as unambiguous Lean short names. If a named headline is no longer in
the target dependency closure, generation fails instead of dropping it from the slide.

```json
{
  "schemaVersion": 1,
  "title": "YWS → Acharyya → Quench",
  "targets": ["DkpsQuench2026.quench_part2_from_aligned_configFrobError_hp"],
  "headlines": [
    {
      "name": "YuWangSamworth2015.sq_gap_mul_sum_cross_le_of_population_gap_opNorm",
      "label": "YWS population-gap sin-Θ",
      "group": "Yu–Wang–Samworth"
    },
    {
      "name": "Acharyya2025.ConfigPerturbation.exists_isometry_configFrobError_spectralConfig_le",
      "label": "Frobenius configuration perturbation",
      "group": "Acharyya"
    }
  ]
}
```

A checked-in starting view for the current Frobenius bridge lives at
`tools/leanq/presentations/quench-frobenius-core.json`:

```bash
leanq graph \
  --presentation tools/leanq/presentations/quench-frobenius-core.json \
  --html build/quench-frobenius-core.html \
  --out build/quench-frobenius-core.json
```

The target can be supplied positionally instead; positional targets override the targets in the
presentation file. `--headline Some.Declaration` adds a one-off initial headline without editing the
JSON, while `--title` and `--subtitle` override display copy.

`leanq.graph.projected_reduction` remains the Python presentation primitive: given selected headline
declarations, it computes their reachability relation, transitively reduces it, and attaches a
shortest exact witness path through omitted support nodes to every displayed edge. The HTML viewer
implements the same operation for interactive headline changes, while a loaded presentation spec is
prevalidated and reduced on the Python side before it is embedded.

## Promotion-boundary queries

`promotions` is for repositories that use path components such as `Experimental` or
`MathAhead` as staging labels.  It imports only the requested production root, then uses
the elaborated declaration dependency graph to separate three different questions that
source grep tends to conflate:

- **tagged but reachable** -- declarations present because the production root imports a
  tagged module somewhere in its import closure;
- **boundary** -- tagged declarations referenced directly by an untagged declaration;
- **support** -- tagged declarations transitively required by a boundary declaration.

The boundary plus support rows are the declarations that actually have to move (or be
reproved/replaced) before the production declaration graph can stop depending on tagged
modules.  Merely reachable declarations are not automatically promotion work.

For this repository:

```bash
pip install -e tools/leanq
lake build DavisKahan
leanq --lib DavisKahan promotions --root DavisKahan --refresh
leanq --lib DavisKahan promotions --root DavisKahan --kind theorem --json > /tmp/dk-promotions.json
```

The default tags are exact dotted-name components `Experimental` and `MathAhead`; add or
replace them with repeated `--tag`.  `--consumer-prefix DavisKahan.Sources` is useful when
you specifically want source-facing consumers rather than every untagged declaration under
the chosen root.  `--boundary-only` omits tagged helper closure and shows only direct
crossings.

`leanq` indexes public environment constants.  Private implementation helpers are therefore
not counted as separate promotion declarations; when moving a module, move or rewrite the
private proof support with its public endpoint.

### Promotion-query performance

`promotions` now uses a separate **dependency-only** root-scoped index. The full index used by
`stubs`, `stats`, and `axioms` computes transitive axiom closure, proposition classification,
and declaration source ranges for every declaration. None of those fields participate in a
promotion boundary, so the structural index emits them as `null` and only computes the direct
dependency graph. The two cache formats have different filenames and cannot accidentally replace
each other.

The first `--refresh` still has to import the chosen Lean root. If build/import optimization has
made `DavisKahan` cheaper to load, that improvement directly helps leanq as well. To distinguish
Lean import time from leanq's declaration walk, enable coarse Lean-side timings:

```bash
LEANQ_TIMINGS=1 leanq --lib DavisKahan promotions --root DavisKahan --refresh
```

The command prints `import_ns=...` and `emit_ns=...` on stderr. A large `import_ns` points at the
module/build graph; a large `emit_ns` points at leanq's environment walk.

For Python line-level profiling, install the optional extra and set `LINE_PROFILE=1`:

```bash
python3 -m pip install -e 'tools/leanq[profile]'
LINE_PROFILE=1 LEANQ_TIMINGS=1 \
  leanq --lib DavisKahan promotions --root DavisKahan --refresh
```

When `LINE_PROFILE=1` is absent, leanq uses an internal no-op `@profile` decorator and does not
import `line_profiler`, so ordinary installs remain dependency-free. The decorated Python hot
paths include project/module discovery, index construction/loading, and promotion-closure
classification.

## What a record contains

```json
{"name": "TauCeti.foo", "module": "ForTauCeti.Analysis.Foo", "kind": "def",
 "isProp": false, "propValued": true, "sorried": true, "axioms": ["sorryAx"]}
```

- `kind` — `def` (which includes instances and projections, since those are definitional
  constants), `theorem`, `axiom`, `inductive`, `ctor`.
- `isProp` — the declaration *is* a proof.
- `propValued` — it *returns* `Prop` after its arguments, i.e. it is a predicate.
- `sorried` — its axiom closure contains `sorryAx`. This is transitive, so a theorem that
  invokes a stubbed lemma is also flagged; that is usually what you want and occasionally not.

Note the denominator: `kind == "def"` counts environment constants, not source-level `def`
keywords. A library with 66 `def` lines can have 129 definitional constants.

## Two things it caught immediately

**A root module that does not import its own library.** `TauCetiRoadmap.lean` imports 23
modules and omits an entire roadmap, because the lakefile globs the library in rather than
aggregating it. Indexing by importing only the root reported *zero* declarations for that
roadmap — a confident, wrong answer. `leanq` therefore imports every built module explicitly.

**Stale build artifacts.** `lake` does not delete the `.olean` of a module you renamed, so a
`Norm` → `Seminorm` rename left six orphans behind. Inventory indexing skips artifacts whose source
file is gone. Proof-graph indexing goes further: it imports only the requested target module(s), so
an optional module whose source still exists but whose `.olean` belongs to an older Lean toolchain
cannot poison an unrelated proof graph.

## Relationship to `leanclient`

[`leanclient`](https://pypi.org/project/leanclient/) drives the Lean language server, and
answers *positional* questions: the goal at a cursor, diagnostics for a file, hover text. It
opens files and elaborates them.

`leanq` answers *whole-library* questions from already-built artifacts: what exists, of what
kind, resting on which axioms. One index, then cheap offline queries.

They compose — use `leanq stubs --names` to find the declarations worth looking at, then
`leanclient` to inspect goal state at one of them. `leanq` deliberately does not depend on it;
install it alongside if you want the positional half.

## Layout

```
src/leanq/cli.py             argparse CLI
src/leanq/index.py           build/load/filter the index
src/leanq/graph.py           cross-library target graphs and graph reductions
src/leanq/presentation.py    exact-name curated headline views
src/leanq/viewer.py          standalone HTML renderer
src/leanq/assets/viewer.html interactive offline viewer
src/leanq/project.py         locate the project, enumerate built modules
src/leanq/lean/decl_index.lean   the metaprogram, run via `lake env lean --run`
```

The Lean side takes a library root and a file of module names, and is toolchain-agnostic — it
has been run against Lean 4.31 and 4.32 projects.
