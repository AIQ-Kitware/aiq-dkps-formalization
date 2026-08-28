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
leanq graph-index --out build/leanq/project-semantic-graph.json
```

`deps --local` answers "what would I have to bring along to restate this somewhere else": it
follows only declarations from the same library, since Mathlib is available wherever you land.
That question came up as "which of these stubbed definitions could I fill in without dragging
in scaffolding", was first answered with a regex over source text, and was wrong.

`--lib` picks the library when a project builds more than one; `--project` points at a project
other than the working directory. Every subcommand takes `--json`, and `query`/`stubs` take
`--names` for a bare list, so output drops straight into a pipeline.

## Proof dependency graphs

The recommended graph workflow is staged so presentation iteration never re-runs Lean.

### Stage 1: reusable project semantic index

`graph-index` is the only graph stage that invokes Lean. With no positional target it discovers the
project's ordinary Lake/default-target build surface and writes one reusable declaration graph for
that whole first-party surface. The graph contains **direct dependency edges only**; target closures,
transitive reductions, headline projections, and HTML are downstream file transformations.

```bash
leanq graph-index \
  --out build/leanq/project-semantic-graph.json
```

The discovery is Lake-driven rather than repository-specific. It honors `defaultTargets`, local
`lean_lib` ownership, `srcDir`, module targets such as `DavisKahan.All`, and glob-built libraries
such as `ForTauCeti` whose root module does not import their full build surface. Optional/non-default
libraries are excluded from the ordinary project graph; opt into every declared local library with
`--all-libraries`, or add an individual optional library with `--include-lib`.

The expensive pieces are cached independently per library/module-root set as graph-vN JSONL files.
Graph caches now carry a source/tool fingerprint covering the local import closure, Lake file,
toolchain declaration, and Lean exporter. An unchanged cache is reused automatically; a source or
exporter change invalidates the affected cache without needing `--refresh`. Explicit controls remain
available:

```bash
# Force only the layers you know changed.
leanq graph-index \
  --refresh-lib Acharyya2025 \
  --refresh-lib DkpsQuench2026 \
  --out build/leanq/project-semantic-graph.json

# Force every project-graph cache.
leanq graph-index \
  --refresh \
  --out build/leanq/project-semantic-graph.json
```

A positional target or `--root-module` still requests a deliberately narrower imported-environment
index when desired, but presentation tooling should normally start from the project graph. The
aggregate JSON records each library's import roots, cache path/fingerprint/reuse status, all direct
declaration edges, and unresolved private-support diagnostics. The graph direction is
**dependency → consumer**.

Target-specific exploration is a second-stage operation and never invokes Lean:

```bash
leanq graph-slice \
  build/leanq/project-semantic-graph.json \
  DkpsQuench2026.QueryEfficiency.infiniteFixedSubset \
  --transitive-reduction \
  --out build/leanq/quench-proof-graph.json
```

That same master graph can be sliced repeatedly for any declaration it contains.

### Whole-formalization explorer with headline landmarks, no Lean

One file-only rendering command embeds the complete semantic graph and annotates actual census
declarations as landmarks:

For the current DK / YWS / Quench review:

```bash
leanq graph-html \
  build/leanq/project-semantic-graph.json \
  --census dev/davis-kahan-1970-full-source-census.json \
  --census dev/yu-wang-samworth-2015-full-source-census.json \
  --census dev/quench-2026-full-source-census.json \
  --boundary headline \
  --out build/leanq/project-semantic-graph.html

xdg-open build/leanq/project-semantic-graph.html
```

**Packages.** The `Packages` button toggles which libraries the projection may draw, with a
declaration count beside each. `--boundary` decides whether the payload carries the Mathlib and
Lean-core declarations the project depends on but does not declare: `none` (default), `headline` for
consumers inside the headline dependency union, or `project` for every consumer. The scopes differ
by more than an order of magnitude -- `headline` adds about 2,900 declarations and 107,000 edges,
`project` about 8,000 and 1,476,000, because nearly every declaration in the repository reaches
`Eq`, `Nat`, and `Real`. The boundary library starts **disabled** in the viewer: it is the reason
the option exists and almost never what you want on screen. The index resolves boundary names only
by name, so Lean core and Batteries constants are grouped under `Mathlib` with them.

The HTML retains every indexed declaration and direct edge, then derives changing projections
locally in the browser without rerunning Python or Lean.

**Headline subset.** Selection is per *declaration*, so one leaf theorem of a claim that registers
several realizations can be the whole selection. Each claim is a group control over its
realizations, listed beneath it with the leafmost ones marked; the paper default selects the leaves
of every headline *theorem* row — the four Davis--Kahan Section 2 theorems, both Yu--Wang--Samworth
Theorem 2 conclusions shown in `formalization_draft2`, and both Quench Theorem 2 conclusions — while
Quench's estimator definition and standing assumption stay available but unselected.
`--default-claim Q26-NN` (repeatable) overrides that on the command line. Per-family
`leaves` / `all` / `none` buttons and the `Paper default` / `All` / `None` buttons move whole groups.

The panel is grouped by paper, one collapsible section each, and every section starts closed with a
`selected / total` claim tally beside its name, so reaching one paper's headline theorems does not
mean scrolling past every other paper's. Opening a section is independent of selecting from it: the
`leaves` / `all` / `none` buttons act on the whole paper without opening it.

Every claim and realization reports which packages its dependency closure actually reaches. A claim
whose closure never leaves its own library is visible immediately, which is how a census row that
registers the abstract form of a theorem rather than the instantiation consuming the shared
mathematics shows up.

**Only reachable nodes.** With `Ancestors of selection only` checked (the default), the visible
universe is exactly the dependency closure of the selected headline theorems: a declaration no
selected headline reaches is never drawn, expanding a cluster cannot introduce one, and selecting
no headline at all renders an empty graph. Unchecking it restores the whole project.
`Shared foundations only` narrows further to declarations at least two selected headlines reach.

**Collapse internal helpers.** Checked by default. Private constants, proof terms and generated
equation lemmas -- about a third of the declarations in a project index -- carry no conceptual
content, but a public theorem's route to its foundations usually runs straight *through* them, so
hiding them outright would cut the very chains the picture is for. They are contracted instead:
each public consumer is reconnected to the public dependencies it reaches through a chain of them,
and the resulting edge is drawn dashed and reports how many were folded away. On the current index
that is 7258 of 22393 declarations folded, with 3233 edges routed through at least one of them --
the links a naive hide would have severed. Reachability is always computed on the full graph, so
ancestor closures, coverage counts and shortest paths do not depend on the setting; only what is
drawn does.

**Export.** `DOT` and `JSON` write the chosen scope to a file. After a `DOT` export the side panel
shows the Graphviz invocation that renders it, with a copy button; the `.dot` repeats it in a header
comment. Paths are written against `~/Downloads`, the browser's download directory, so the command
can be pasted into any shell without changing directory first:

```dot
// leanq export: 69 nodes, 99 edges, scope visible
//   dot -Tsvg ~/Downloads/leanq-visible-69-nodes.dot -o ~/Downloads/leanq-visible-69-nodes.svg
//     hierarchical, left to right
```

Two selects beside the export buttons choose the output format (`SVG`, `PNG`, `PDF`) and the layout
engine (`auto`, `dot`, `neato`, `fdp`, `sfdp`, `circo`, `twopi`). Changing either rewrites the shown
command in place; the `.dot` already on disk is untouched, and its header records the command as it
was exported.

`auto` picks the engine from the size of the export. `dot` reads the `rankdir=LR` the file already
sets and its layering is the point of the drawing, but its iterative passes are superlinear: past
2500 nodes the command bounds them with `-Gnslimit=2 -Gmclimit=2` and offers `sfdp` as the
fallback, and past 12000 it leads with `sfdp -Goverlap=prism`, which is the only engine that
realistically finishes at that size. Picking an engine explicitly overrides that, and the panel says
so when the choice is likely to be slow: measured on this project's 2007-node export, `neato` did
not finish inside two minutes while `dot` took 134s.

`PNG` always carries `-Gsize='30,30!' -Gdpi=150`. Without it Graphviz hits its bitmap ceiling and
says `graph is too large for cairo-renderer bitmaps. Scaling by 0.317408 to fit` -- it does not
fail, it silently shrinks the whole drawing, which on that same export produced an unreadable
11375x32766 pixel, 46 MB file. With the cap it is 1562x4500 and 2.2 MB. `SVG` and `PDF` are vector
formats and get no cap.

**Progressive hierarchical expansion.** A declaration is collapsed at the shallowest prefix of
`Library / module segment / module segment / ...` that neither the global `Group` depth nor an
explicit double-click has opened, so double-clicking `DavisKahan` opens its immediate submodules
rather than its thirteen thousand declarations and leaves every other branch exactly as it was.
Double-click is always an expansion; collapsing is an explicit button in the selection panel.
Selected headline declarations always render as real nodes.

Boxes say whether they can be opened: `▸` marks an expandable node, `•` a fully opened one, `★` a
selected headline theorem. Each box is labelled with its qualified Lean name, wrapped on its dots,
and carries its edge degrees — a declaration shows true `in` / `out` direct-edge counts, the counts
actually drawn, and how many dependencies are still folded inside a cluster; a cluster shows its
declaration, child, internal-edge and projected-edge counts.

**Paper foundations.** `--foundations` takes a CSV with `module` and `theory_id` columns -- the
draft's `generated/formalization_declaration_formal_provenance.csv` is one -- and tags each
declaration with the paper's named mathematical foundation, reading labels from
`formalization_basic_theories.csv` beside it. The taxonomy spans packages: the same foundation has
modules in `DavisKahan`, `ForTauCeti`, and `YuWangSamworth2015`, because material was promoted
between them. `Paper foundation bands` therefore groups the graph by the mathematics rather than by
which package currently hosts it, which package columns alone cannot show. In that mode a cluster
is rooted at its foundation, so no cluster spans two.

**Layout.** `Library bands` gives every package its own column and pins the selected headline
theorems to one extremal column, so the edges into them are the picture. Column order is a
depth-first Kahn traversal of the package dependency DAG: a package is placed once its prerequisites
are, and the traversal follows the heaviest outgoing chain first, which keeps a lineage contiguous
(`ForTauCeti → DavisKahan → YuWangSamworth2015`, then the DKPS application chain) instead of
interleaving packages that never touch. Only packages the current selection reaches get a column;
the rest are named in a `not reached` badge. `Dependency depth` keeps the older topological columns.
Columns are labelled with their visible node count.

**Export.** `DOT` and `JSON` write the visible projection, the selected headline closure, one
declaration's dependency cone, or the complete graph. DOT nodes carry `leanq_library`,
`leanq_module`, `leanq_kind`, `leanq_headline`, `leanq_headline_claims`, `leanq_headline_family`,
`leanq_coverage`, `leanq_depth`, and `leanq_declaration_count` attributes, so a Graphviz layout can
style headline nodes and package membership; collapsed edges carry their multiplicity as `label`
and `weight`.

Canonical declarations from `semantic_review` become strongly marked headline nodes. Supporting
declarations get a weaker marker. For an older census without reviewed canonical metadata, the
exact `lean_declarations` list remains the fallback realization list. Headline metrics include
transitive dependency size, maximum depth, module/library span, exclusive/shared dependency counts,
and the nearest shared dependency with its exact shortest path.

### Optional focused headline analysis, no Lean

`graph-headlines` remains useful when a smaller JSON artifact is wanted. Its default
`--view dependencies` computes the union of all real canonical headline dependency closures and
retains every direct declaration edge in that union; no target is required:

```bash
leanq graph-headlines \
  build/leanq/project-semantic-graph.json \
  --census dev/davis-kahan-1970-full-source-census.json \
  --census dev/yu-wang-samworth-2015-full-source-census.json \
  --census dev/quench-2026-full-source-census.json \
  --view dependencies \
  --out build/leanq/headline-dependencies.json
```

Its payload includes:

- every canonical headline declaration, including multiple realizations of one claim;
- complete real dependency nodes and compiler-derived direct edges;
- per-node headline coverage and shared-frontier annotations;
- per-headline nearest shared dependency distances and witness paths;
- pairwise nearest common dependencies; and
- a structural projection whose collapsed linear edges retain exact witnesses and omitted counts.

An optional `--target` only annotates reachability and distance. The legacy target-oriented summary
is still available explicitly as `--view consumption --target DECLARATION`.

### Stage 3: HTML, no Lean

Rendering is a separate command and reads only saved JSON:

```bash
leanq graph-html build/leanq/headline-dependencies.json \
  --out build/leanq/headline-dependencies.html
```

This separation means:

```text
Lean/source changes         -> graph-index, then whichever file transforms you need
target selection             -> graph-slice or optional graph-headlines annotation; no Lean
census selection             -> graph-headlines or graph-html annotation; no Lean
HTML / CSS / JS iteration    -> graph-html only; no Lean
```

`leanq graph` remains as a backwards-compatible one-shot target-ancestor command, including its
older `--html`/`--presentation` options.  New presentation work should prefer the staged commands
above so rendering does not accidentally trigger Lean.

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
the target dependency closure, the default behavior is to omit that headline, write the exact JSON
and HTML anyway, and report the missing name both on stderr and in a visible viewer warning. This
keeps stale editorial metadata from blocking access to the semantic graph. Use
`--strict-presentation` when a curated presentation file is itself an audited artifact and any
missing headline should fail the command.

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
validated and reduced on the Python side before it is embedded. Missing curated names are carried
in `presentation.missingHeadlines`, so downstream tooling can distinguish a complete curated view
from a degraded-but-still-truthful one.

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

### Package-first census ancestry/comparison publisher

`graph-compare-html` is an alternative publisher over the same semantic index used by
`graph-html`. It is generic over the census schema: zero, one, or many loaded census families can
be active in the browser. Zero active families shows the union of all loaded census ancestry; one
shows that formalization's ancestor closure; several families split each package internally by exact
ancestry-membership subsets.

Root Lake libraries remain persistent compound clusters. Cross-package edges are bundled by package
pair by default, while package-internal group edges are opt-in. Mathlib boundary declarations can be
hidden, summarized as one package, grouped by namespace root, or shown as a capped set of high-impact
boundary declarations.

The graph is also manually arrangeable. With `Arrange by drag` enabled, drag any visible declaration
or module cluster to move it inside its package and immediately reroute its incident edges. Drag a
package header to move that whole package and all visible contents. Drag empty canvas to pan. Manual
positions survive zooming, package expansion/collapse, and family changes when the same visible node
still exists. `Reset moved` returns the graph to automatic placement; the inspector can reset one
node or package independently.

```bash
leanq graph-compare-html \
  build/leanq/project-semantic-graph.json \
  --census dev/davis-kahan-1970-full-source-census.json \
  --census dev/yu-wang-samworth-2015-full-source-census.json \
  --census dev/quench-2026-full-source-census.json \
  --boundary headline \
  --family 'Davis–Kahan' \
  --family 'Quench' \
  --out build/leanq/proof-comparison.html
```

`--family` is repeatable and chooses only the initial active set. Omitting it starts with zero active
families and the all-census ancestry union. A census can provide a stable generic display family with
`{"presentation": {"family": "My Formalization"}, ...}` or top-level `family`; filename inference is
only a fallback.
