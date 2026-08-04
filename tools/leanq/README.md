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

No runtime dependencies. It shells out to `lake`, so it needs a project that has been built.

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
```

`--lib` picks the library when a project builds more than one; `--project` points at a project
other than the working directory. Every subcommand takes `--json`, and `query`/`stubs` take
`--names` for a bare list, so output drops straight into a pipeline.

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
`Norm` → `Seminorm` rename left six orphans behind. Importing one next to its replacement fails
outright: two modules claiming `TauCeti.diagOp`. `leanq` skips artifacts whose source file is
gone and says how many it skipped.

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
src/leanq/project.py         locate the project, enumerate built modules
src/leanq/lean/decl_index.lean   the metaprogram, run via `lake env lean --run`
```

The Lean side takes a library root and a file of module names, and is toolchain-agnostic — it
has been run against Lean 4.31 and 4.32 projects.
