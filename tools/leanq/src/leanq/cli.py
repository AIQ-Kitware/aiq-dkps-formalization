"""``leanq`` command line.

Output defaults to plain text and every subcommand takes ``--json``, so an agent can either
read it or parse it without a second thought.
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path

from ._profile import profile
from .index import (
    Decl,
    build_index,
    by_name,
    closure,
    ensure_index,
    ensure_scoped_index,
    filter_decls,
    index_path,
)
from .graph import (
    merge_declarations,
    strongly_connected_components,
    target_dependency_graph,
    transitive_reduction,
)
from .presentation import build_presentation, load_presentation
from .viewer import write_graph_html
from .project import ProjectError, find_project
from .promotion import DEFAULT_TAGS, promotion_report


def _tristate(args, flag: str) -> bool | None:
    value = getattr(args, flag, None)
    return value


@profile
def _resolve(args):
    project = find_project(Path(args.project) if args.project else None)
    library = args.lib
    if library is None:
        libs = project.libraries()
        if len(libs) != 1:
            raise ProjectError(
                f"{project.root} builds {len(libs)} libraries ({', '.join(libs) or 'none'}); "
                f"pass --lib"
            )
        library = libs[0]
    return project, library


def _emit(decls: list[Decl], args) -> None:
    if args.json:
        json.dump([d.to_json() for d in decls], sys.stdout, indent=2)
        sys.stdout.write("\n")
        return
    if args.names:
        for decl in decls:
            print(decl.name)
        return
    width = max((len(d.short_name) for d in decls), default=0)
    for decl in decls:
        marks = "".join(
            [
                "S" if decl.sorried is True else ("?" if decl.sorried is None else "-"),
                "P" if decl.prop_valued is True else ("?" if decl.prop_valued is None else "-"),
            ]
        )
        print(f"{marks}  {decl.kind:8s} {decl.short_name:{width}s}  {decl.location()}")
    print(f"\n{len(decls)} declaration(s)   [S]orried  [P]rop-valued", file=sys.stderr)


def cmd_index(args) -> int:
    project, library = _resolve(args)
    out = build_index(project, library, out=Path(args.out) if args.out else None)
    print(out)
    return 0


def cmd_query(args) -> int:
    project, library = _resolve(args)
    decls = ensure_index(project, library, refresh=args.refresh, verbose=not args.json)
    selected = sorted(
        filter_decls(
            decls,
            kind=args.kind,
            sorried=_tristate(args, "sorried"),
            prop_valued=_tristate(args, "prop_valued"),
            is_prop=_tristate(args, "is_prop"),
            module=args.module,
            name=args.name,
            axiom=args.axiom,
            uses=getattr(args, "uses", None),
        ),
        key=lambda d: (d.module, d.name),
    )
    _emit(selected, args)
    return 0


def cmd_stubs(args) -> int:
    """Declarations whose axiom closure contains `sorryAx` — the honest `sorry` count."""
    args.sorried = True
    args.axiom = None
    args.is_prop = None
    return cmd_query(args)


def cmd_stats(args) -> int:
    project, library = _resolve(args)
    decls = ensure_index(project, library, refresh=args.refresh, verbose=not args.json)
    depth = args.depth
    table: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    for decl in decls:
        group = ".".join(decl.module.split(".")[:depth]) if depth else decl.module
        counter = table[group]
        if decl.kind in ("def", "theorem"):
            counter[f"{decl.kind}_total"] += 1
            if decl.sorried:
                counter[f"{decl.kind}_stub"] += 1
            if decl.kind == "def" and decl.prop_valued and decl.sorried:
                counter["prop_stub"] += 1
    if args.json:
        json.dump(
            {g: dict(c) for g, c in sorted(table.items())}, sys.stdout, indent=2
        )
        sys.stdout.write("\n")
        return 0
    width = max((len(g) for g in table), default=10)
    print(
        f"{'module':{width}s} {'defs':>6s} {'stub':>6s} {'%':>5s} "
        f"{'thms':>6s} {'stub':>6s} {'%':>5s} {'Prop:=sorry':>12s}"
    )
    for group, c in sorted(table.items(), key=lambda kv: -kv[1]["def_stub"]):
        dt, ds = c["def_total"], c["def_stub"]
        tt, ts = c["theorem_total"], c["theorem_stub"]
        dp = f"{100 * ds / dt:.0f}%" if dt else "-"
        tp = f"{100 * ts / tt:.0f}%" if tt else "-"
        print(
            f"{group:{width}s} {dt:6d} {ds:6d} {dp:>5s} {tt:6d} {ts:6d} {tp:>5s} "
            f"{c['prop_stub']:12d}"
        )
    return 0


def cmd_deps(args) -> int:
    """What a declaration needs — directly, or transitively within the library."""
    project, library = _resolve(args)
    decls = ensure_index(project, library, refresh=args.refresh, verbose=not args.json)
    table = by_name(decls)
    if args.decl not in table:
        print(f"no declaration named {args.decl!r}", file=sys.stderr)
        return 1
    if args.transitive or args.local:
        found = closure(
            decls,
            args.decl,
            library=library if args.local else None,
            depth=0 if args.transitive else 1,
        )
    else:
        start = table[args.decl]
        found = sorted(
            (table[d] for d in start.deps if d in table),
            key=lambda d: (d.module, d.name),
        )
    _emit(found, args)
    return 0


def cmd_rdeps(args) -> int:
    """Which declarations reference this one."""
    args.uses = args.decl
    args.kind = getattr(args, "kind", None)
    args.name = None
    args.axiom = None
    args.sorried = getattr(args, "sorried", None)
    args.is_prop = None
    args.prop_valued = getattr(args, "prop_valued", None)
    return cmd_query(args)


@profile
def cmd_promotions(args) -> int:
    """Tagged declarations that a chosen production root actually depends on."""
    project, library = _resolve(args)
    roots = args.root or [library]
    decls = ensure_scoped_index(
        project, library, roots, refresh=args.refresh, verbose=not args.json, detail="deps"
    )
    tags = args.tag or list(DEFAULT_TAGS)
    report = promotion_report(
        decls, tags=tags, consumer_prefixes=args.consumer_prefix or ()
    )
    entries = list(report.entries)
    if args.boundary_only:
        entries = [entry for entry in entries if entry.role == "boundary"]
    if args.kind:
        entries = [entry for entry in entries if entry.decl.kind == args.kind]

    if args.json:
        payload = {
            "library": library,
            "roots": roots,
            "tags": list(report.tags),
            "consumerPrefixes": args.consumer_prefix or [],
            "scopeDeclarations": report.scope_declarations,
            "taggedReachableDeclarations": len(report.tagged_reachable),
            "taggedReachableTheorems": sum(
                decl.kind == "theorem" for decl in report.tagged_reachable
            ),
            "neededDeclarations": len(report.entries),
            "neededTheorems": report.count_kind("theorem"),
            "boundaryDeclarations": sum(e.role == "boundary" for e in report.entries),
            "boundaryTheorems": report.count_kind("theorem", role="boundary"),
            "rows": [entry.to_json() for entry in entries],
        }
        json.dump(payload, sys.stdout, indent=2)
        sys.stdout.write("\n")
        return 0

    print(f"roots: {', '.join(roots)}")
    print(f"tags: {', '.join(report.tags)}")
    print(f"root-scope declarations: {report.scope_declarations}")
    print(
        "tagged but reachable: "
        f"{len(report.tagged_reachable)} declaration(s), "
        f"{sum(d.kind == 'theorem' for d in report.tagged_reachable)} theorem(s)"
    )
    print(
        "actually needed across the boundary: "
        f"{len(report.entries)} declaration(s), "
        f"{report.count_kind('theorem')} theorem(s)"
    )
    print(
        "direct boundary: "
        f"{sum(e.role == 'boundary' for e in report.entries)} declaration(s), "
        f"{report.count_kind('theorem', role='boundary')} theorem(s)"
    )
    print()
    width = max((len(entry.decl.short_name) for entry in entries), default=0)
    for entry in entries:
        if args.names:
            print(entry.decl.name)
            continue
        consumers = ""
        if entry.direct_consumers:
            shown = ", ".join(entry.direct_consumers[:3])
            extra = len(entry.direct_consumers) - 3
            consumers = f"  <- {shown}" + (f" (+{extra})" if extra else "")
        print(
            f"{entry.role:8s} {entry.decl.kind:8s} "
            f"{entry.decl.short_name:{width}s}  {entry.decl.location()}{consumers}"
        )
    return 0

@profile
def cmd_graph(args) -> int:
    """Exact project-local declaration graph and optional interactive viewer."""
    project = find_project(Path(args.project) if args.project else None)
    presentation_spec = (
        load_presentation(Path(args.presentation)) if args.presentation else None
    )
    targets = list(args.target or ())
    if not targets and presentation_spec is not None:
        targets = list(presentation_spec.targets)
    if not targets:
        raise ProjectError(
            "graph needs at least one target declaration, either positionally or in --presentation"
        )

    root_modules = list(dict.fromkeys(args.root_module or ()))
    if not root_modules:
        root_modules = project.declaration_modules(targets)

    if args.include_lib:
        libraries = list(dict.fromkeys(args.include_lib))
    elif args.lib:
        libraries = [args.lib]
    else:
        libraries = project.libraries_for_import_closure(root_modules)
    excluded = set(args.exclude_lib or ())
    libraries = [library for library in libraries if library not in excluded]
    if not libraries:
        raise ProjectError("graph scope contains no libraries")

    groups = []
    for library in libraries:
        groups.append(
            ensure_scoped_index(
                project,
                library,
                root_modules,
                refresh=args.refresh,
                verbose=not args.json,
                detail="graph",
            )
        )
    table = merge_declarations(groups)
    graph = target_dependency_graph(table.values(), targets)
    need_reduction = args.transitive_reduction or bool(args.html)
    reduced = (
        transitive_reduction(graph.nodes, graph.edges) if need_reduction else None
    )
    payload = graph.to_json(reduced_edges=reduced)
    payload["project"] = str(project.root)
    payload["libraries"] = libraries
    payload["importRoots"] = root_modules
    payload["scope"] = "target-import-closure"
    components = strongly_connected_components(graph.nodes, graph.edges)
    cyclic = [list(component) for component in components if len(component) > 1]
    payload["cyclicComponentCount"] = len(cyclic)
    payload["cyclicComponents"] = cyclic
    if args.include_unresolved:
        payload["unresolvedDependencies"] = [
            {"consumer": consumer, "dependency": dependency}
            for consumer, dependency in graph.unresolved
        ]

    if presentation_spec is not None or args.headline:
        payload["presentation"] = build_presentation(
            graph,
            presentation_spec,
            extra_headlines=args.headline or (),
            title=args.title,
            subtitle=args.subtitle,
        )
    elif args.title or args.subtitle:
        payload["presentation"] = build_presentation(
            graph,
            None,
            title=args.title,
            subtitle=args.subtitle,
        )

    text = json.dumps(payload, indent=2) + "\n"
    written = []
    if args.out:
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding="utf-8")
        written.append(out)
    if args.html:
        html_path = Path(args.html)
        if args.out and html_path.resolve() == Path(args.out).resolve():
            raise ProjectError("--html and --out must name different files")
        write_graph_html(html_path, payload, title=args.title)
        written.append(html_path)

    if args.json:
        sys.stdout.write(text)
    elif written:
        for path in written:
            print(path)
    else:
        print(f"targets: {', '.join(graph.targets)}")
        print(f"libraries: {', '.join(libraries)}")
        print(f"nodes: {len(graph.nodes)}")
        print(f"direct edges: {len(graph.edges)}")
        if reduced is not None:
            print(f"transitive-reduction edges: {len(reduced)}")
        print(f"cyclic components: {len(cyclic)}")
        print(f"unresolved boundary dependencies: {len(graph.unresolved)}")
    return 0


def cmd_axioms(args) -> int:
    project, library = _resolve(args)
    decls = ensure_index(project, library, refresh=args.refresh, verbose=not args.json)
    matches = [d for d in decls if d.name == args.decl or d.short_name == args.decl]
    if not matches:
        print(f"no declaration named {args.decl!r}", file=sys.stderr)
        return 1
    if args.json:
        json.dump([d.to_json() for d in matches], sys.stdout, indent=2)
        sys.stdout.write("\n")
        return 0
    for decl in matches:
        print(f"{decl.name}  ({decl.kind}, {decl.module})")
        axioms = decl.axioms if decl.axioms is not None else ("(not indexed)",)
        for axiom in axioms or ("(none)",):
            print(f"    {axiom}")
    return 0


def cmd_libs(args) -> int:
    project = find_project(Path(args.project) if args.project else None)
    for library in project.built_roots():
        marker = " (indexed)" if index_path(project, library).exists() else ""
        print(f"{library}{marker}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="leanq",
        description=(
            "Query a built Lean 4 library from the elaborator. Declaration kinds, whether a "
            "definition returns Prop, and whether it depends on sorryAx are read out of the "
            "environment, so multi-line signatures and neighbouring declarations cannot skew "
            "the answer the way a regex does."
        ),
    )
    parser.add_argument("--project", help="path inside the Lean project (default: cwd)")
    parser.add_argument("--lib", help="library root module (default: the only built one)")
    parser.add_argument("--json", action="store_true", help="emit JSON")
    sub = parser.add_subparsers(dest="command", required=True)

    def add_common(sp) -> None:
        """`--json` reads naturally after the subcommand; accept it in both positions."""
        sp.add_argument(
            "--json", action="store_true", default=argparse.SUPPRESS, help="emit JSON"
        )


    p = sub.add_parser("libs", help="list built libraries")
    add_common(p)
    p.set_defaults(func=cmd_libs)

    p = sub.add_parser("index", help="build the declaration index")
    add_common(p)
    p.add_argument("--out", help="write the JSONL here instead of <project>/.leanq/")
    p.set_defaults(func=cmd_index)

    def add_query_flags(sp, *, with_sorried: bool = True) -> None:
        add_common(sp)
        sp.add_argument("--refresh", action="store_true", help="rebuild the index first")
        sp.add_argument("--kind", choices=["def", "theorem", "axiom", "inductive", "ctor"])
        sp.add_argument("--module", help="substring match on the module name")
        sp.add_argument("--name", help="substring match on the declaration name")
        sp.add_argument("--axiom", help="substring match within the axiom closure")
        sp.add_argument("--names", action="store_true", help="print bare names")
        sp.add_argument("--uses", help="only declarations referencing this constant")
        if with_sorried:
            group = sp.add_mutually_exclusive_group()
            group.add_argument(
                "--sorried", dest="sorried", action="store_const", const=True,
                help="only declarations depending on sorryAx",
            )
            group.add_argument(
                "--no-sorried", dest="sorried", action="store_const", const=False,
                help="only declarations free of sorryAx",
            )
            sp.set_defaults(sorried=None)
        pv = sp.add_mutually_exclusive_group()
        pv.add_argument(
            "--prop-valued", dest="prop_valued", action="store_const", const=True,
            help="only declarations returning Prop (predicates)",
        )
        pv.add_argument(
            "--not-prop-valued", dest="prop_valued", action="store_const", const=False,
        )
        sp.set_defaults(prop_valued=None, is_prop=None)

    p = sub.add_parser("query", help="filter declarations")
    add_query_flags(p)
    p.set_defaults(func=cmd_query)

    p = sub.add_parser("stubs", help="declarations that depend on sorryAx")
    add_query_flags(p, with_sorried=False)
    p.set_defaults(func=cmd_stubs)

    p = sub.add_parser("stats", help="per-module def/theorem stub counts")
    add_common(p)
    p.add_argument("--refresh", action="store_true")
    p.add_argument(
        "--depth", type=int, default=2,
        help="group modules by this many name components (0 = full module)",
    )
    p.set_defaults(func=cmd_stats)

    p = sub.add_parser(
        "deps", help="what a declaration references (--local: only same-library helpers)"
    )
    add_common(p)
    p.add_argument("decl", help="full or short declaration name")
    p.add_argument("--refresh", action="store_true")
    p.add_argument("--names", action="store_true")
    p.add_argument(
        "--transitive", action="store_true", help="follow dependencies all the way down"
    )
    p.add_argument(
        "--local", action="store_true",
        help="only declarations from this library, followed transitively -- the "
             "'what would I have to bring along' question",
    )
    p.set_defaults(func=cmd_deps)

    p = sub.add_parser("rdeps", help="declarations that reference this one")
    add_common(p)
    p.add_argument("decl", help="full or short declaration name")
    p.add_argument("--refresh", action="store_true")
    p.add_argument("--names", action="store_true")
    p.add_argument("--module")
    p.add_argument("--kind", choices=["def", "theorem", "axiom", "inductive", "ctor"])
    p.set_defaults(func=cmd_rdeps, sorried=None, prop_valued=None, is_prop=None)

    p = sub.add_parser(
        "promotions",
        help="tagged declarations actually required by declarations under a production root",
    )
    add_common(p)
    p.add_argument(
        "--root", action="append",
        help="root module to import (repeatable; default: the library root)",
    )
    p.add_argument(
        "--tag", action="append",
        help="exact module-name component treated as experimental (default: Experimental, MathAhead)",
    )
    p.add_argument(
        "--consumer-prefix", action="append",
        help="only count boundary users in modules with this prefix (repeatable)",
    )
    p.add_argument(
        "--kind", choices=["def", "theorem", "axiom", "inductive", "ctor"],
        help="filter displayed rows by declaration kind; summary remains unfiltered",
    )
    p.add_argument(
        "--boundary-only", action="store_true",
        help="show only declarations referenced directly from an untagged module",
    )
    p.add_argument("--refresh", action="store_true", help="rebuild the root-scoped index")
    p.add_argument("--names", action="store_true", help="print bare declaration names")
    p.set_defaults(func=cmd_promotions)

    p = sub.add_parser(
        "graph",
        help="project-local elaborated dependency graph for one or more target declarations",
    )
    add_common(p)
    p.add_argument(
        "target", nargs="*",
        help="full or unambiguous short declaration name; may come from --presentation instead",
    )
    p.add_argument(
        "--include-lib", action="append",
        help="library to include as graph nodes (repeatable; default: local libraries in the target module import closure)",
    )
    p.add_argument(
        "--root-module", action="append",
        help="module to import for the graph environment (repeatable; normally inferred from target declarations)",
    )
    p.add_argument(
        "--exclude-lib", action="append",
        help="remove a library from the default graph scope (repeatable)",
    )
    p.add_argument("--refresh", action="store_true", help="rebuild graph indexes first")
    p.add_argument(
        "--transitive-reduction", action="store_true",
        help="also emit a reachability-preserving reduced edge set",
    )
    p.add_argument(
        "--include-unresolved", action="store_true",
        help="include names outside the indexed project-local graph, e.g. Mathlib dependencies",
    )
    p.add_argument("--out", help="write the graph JSON payload to this path")
    p.add_argument(
        "--html", metavar="PATH",
        help="write a self-contained interactive HTML dependency viewer",
    )
    p.add_argument(
        "--presentation", metavar="JSON",
        help="curated exact-name presentation spec; may also provide graph targets",
    )
    p.add_argument(
        "--headline", action="append",
        help="add a declaration to the initial headline presentation (repeatable)",
    )
    p.add_argument("--title", help="override the viewer/presentation title")
    p.add_argument("--subtitle", help="override the viewer/presentation subtitle")
    p.set_defaults(func=cmd_graph)

    p = sub.add_parser("axioms", help="axiom closure of one declaration")
    add_common(p)
    p.add_argument("decl", help="full or short declaration name")
    p.add_argument("--refresh", action="store_true")
    p.set_defaults(func=cmd_axioms)

    return parser


@profile
def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except ProjectError as exc:
        print(f"leanq: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
