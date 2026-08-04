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

from .index import (
    Decl,
    build_index,
    by_name,
    closure,
    ensure_index,
    filter_decls,
    index_path,
)
from .project import ProjectError, find_project


def _tristate(args, flag: str) -> bool | None:
    value = getattr(args, flag, None)
    return value


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
                "S" if decl.sorried else "-",
                "P" if decl.prop_valued else "-",
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
        for axiom in decl.axioms or ("(none)",):
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

    p = sub.add_parser("axioms", help="axiom closure of one declaration")
    add_common(p)
    p.add_argument("decl", help="full or short declaration name")
    p.add_argument("--refresh", action="store_true")
    p.set_defaults(func=cmd_axioms)

    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except ProjectError as exc:
        print(f"leanq: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
