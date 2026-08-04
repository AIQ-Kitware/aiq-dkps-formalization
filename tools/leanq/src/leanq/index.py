"""Building and loading the declaration index."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator

from .project import LeanProject, ProjectError

LEAN_SCRIPT = Path(__file__).with_name("lean") / "decl_index.lean"


@dataclass(frozen=True)
class Decl:
    """One declaration, as the elaborator sees it."""

    name: str
    module: str
    kind: str
    is_prop: bool
    prop_valued: bool
    sorried: bool
    line: int
    axioms: tuple[str, ...]
    deps: tuple[str, ...]

    @classmethod
    def from_json(cls, obj: dict) -> "Decl":
        return cls(
            name=obj["name"],
            module=obj["module"],
            kind=obj["kind"],
            is_prop=obj["isProp"],
            prop_valued=obj["propValued"],
            sorried=obj["sorried"],
            line=obj.get("line", 0),
            axioms=tuple(obj.get("axioms", ())),
            deps=tuple(obj.get("deps", ())),
        )

    def to_json(self) -> dict:
        return {
            "name": self.name,
            "module": self.module,
            "kind": self.kind,
            "isProp": self.is_prop,
            "propValued": self.prop_valued,
            "sorried": self.sorried,
            "line": self.line,
            "axioms": list(self.axioms),
            "deps": list(self.deps),
        }

    @property
    def short_name(self) -> str:
        return self.name.rsplit(".", 1)[-1]

    def location(self) -> str:
        """`path:line`, clickable in most terminals."""
        path = "/".join(self.module.split(".")) + ".lean"
        return f"{path}:{self.line}" if self.line else path


def index_path(project: LeanProject, library: str) -> Path:
    """Where the index is cached.

    Defaults to ``<project>/.leanq``. Set ``LEANQ_CACHE_DIR`` to keep generated files out of a
    project you do not own -- a git submodule, for instance, where an untracked directory shows
    up as a dirty worktree in the parent repository.
    """
    base = os.environ.get("LEANQ_CACHE_DIR")
    if base:
        return Path(base) / project.root.name / f"{library}.jsonl"
    return project.root / ".leanq" / f"{library}.jsonl"


def build_index(
    project: LeanProject,
    library: str,
    *,
    out: Path | None = None,
    timeout: int = 3600,
    verbose: bool = True,
) -> Path:
    """Run the Lean metaprogram and write a JSONL index.

    Every built module of the library is imported explicitly.  Importing only the root would
    quietly index nothing for modules the root does not import, and a confident zero is a worse
    answer than an obvious error.
    """
    modules = project.modules(library)
    if project.stale_modules and verbose:
        print(
            f"leanq: skipping {len(project.stale_modules)} stale artifact(s) with no source, "
            f"e.g. {project.stale_modules[0]}",
            file=sys.stderr,
        )
    out = out or index_path(project, library)
    out.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as handle:
        handle.write("\n".join(modules))
        modules_file = handle.name

    cmd = ["lake", "env", "lean", "--run", str(LEAN_SCRIPT), library, modules_file]
    if verbose:
        print(
            f"leanq: indexing {len(modules)} module(s) of {library} "
            f"in {project.root}",
            file=sys.stderr,
        )
    try:
        proc = subprocess.run(
            cmd,
            cwd=project.root,
            capture_output=True,
            text=True,
            timeout=timeout,
            env={**os.environ, "LEAN_NUM_THREADS": os.environ.get("LEAN_NUM_THREADS", "4")},
        )
    finally:
        os.unlink(modules_file)

    stdout = proc.stdout or ""
    records = [line for line in stdout.splitlines() if line.startswith("{")]
    junk = [line for line in stdout.splitlines() if line and not line.startswith("{")]
    if proc.returncode != 0 and not records:
        detail = (proc.stderr or "").strip() or "\n".join(junk[:20]) or "(no output)"
        raise ProjectError(f"lean exited {proc.returncode}:\n{detail}")
    if junk and verbose:
        print(f"leanq: {len(junk)} non-record line(s) from lean, first:", file=sys.stderr)
        print(f"  {junk[0][:200]}", file=sys.stderr)

    out.write_text("\n".join(records) + ("\n" if records else ""), encoding="utf-8")
    if verbose:
        print(f"leanq: wrote {len(records)} declaration(s) to {out}", file=sys.stderr)
    return out


def load_index(path: Path) -> list[Decl]:
    if not path.exists():
        raise ProjectError(f"no index at {path}; run `leanq index` first")
    decls = []
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                decls.append(Decl.from_json(json.loads(line)))
    return decls


def ensure_index(
    project: LeanProject, library: str, *, refresh: bool = False, verbose: bool = True
) -> list[Decl]:
    path = index_path(project, library)
    if refresh or not path.exists():
        build_index(project, library, out=path, verbose=verbose)
    return load_index(path)


def filter_decls(
    decls: Iterable[Decl],
    *,
    kind: str | None = None,
    sorried: bool | None = None,
    prop_valued: bool | None = None,
    is_prop: bool | None = None,
    module: str | None = None,
    name: str | None = None,
    axiom: str | None = None,
    uses: str | None = None,
) -> Iterator[Decl]:
    """Apply the CLI's filters.  ``module`` and ``name`` are substring matches."""
    for decl in decls:
        if kind is not None and decl.kind != kind:
            continue
        if sorried is not None and decl.sorried != sorried:
            continue
        if prop_valued is not None and decl.prop_valued != prop_valued:
            continue
        if is_prop is not None and decl.is_prop != is_prop:
            continue
        if module is not None and module not in decl.module:
            continue
        if name is not None and name not in decl.name:
            continue
        if axiom is not None and not any(axiom in a for a in decl.axioms):
            continue
        if uses is not None and not any(
            d == uses or d.rsplit(".", 1)[-1] == uses for d in decl.deps
        ):
            continue
        yield decl


def by_name(decls: Iterable[Decl]) -> dict[str, Decl]:
    """Index by full name, with short names as a fallback key."""
    table: dict[str, Decl] = {}
    for decl in decls:
        table[decl.name] = decl
        table.setdefault(decl.short_name, decl)
    return table


def closure(
    decls: Iterable[Decl], root: str, *, library: str | None = None, depth: int = 0
) -> list[Decl]:
    """Everything ``root`` transitively needs, restricted to declarations we have.

    With ``library`` set, only declarations from that library are followed, which is the
    "what would I have to bring along" question: dependencies on Mathlib are already available
    wherever the declaration is restated, local helpers are not.
    """
    table = by_name(decls)
    start = table.get(root)
    if start is None:
        return []
    seen: dict[str, Decl] = {}
    frontier = [(start, 0)]
    while frontier:
        decl, level = frontier.pop()
        for dep in decl.deps:
            target = table.get(dep) or table.get(dep.rsplit(".", 1)[-1])
            if target is None or target.name in seen or target.name == start.name:
                continue
            if library is not None and not target.module.startswith(library):
                continue
            seen[target.name] = target
            if depth == 0 or level + 1 < depth:
                frontier.append((target, level + 1))
    return sorted(seen.values(), key=lambda d: (d.module, d.name))
