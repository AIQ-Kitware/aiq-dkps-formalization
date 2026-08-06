"""Locating a Lean project and enumerating what it actually built.

Nothing here parses Lean source.  A project is found by walking up to a ``lakefile``, and its
modules are read off the ``.lake`` build tree, so the index describes what exists rather than
what someone hoped exists.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

LAKEFILES = ("lakefile.toml", "lakefile.lean")


class ProjectError(RuntimeError):
    """Raised when a project cannot be located or is not built."""


@dataclass
class LeanProject:
    """A Lake project on disk."""

    root: Path

    @property
    def lakefile(self) -> Path:
        for name in LAKEFILES:
            candidate = self.root / name
            if candidate.exists():
                return candidate
        raise ProjectError(f"no lakefile under {self.root}")

    @property
    def build_lib(self) -> Path:
        # `.lake` is frequently a symlink to a cache outside the repo; resolve() follows it.
        return (self.root / ".lake" / "build" / "lib" / "lean").resolve()

    def libraries(self) -> list[str]:
        """Library root names declared by the lakefile, best effort.

        Falls back to the top-level names present in the build tree, which is what actually
        matters for indexing.
        """
        text = self.lakefile.read_text(encoding="utf-8")
        names = re.findall(r"^\s*name\s*=\s*[\"']?([A-Za-z_][A-Za-z0-9_']*)", text, re.M)
        names += re.findall(r"lean_lib\s+[«]?([A-Za-z_][A-Za-z0-9_']*)", text)
        seen = {n for n in names if n not in {"mathlib", "batteries"}}
        built = set(self.built_roots())
        ordered = [n for n in seen if n in built] or sorted(built)
        return sorted(set(ordered))

    def built_roots(self) -> list[str]:
        """Top-level module names with compiled artifacts."""
        lib = self.build_lib
        if not lib.is_dir():
            return []
        roots = set()
        for olean in lib.glob("*.olean"):
            roots.add(olean.stem)
        for child in lib.iterdir():
            if child.is_dir() and any(child.rglob("*.olean")):
                roots.add(child.name)
        return sorted(roots)

    def modules(self, library: str) -> list[str]:
        """Every built module under ``library``, as dotted module names.

        Read from ``.olean`` paths rather than from imports: a library's root module is not
        required to import the library.  ``TauCetiRoadmap.lean`` omits an entire roadmap that
        the lakefile globs in, so an import-following walk would silently miss it.
        """
        lib = self.build_lib
        if not lib.is_dir():
            raise ProjectError(
                f"{self.root} has no build tree at {lib}; run `lake build` first"
            )
        mods = []
        root_olean = lib / f"{library}.olean"
        if root_olean.exists():
            mods.append(library)
        subdir = lib / library
        if subdir.is_dir():
            for olean in sorted(subdir.rglob("*.olean")):
                rel = olean.relative_to(lib).with_suffix("")
                mods.append(".".join(rel.parts))
        if not mods:
            raise ProjectError(
                f"no built modules for library {library!r} under {lib}; "
                f"available: {', '.join(self.built_roots()) or '(none)'}"
            )
        live, stale = self._split_stale(sorted(set(mods)))
        self._stale = stale
        return live

    def source_of(self, module: str) -> Path:
        """Where a module's source would live, by the standard layout."""
        return self.root.joinpath(*module.split(".")).with_suffix(".lean")

    def _split_stale(self, mods: list[str]) -> tuple[list[str], list[str]]:
        """Drop modules whose source is gone.

        `lake` does not delete the `.olean` of a module you renamed or removed, so the build
        tree accumulates artifacts that no longer correspond to anything.  Importing one
        alongside its replacement fails outright -- two modules claiming the same constant --
        which is how the `UnitarilyInvariantNorm` -> `...Seminorm` rename surfaced.  If no
        module resolves to a source file the layout is non-standard, so filter nothing.
        """
        live = [m for m in mods if self.source_of(m).exists()]
        if not live:
            return mods, []
        stale = [m for m in mods if not self.source_of(m).exists()]
        return live, stale

    @property
    def stale_modules(self) -> list[str]:
        return list(getattr(self, "_stale", []))


def find_project(start: Path | None = None) -> LeanProject:
    """Walk up from ``start`` until a lakefile appears."""
    here = (start or Path.cwd()).resolve()
    for candidate in (here, *here.parents):
        if any((candidate / name).exists() for name in LAKEFILES):
            return LeanProject(candidate)
    raise ProjectError(f"no lakefile at or above {here}")
