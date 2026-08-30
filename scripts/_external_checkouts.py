#!/usr/bin/env python3
"""Resolve optional external Tau Ceti / roadmap / review checkouts.

The ordinary DKPS build does not depend on any checkout under `external/` or
`submodules/`. Tau Ceti itself is a pinned Lake dependency. An editable Tau Ceti
worktree and the tracked roadmap/review coordination repositories are optional
inputs for export, provenance, and review tooling only.

Resolution order is explicit argument, environment variable, conventional local or
coordination path, then -- for read-only Tau Ceti uses only -- the Lake package
checkout. A checker whose optional external input is absent must report
`SKIP` / `UNAVAILABLE` honestly.

`external/TauCeti` is retained as an untracked compatibility path for developers who
already keep an editable checkout there. `submodules/TauCetiRoadmap` and
`submodules/TauCetiReview` may be tracked coordination checkouts, but nothing in the
ordinary build requires them initialized.
"""
from __future__ import annotations

import os
import pathlib

#: Distinguished exit status meaning "this check did not run: an external input it
#: needs is absent". `scripts/run_gates.py` reports it separately from pass and
#: fail, because an unavailable check is neither.
EXIT_UNAVAILABLE = 3

ROOT = pathlib.Path(__file__).resolve().parents[1]

TAUCETI_ENV = "TAUCETI_ROOT"
ROADMAP_ENV = "TAUCETI_ROADMAP_ROOT"
REVIEW_ENV = "TAUCETI_REVIEW_ROOT"

#: Conventional optional checkout paths. The names are retained for compatibility.
LEGACY_TAUCETI = ROOT / "external/TauCeti"
LEGACY_ROADMAP = ROOT / "submodules/TauCetiRoadmap"
LEGACY_REVIEW = ROOT / "submodules/TauCetiReview"

#: Read-only Tau Ceti source, materialised by `lake`. Never an export target: it is
#: Lake's cache, it is not a Git working tree anyone should commit into, and
#: `lake update` may replace it without warning.
LAKE_TAUCETI = ROOT / ".lake/packages/TauCeti"


class MissingCheckout(RuntimeError):
    """Raised when an operation genuinely requires a checkout and none was found."""


def _populated(path: pathlib.Path | None) -> bool:
    return path is not None and path.is_dir() and any(path.iterdir())


def tauceti_root(
    explicit: str | pathlib.Path | None = None,
    *,
    require_editable: bool = False,
    required: bool = False,
) -> pathlib.Path | None:
    """Locate a Tau Ceti checkout.

    `require_editable` excludes the Lake package copy: an export writes files and
    expects a Git working tree the operator controls, which Lake's cache is not.
    `required` turns "not found" into `MissingCheckout` instead of `None`.
    """
    candidates: list[pathlib.Path] = []
    if explicit:
        candidates.append(pathlib.Path(explicit).expanduser().resolve())
    env = os.environ.get(TAUCETI_ENV)
    if env:
        candidates.append(pathlib.Path(env).expanduser().resolve())
    candidates.append(LEGACY_TAUCETI)
    if not require_editable:
        candidates.append(LAKE_TAUCETI)

    for candidate in candidates:
        if _populated(candidate):
            return candidate

    if required:
        what = "an editable Tau Ceti checkout" if require_editable else "a Tau Ceti checkout"
        raise MissingCheckout(
            f"this operation needs {what}, and none was found.\n"
            f"  pass --tauceti-root PATH, or set {TAUCETI_ENV}=PATH.\n"
            f"  clone it with: git clone https://github.com/TauCetiProject/TauCeti.git\n"
            f"  the revision this repository builds against is pinned in lake-manifest.json."
            + ("" if require_editable else
               f"\n  (read-only uses may also use {LAKE_TAUCETI}, populated by `lake build`.)")
        )
    return None


def roadmap_root(
    explicit: str | pathlib.Path | None = None, *, required: bool = False
) -> pathlib.Path | None:
    """Locate a TauCetiRoadmap checkout (read-only review surface)."""
    return _simple_root(
        explicit, LEGACY_ROADMAP, ROADMAP_ENV, "--roadmap-root",
        "https://github.com/Erotemic/TauCetiRoadmap.git", required,
    )


def review_root(
    explicit: str | pathlib.Path | None = None, *, required: bool = False
) -> pathlib.Path | None:
    """Locate a TauCetiReview checkout (read-only review surface)."""
    return _simple_root(
        explicit, LEGACY_REVIEW, REVIEW_ENV, "--review-root",
        "https://github.com/TauCetiProject/TauCetiReview.git", required,
    )


def _simple_root(explicit, legacy, env_name, flag, clone_url, required):
    candidates = []
    if explicit:
        candidates.append(pathlib.Path(explicit).expanduser().resolve())
    env = os.environ.get(env_name)
    if env:
        candidates.append(pathlib.Path(env).expanduser().resolve())
    candidates.append(legacy)
    for candidate in candidates:
        if _populated(candidate):
            return candidate
    if required:
        raise MissingCheckout(
            f"this operation needs a checkout of {clone_url}, and none was found.\n"
            f"  pass {flag} PATH, or set {env_name}=PATH."
        )
    return None


def skip_note(what: str, flag: str, env_name: str) -> str:
    """The one-line message a checker prints when it skips for want of a checkout."""
    return (
        f"SKIP: {what} is unavailable; pass {flag} PATH or set {env_name}=PATH. "
        f"This is not a pass -- the check did not run."
    )
