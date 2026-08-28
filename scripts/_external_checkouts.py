#!/usr/bin/env python3
"""Resolve optional external Tau Ceti checkouts.

This repository used to carry three Git submodules — `external/TauCeti`,
`submodules/TauCetiRoadmap` and `submodules/TauCetiReview`. They are gone, because
Lake fetches a Git dependency with a plain clone and does not initialise
submodules: a path dependency into a gitlink makes this repository unusable as a
dependency of anything else, including a Palomar thin-wrapper submission repo.
See `dev/palomar-readiness.md`.

What the submodules provided is now an *optional* input. The build never needs
one: Tau Ceti arrives as a pinned Lake dependency. Only three kinds of work need a
real checkout, and each says so explicitly:

  * exporting staged `ForTauCeti` modules upstream (needs an **editable** checkout);
  * reading upstream Git provenance for an audit certificate (read-only);
  * validating this repository against the roadmap / review surfaces (read-only).

Resolution order is the same everywhere: an explicit argument, then an environment
variable, then the historical in-repository path if someone still has one
populated, then — for Tau Ceti read-only uses only — the Lake package checkout.

A checker whose external reference is absent must report `SKIP` / `UNAVAILABLE`
honestly. Making a gate green by deleting the thing it checks is not allowed.
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

#: Where the submodules used to live. Still honoured when populated, so a working
#: copy that predates the removal keeps working.
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
