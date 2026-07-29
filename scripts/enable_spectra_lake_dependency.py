#!/usr/bin/env python3
"""RETIRED 2026-07-28 — refuses to run.  See dev/tauceti/spectra-removal-plan.md.

This script inserted a Lake requirement of ``path = "external/Spectra"`` under the
marker ``# BEGIN local Spectra development dependency``.  Running it today would
not be a no-op: it would repoint the build at the read-only provenance submodule
and *undo the vendoring architecture*, which deliberately builds from
``vendor/Spectra`` and keeps ``external/Spectra`` out of the build
(``vendor/Spectra.UPSTREAM.md``).

The ordering constraint it documented is still real and still enforced by the
lakefile itself: the authoritative root Mathlib ``[[require]]`` must come last,
after Spectra and Tau Ceti, because Spectra pins an older dependency graph.  That
comment now lives in ``lakefile.toml`` where it applies.
"""

import sys

sys.exit(__doc__)
