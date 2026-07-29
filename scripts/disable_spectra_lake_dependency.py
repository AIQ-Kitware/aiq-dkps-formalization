#!/usr/bin/env python3
"""RETIRED 2026-07-28 — refuses to run.  See dev/tauceti/spectra-removal-plan.md.

This script targeted the marker ``# BEGIN local Spectra development dependency``
and a Lake requirement of ``path = "external/Spectra"``.  Neither exists any
more: the build takes Spectra from the vendored snapshot
(``# BEGIN vendored upstream Spectra snapshot``, ``path = "vendor/Spectra"``) and
``external/Spectra`` is a read-only provenance reference that is deliberately
*not* a build input (``vendor/Spectra.UPSTREAM.md``).

It was not merely inert.  It **exited 0 while changing nothing** — so a
"disable Spectra and confirm the build still works" check passed without ever
disabling anything.  For a campaign whose whole purpose is removing this
dependency, a verification step that silently succeeds is the worst available
failure mode, which is why this is now a hard error rather than a repair.

To measure removal progress, use the real instruments:

    lake env lean --run scripts/ExportSpectraUsage.lean | wc -l   # target 0
    python3 scripts/check_spectra_namespace.py
    python3 scripts/check_spectra_vendor_authorship.py

The dependency block is removed by hand in phase S6, once that count is zero.
"""

import sys

sys.exit(__doc__)
