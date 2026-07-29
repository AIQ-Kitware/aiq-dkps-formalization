#!/usr/bin/env bash
# RETIRED 2026-07-28 -- refuses to run.  See dev/tauceti/spectra-removal-plan.md.
#
# This checked a "parent-only bridge" experiment via two scripts that no longer
# exist (remove_spectra_submodule_bridge_experiment.py,
# apply_spectra_lightweight_bridge_fix.py) and built
# DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.* modules that are
# also gone.  It aborted on the first missing script, so it failed loudly rather
# than passing falsely -- but it was dead weight in the one area where a stale
# verification tool is most dangerous.
#
# The Spectra-facing invariants that are actually checked now:
#   python3 scripts/check_spectra_namespace.py
#   python3 scripts/check_spectra_vendor_authorship.py
#   python3 scripts/spectra_port_surface.py build/spectra_direct_uses.jsonl --check

echo "check_spectra_parent_only_bridge.sh is retired; see dev/tauceti/spectra-removal-plan.md" >&2
exit 1
