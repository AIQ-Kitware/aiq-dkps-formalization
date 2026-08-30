#!/usr/bin/env bash
# Verify a prepared Palomar Registry entry locally.
#
# This runs the checks we can run here. It is NOT Palomar's verification, it never
# contacts the registry, and passing it establishes nothing about acceptance.
# Registration is permanent and is a maintainer decision; see
# dev/palomar-readiness.md.
#
# Usage:
#   scripts/verify_palomar.sh                 # every entry under registry/
#   scripts/verify_palomar.sh yws-2015        # one entry
#   scripts/verify_palomar.sh --all
#   scripts/verify_palomar.sh yws-2015 --fake-landrun
#   scripts/verify_palomar.sh yws-2015 --static-only
#
# Four stages, cheapest first, each a real check rather than a proxy for one:
#
#   1. static preflight       scripts/check_palomar_readiness.py -- submodules,
#                             manifest pins, metadata shape, comparator keys, and
#                             the Challenge import closure
#   2. build                  lake build Palomar
#   3. signature pre-flight   scripts/check_comparator_signatures.py -- catches the
#                             universe-slot and instance-telescope drift that builds
#                             green and still fails the real exporter. Seconds, not
#                             minutes; see
#                             dev/journals/comparator-statement-export-matching-2026-06-14.md
#   4. comparator + NanoDa    scripts/run_challenge_comparator.sh, which is the
#                             existing runner and remains ground truth
#
# Stage 4 needs the external tools. Install them once with
#   bash scripts/install_comparator_tools.sh
# and see docs/challenge/comparator-tools.md. Without them this script says so and
# fails rather than quietly reporting success from the first three stages.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ENTRIES=()
PASSTHRU=()
STATIC_ONLY=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --all) ;;
        --static-only) STATIC_ONLY=1 ;;
        --fake-landrun|--only-comparator) PASSTHRU+=("$1") ;;
        -h|--help) sed -n '2,35p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
        -*) echo "unknown option: $1" >&2; exit 2 ;;
        *) ENTRIES+=("$1") ;;
    esac
    shift
done

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    while IFS= read -r cfg; do
        ENTRIES+=("$(basename "$(dirname "$cfg")")")
    done < <(find registry -mindepth 2 -maxdepth 2 -name comparator.json | sort)
fi

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    echo "no entries found under registry/*/comparator.json" >&2
    exit 2
fi

FAILED=()

for entry in "${ENTRIES[@]}"; do
    cfg="registry/$entry/comparator.json"
    echo "======================================================================"
    echo "palomar entry: $entry"
    echo "======================================================================"
    if [[ ! -f "$cfg" ]]; then
        echo "  no such entry: $cfg" >&2
        FAILED+=("$entry (missing config)")
        continue
    fi

    ok=1

    echo "--- 1/4 static preflight"
    python3 scripts/check_palomar_readiness.py --entry "$entry" || ok=0

    echo "--- 2/4 lake build Palomar"
    lake build Palomar || ok=0

    echo "--- 3/4 signature pre-flight"
    python3 scripts/check_comparator_signatures.py --no-build "$cfg" || ok=0

    if [[ $STATIC_ONLY -eq 1 ]]; then
        echo "--- 4/4 comparator: skipped (--static-only)"
        echo "    Not a pass. The exporter is ground truth and did not run."
    else
        echo "--- 4/4 comparator + NanoDa"
        if ! command -v comparator >/dev/null 2>&1; then
            echo "    comparator is not on PATH."
            echo "    Install once: bash scripts/install_comparator_tools.sh"
            echo "    See docs/challenge/comparator-tools.md."
            ok=0
        else
            bash scripts/run_challenge_comparator.sh --config "$cfg" \
                ${PASSTHRU[@]+"${PASSTHRU[@]}"} || ok=0
        fi
    fi

    [[ $ok -eq 1 ]] || FAILED+=("$entry")
    echo
done

echo "======================================================================"
if [[ ${#FAILED[@]} -eq 0 ]]; then
    echo "palomar verify: OK for ${#ENTRIES[@]} entry/entries"
    echo
    echo "  Locally verified only. This is not Palomar verification, not"
    echo "  acceptance, and not registration. The maintainer reviews the prepared"
    echo "  commit and submits; an agent must not."
    exit 0
fi
echo "palomar verify: FAILED for ${#FAILED[@]} of ${#ENTRIES[@]}: ${FAILED[*]}"
exit 1
