#!/bin/bash
# Write the semantic-alignment review as one self-contained HTML page, and open it.
#
# The page pairs each census row's source statement and clauses with the Lean
# declarations that answer it. Nothing is served: the result is a single file,
# mailable, and readable with no tooling installed at the other end. For the
# live version -- every viewer under one shell, cross-ledger search, annotation,
# and reload when a ledger changes -- use ./semantic-alignment-server.sh.
#
# By default the page is built from the censuses alone, which needs no Lean and
# takes seconds -- nothing has to be built first. The two richer panels are the
# only things that do, and they are opt-in because they are slow:
#
#   --statements   elaborated signatures and pin status (invokes Lean, so the
#                  libraries must be built: about 90s warm)
#   --graph        the proof-dependency panel, from a saved leanq graph index
#                  (built by `leanq graph-index`, about ten minutes)
#
# --build does that preparation for you. Without it the script says what it
# found: a missing input is left out of the page, and one older than the Lean
# sources is included and labelled stale rather than shown as current.
#
# Usage:
#   ./semantic-alignment-page.sh [options] [census.json ...]
#
# Options:
#   --build               build what the requested panels need before rendering:
#                         `lake build`, and a leanq graph index when --graph is
#                         asked for and is missing or older than the sources.
#                         With no panel requested it turns both on, because a
#                         page with neither needs no build at all.
#   --statements          build/refresh the leanq statement sidecar (slow: runs Lean)
#   --graph [FILE]        add the proof-dependency panel
#                         (default: build/leanq/project-semantic-graph.json)
#   --importance LEVEL    headline | major | supporting | technical  (default: headline)
#   --title TEXT          page title
#   -o, --out FILE        output path (default: build/semantic-alignment/review.html)
#   --no-open             build only; do not launch a browser
#   -h, --help            this message
#
# With no census arguments, every dev/*-full-source-census.json is included.

set -euo pipefail

cd "$(dirname "$0")"

OUT="build/semantic-alignment/review.html"
IMPORTANCE="headline"
TITLE="Semantic alignment review"
GRAPH=""
DEFAULT_GRAPH="build/leanq/project-semantic-graph.json"
STATEMENTS=0
BUILD=0
OPEN=1
CENSUSES=()

usage() { sed -n '2,${/^#/!q;s/^# \{0,1\}//;p}' "$0"; }

while [ $# -gt 0 ]; do
    case "$1" in
        --build) BUILD=1; shift ;;
        --statements) STATEMENTS=1; shift ;;
        --graph=*) GRAPH="${1#--graph=}"; shift ;;
        --graph)
            # Optional value: the next token counts as the graph path unless it
            # is an option or a census argument. A missing file warns later
            # rather than being silently taken for a census.
            if [ $# -ge 2 ] && [ "${2#-}" = "$2" ] && [ "${2%full-source-census.json}" = "$2" ]; then
                GRAPH="$2"; shift 2
            else
                GRAPH="$DEFAULT_GRAPH"; shift
            fi ;;
        --importance) IMPORTANCE="$2"; shift 2 ;;
        --title) TITLE="$2"; shift 2 ;;
        -o|--out) OUT="$2"; shift 2 ;;
        --no-open) OPEN=0; shift ;;
        -h|--help) usage; exit 0 ;;
        --serve)
            echo "the server moved to its own command: ./semantic-alignment-server.sh" >&2
            exit 2 ;;
        -*) echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
        *) CENSUSES+=("$1"); shift ;;
    esac
done

if [ ${#CENSUSES[@]} -eq 0 ]; then
    for c in dev/*-full-source-census.json; do CENSUSES+=("$c"); done
fi

for c in "${CENSUSES[@]}"; do
    [ -f "$c" ] || { echo "no such census: $c" >&2; exit 2; }
done

# A Lean source newer than the index means the index describes declarations that
# may since have been renamed or removed -- the drift this page exists to catch,
# so it is never presented as current.
graph_stale() {
    [ -f "$1" ] || return 0
    [ -n "$(find . -name '*.lean' -newer "$1" -not -path './.lake/*' \
              -not -path './submodules/*' -print -quit 2>/dev/null)" ]
}

if [ "$BUILD" -eq 1 ]; then
    # A page with neither rich panel reads nothing that has to be built, so
    # --build on its own would spend ninety seconds to change nothing.
    if [ "$STATEMENTS" -eq 0 ] && [ -z "$GRAPH" ]; then
        echo "--build with no panel requested: turning on --statements and --graph."
        STATEMENTS=1
        GRAPH="$DEFAULT_GRAPH"
    fi
    echo "Building the Lean libraries (about 90s warm; do not run this while the"
    echo "gate suite is running -- several gates invoke lake and will fail)."
    if ! lake build; then
        cat >&2 <<'EOF'

The Lean build failed, so nothing was rendered: the elaborated signatures and
the dependency graph would describe a tree that does not compile, and a page
that presents them as evidence is worse than one without them.

Fix the build, or render the census-only page, which needs no Lean at all:

    ./semantic-alignment-page.sh

EOF
        exit 1
    fi
    if [ -n "$GRAPH" ] && graph_stale "$GRAPH"; then
        echo
        echo "Building the dependency graph index at $GRAPH (about ten minutes)."
        mkdir -p "$(dirname "$GRAPH")"
        leanq graph-index --out "$GRAPH"
    elif [ -n "$GRAPH" ]; then
        echo "Dependency graph index is current: $GRAPH"
    fi
    echo
fi

if ! command -v aiq-lean >/dev/null 2>&1; then
    cat >&2 <<'EOF'
aiq-lean is not on PATH. The alignment renderer lives in the tools package:

    python3 -m pip install -e submodules/aiq-lean-formalization-tools

EOF
    exit 127
fi

ARGS=(alignment html "${CENSUSES[@]}" --importance "$IMPORTANCE" --title "$TITLE" -o "$OUT")

if [ "$STATEMENTS" -eq 1 ]; then
    ARGS+=(--statements)
    # The statement sidecar imports the modules its seeds are declared in. A
    # built Challenge library declares the same names as the library modules it
    # mirrors, and the two collide at import ("environment already contains
    # ..."). Challenge is not a default target, so this only bites after an
    # explicit `lake build Challenge`.
    if [ -d .lake/build/lib/lean/Challenge ]; then
        cat >&2 <<'EOF'
warning: .lake/build/lib/lean/Challenge is built.

  Challenge mirrors library declaration names by convention, so the statement
  sidecar can fail on a duplicate-name import. If this run fails that way, move
  those build artifacts aside and retry:

      mv .lake/build/lib/lean/Challenge /tmp/challenge-olean-backup

  then move them back when you are done.

EOF
    fi
fi

if [ -n "$GRAPH" ]; then
    if [ ! -f "$GRAPH" ]; then
        cat >&2 <<EOF
warning: no graph index at $GRAPH -- building without the proof-dependency panel.
  Build one with:  leanq graph-index --out $GRAPH
  or re-run this script with --build.

EOF
    elif graph_stale "$GRAPH"; then
        cat >&2 <<EOF
warning: $GRAPH is older than a Lean source, so it may name declarations that
  have since been renamed. The panel is included and says it is stale.
  Rebuild with:  leanq graph-index --out $GRAPH
  or re-run this script with --build.

EOF
        ARGS+=(--graph "$GRAPH")
    else
        ARGS+=(--graph "$GRAPH")
    fi
fi

mkdir -p "$(dirname "$OUT")"
aiq-lean "${ARGS[@]}"

[ -s "$OUT" ] || { echo "renderer wrote nothing to $OUT" >&2; exit 1; }

echo
echo "Semantic alignment review built:"
echo
echo "    $OUT  ($(du -h "$OUT" | cut -f1))"
echo

[ "$OPEN" -eq 1 ] || exit 0

ABS="$PWD/$OUT"
for opener in ${BROWSER:-} xdg-open google-chrome chromium firefox open; do
    if command -v "$opener" >/dev/null 2>&1; then
        echo "Opening with $opener ..."
        "$opener" "$ABS" >/dev/null 2>&1 &
        exit 0
    fi
done

cat <<EOF
No browser launcher found. Open it yourself:

    xdg-open $ABS

EOF
