#!/bin/bash
# Open the semantic-alignment review in a browser.
#
# Two modes. `--serve` runs the live server: every viewer under one shell, with
# search across all the ledgers at once, annotation, and a reload when a ledger
# changes on disk. Without it, a static self-contained page is written instead
# -- no server, mailable, and what the review packets are generated from.
#
# The page pairs each census row's source statement and clauses with the Lean
# declarations that answer it. By default it is built from the censuses alone,
# which needs no Lean and takes seconds. The two richer panels are opt-in
# because they are slow:
#
#   --statements   elaborated signatures and pin status (invokes Lean)
#   --graph        the proof-dependency panel, from a saved leanq graph index
#
# --serve needs the optional FastAPI extra. It looks for an aiq-lean in
# $AIQ_SERVE_VENV (default /home/agent/venvs/aiq-serve) and otherwise falls back
# to PATH, which prints the install line if the extra is missing.
#
# Usage:
#   ./launch_semantic_alignment_browser.sh [options] [census.json ...]
#
# Options:
#   --serve               run the live server instead of writing a static page:
#                         every viewer under one shell, cross-ledger search,
#                         annotation, and reload when a ledger changes on disk
#   --port N              port for --serve (default: 8800)
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

SERVE=0
PORT=8800
SERVE_VENV="${AIQ_SERVE_VENV:-/home/agent/venvs/aiq-serve}"
OUT="build/semantic-alignment/review.html"
IMPORTANCE="headline"
TITLE="Semantic alignment review"
GRAPH=""
DEFAULT_GRAPH="build/leanq/project-semantic-graph.json"
STATEMENTS=0
OPEN=1
CENSUSES=()

usage() { sed -n '2,${/^#/!q;s/^# \{0,1\}//;p}' "$0"; }

while [ $# -gt 0 ]; do
    case "$1" in
        --serve) SERVE=1; shift ;;
        --port) PORT="$2"; shift 2 ;;
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

if [ "$SERVE" -eq 1 ]; then
    # The server needs the optional FastAPI extra. Prefer a venv that has it;
    # fall back to whatever aiq-lean is on PATH and let it print the install line.
    if [ -x "$SERVE_VENV/bin/aiq-lean" ]; then
        RUN="$SERVE_VENV/bin/aiq-lean"
    else
        RUN="aiq-lean"
    fi
    URL="http://127.0.0.1:$PORT/"
    echo "Serving every viewer at $URL  (ctrl-c to stop)"
    if [ "$OPEN" -eq 1 ]; then
        for opener in ${BROWSER:-} xdg-open google-chrome chromium firefox open; do
            if command -v "$opener" >/dev/null 2>&1; then
                ( sleep 2; "$opener" "$URL" >/dev/null 2>&1 & ) &
                break
            fi
        done
    fi
    exec "$RUN" serve --root "$PWD" --port "$PORT"
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
    if [ -f "$GRAPH" ]; then
        ARGS+=(--graph "$GRAPH")
    else
        cat >&2 <<EOF
warning: no graph index at $GRAPH -- building without the proof-dependency panel.
  Build one with:  leanq graph-index --out $GRAPH

EOF
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
