#!/bin/bash
# Run the live review server, and open it.
#
# One process holds every ledger in the repository and every viewer that reads
# one, so the views refer to each other: a declaration named in an alignment row
# links to the census row that registers it, search runs across all the ledgers
# at once, annotations are written back, and a page reloads when a ledger or a
# Lean source changes on disk.
#
# The served pages are rendered by the same code that writes the static ones, so
# the two cannot disagree. For a single self-contained file you can mail to
# someone, use ./semantic-alignment-page.sh instead.
#
# Nothing has to be built to serve: the ledgers and the Lean sources are read
# from disk. Two panels are richer when their inputs exist -- the elaborated
# signatures come from leanq statement sidecars and the proof dependencies from
# a saved graph index -- and the server says which are missing or stale rather
# than presenting an absence as an answer. --build prepares both.
#
# The server needs the optional FastAPI extra. It prefers an aiq-lean in
# $AIQ_SERVE_VENV (default /home/agent/venvs/aiq-serve) and otherwise falls back
# to PATH, which prints the install line if the extra is missing.
#
# Usage:
#   ./semantic-alignment-server.sh [options]
#
# Options:
#   --build               prepare the elaborated-signature and proof-dependency
#                         inputs before serving, by running
#                         ./semantic-alignment-page.sh --build --statements
#                         --graph (which also writes the static page). Slow:
#                         a Lean build and, when the graph index is stale, about
#                         ten minutes to rebuild it.
#   --port N              port to listen on (default: 8800)
#   --host ADDR           address to bind (default: 127.0.0.1)
#   --title TEXT          window title
#   --private-sources F   JSON file, outside the repository, declaring
#                         local-only source documents
#   --include-private     LOCAL ONLY: render private source excerpts in this
#                         browser session. Nothing is written to disk, but do
#                         not screen-share or export the page
#   --no-open             serve only; do not launch a browser
#   -h, --help            this message

set -euo pipefail

cd "$(dirname "$0")"

BUILD=0
PORT=8800
HOST="127.0.0.1"
TITLE=""
OPEN=1
SERVE_VENV="${AIQ_SERVE_VENV:-/home/agent/venvs/aiq-serve}"
EXTRA=()

usage() { sed -n '2,${/^#/!q;s/^# \{0,1\}//;p}' "$0"; }

while [ $# -gt 0 ]; do
    case "$1" in
        --build) BUILD=1; shift ;;
        --port) PORT="$2"; shift 2 ;;
        --host) HOST="$2"; shift 2 ;;
        --title) TITLE="$2"; shift 2 ;;
        --private-sources) EXTRA+=(--private-sources "$2"); shift 2 ;;
        --include-private) EXTRA+=(--include-private); shift ;;
        --no-open) OPEN=0; shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if [ -n "$TITLE" ]; then EXTRA+=(--title "$TITLE"); fi

if [ "$BUILD" -eq 1 ]; then
    # Delegated rather than duplicated: refreshing a statement sidecar means
    # elaborating the declarations a census registers, which is the page
    # renderer's job, and the graph index is the same file both read.
    ./semantic-alignment-page.sh --build --statements --graph --no-open
    echo
fi

# Prefer a venv that has the FastAPI extra; fall back to whatever aiq-lean is on
# PATH and let it print the install line.
if [ -x "$SERVE_VENV/bin/aiq-lean" ]; then
    RUN="$SERVE_VENV/bin/aiq-lean"
elif command -v aiq-lean >/dev/null 2>&1; then
    RUN="aiq-lean"
else
    cat >&2 <<'EOF'
aiq-lean is not on PATH. The server lives in the tools package:

    python3 -m pip install -e 'submodules/aiq-lean-formalization-tools[serve]'

EOF
    exit 127
fi

URL="http://$HOST:$PORT/"
echo "Serving every viewer at $URL  (ctrl-c to stop)"

if [ "$OPEN" -eq 1 ]; then
    for opener in ${BROWSER:-} xdg-open google-chrome chromium firefox open; do
        if command -v "$opener" >/dev/null 2>&1; then
            ( sleep 2; "$opener" "$URL" >/dev/null 2>&1 & ) &
            break
        fi
    done
fi

exec "$RUN" serve --root "$PWD" --host "$HOST" --port "$PORT" "${EXTRA[@]}"
