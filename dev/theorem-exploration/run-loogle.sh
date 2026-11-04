#!/usr/bin/env bash
# Run Loogle's native CLI or upstream browser UI, never a replacement viewer.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/common.sh"
usage() {
    cat <<'TXT'
Usage:
  run-loogle.sh [--module MOD] [--json] [--max-results N] 'Loogle query'
  run-loogle.sh --web [--module MOD] [--port N] [--host HOST]
  run-loogle.sh --prepare [--module MOD] [--web | 'query']

Default module: DavisKahan.All. Loogle indexes only the selected module's
transitive imports; switch --module to search a different DKPS root.
--prepare explicitly builds that Lean module (after lake exe cache get).
By default, previously compiled .olean files are required.
TXT
}
mod='DavisKahan.All'; json=0; web=0; prepare=0
port=8088; host=127.0.0.1; max_results=50; query=''
while (($#)); do
    case "$1" in
        --module) [[ $# -ge 2 ]] || fail 'Missing --module value'; mod="$2"; shift 2 ;;
        --web) web=1; shift ;;
        --prepare) prepare=1; shift ;;
        --json) json=1; shift ;;
        --port) [[ $# -ge 2 ]] || fail 'Missing --port value'; port="$2"; shift 2 ;;
        --host) [[ $# -ge 2 ]] || fail 'Missing --host value'; host="$2"; shift 2 ;;
        --max-results) [[ $# -ge 2 ]] || fail 'Missing --max-results value'; max_results="$2"; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        --) shift; query="$*"; break ;;
        -*) fail "Unknown flag: $1" ;;
        *) [[ -z "$query" ]] || fail 'Pass exactly one quoted query'; query="$1"; shift ;;
    esac
done
[[ "$mod" =~ ^[a-zA-Z_][a-zA-Z0-9_\.]*$ ]] || fail 'Invalid Lean module name'
[[ "$max_results" =~ ^[0-9]+$ ]] || fail '--max-results must be an integer'
[[ "$port" =~ ^[0-9]+$ ]] || fail '--port must be an integer'
[[ -x "$LOOGLE_BIN" ]] || fail 'First run ./dev/theorem-exploration/install-loogle.sh'
[[ "$(cat "$LOOGLE_SRC/lean-toolchain")" == "$(cat "$PROJECT_ROOT/lean-toolchain")" ]] || fail 'Project Lean toolchain changed; reinstall Loogle'
need lake
if ((prepare)); then
    (cd "$PROJECT_ROOT" && lake exe cache get && lake build "$mod")
fi
# Isolate per-root index from .lake and avoid writing into any dependency checkout.
mkdir -p "$WORK_ROOT/loogle/index"
index_file="$WORK_ROOT/loogle/index/${mod//./_}.loogle-index"
if ((web)); then
    [[ -z "$query" ]] || fail 'Web mode does not take a CLI query'
    need python3
    printf 'Local Loogle UI: http://%s:%s (module %s)\n' "$host" "$port" "$mod"
    cd "$LOOGLE_SRC"
    exec python3 server.py \
        --project-dir "$PROJECT_ROOT" \
        --loogle-bin "$LOOGLE_BIN" \
        --host "$host" --port "$port" \
        -- --module "$mod" --max-results "$max_results" --index-file "$index_file"
else
    [[ -n "$query" ]] || { usage; exit 2; }
    opts=(--module "$mod" --max-results "$max_results" --index-file "$index_file")
    (( json == 0 )) || opts+=(--json)
    cd "$PROJECT_ROOT"
    exec lake env "$LOOGLE_BIN" "${opts[@]}" "$query"
fi
