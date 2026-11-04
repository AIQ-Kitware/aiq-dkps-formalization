#!/usr/bin/env bash
# Serve LeanSearch v2 locally on ONE GPU, or query its local FastAPI endpoint.
# Enforce rerank=false for the single-3090 experiment.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/common.sh"
usage() {
    cat <<'TXT'
Usage:
  run-leansearch.sh --serve [--port N]
  run-leansearch.sh [--port N] [--limit N] [--json] [--profile] 'query'

Prerequisite: install-leansearch.sh --fetch-assets
Only localhost HTTP requests. The search endpoint always receives rerank=false.
The published cuVS corpus is Mathlib v4.28.0-rc1, NOT this repo's Lean version.
TXT
}
port=8000; limit=10; mode=query; as_json=0; profile=0; query=''
while (($#)); do
    case "$1" in
        --serve) mode=serve; shift ;;
        --port) [[ $# -ge 2 ]] || fail 'Missing --port'; port="$2"; shift 2 ;;
        --limit) [[ $# -ge 2 ]] || fail 'Missing --limit'; limit="$2"; shift 2 ;;
        --profile) profile=1; shift ;;
        --json) as_json=1; shift ;;
        --help|-h) usage; exit 0 ;;
        --) shift; query="$*"; break ;;
        -*) fail "Unknown flag: $1" ;;
        *) [[ -z "$query" ]] || fail 'Pass exactly one quoted query'; query="$1"; shift ;;
    esac
done
[[ "$port" =~ ^[0-9]+$ && "$limit" =~ ^[0-9]+$ ]] || fail 'port and limit must be integers'
(( port > 0 && port < 65536 && limit > 0 )) || fail 'port must be 1..65535 and limit positive'
leansearch_paths
if [[ "$mode" == serve ]]; then
    [[ -z "$query" ]] || fail '--serve takes no query'
    [[ -x "$LEANSEARCH_VENV/bin/python" && -d "$LEANSEARCH_SRC/src/leansearchv2" ]] || fail 'First run install-leansearch.sh'
    for name in metadata.pkl texts.pkl cuvs_index.bin; do
        [[ -s "$VECTORDB_DIR/$name" ]] || fail "Missing $VECTORDB_DIR/$name; run install-leansearch.sh --fetch-assets"
    done
    [[ -s "$EMBEDDING_MODEL_PATH/config.json" ]] || fail 'Embedding weights absent; run install-leansearch.sh --fetch-assets'
    [[ -s "$RERANKER_MODEL_PATH/tokenizer_config.json" ]] || fail 'Reranker tokenizer absent; run install-leansearch.sh --fetch-assets'
    export HOST=127.0.0.1 PORT="$port"
    export CUDA_VISIBLE_DEVICES="${CUDA_VISIBLE_DEVICES:-0}"
    export NUM_GPUS=1
    export HF_HUB_OFFLINE=1 TRANSFORMERS_OFFLINE=1 HF_DATASETS_OFFLINE=1
    export PYTHONPATH="$LEANSEARCH_SRC/src${PYTHONPATH:+:$PYTHONPATH}"
    printf 'LeanSearch v2 at http://127.0.0.1:%s/docs (single GPU, rerank=false queries only)\n' "$port"
    echo 'WARNING: this upstream server also exposes rerank=true; do not send those requests with one GPU.' >&2
    echo 'WARNING: loading the 8B model and ~5.2 GB cuVS index might exhaust a 24 GB 3090.' >&2
    cd "$LEANSEARCH_SRC"
    exec "$LEANSEARCH_VENV/bin/python" -m uvicorn leansearchv2.server:app --host 127.0.0.1 --port "$port"
fi
[[ -n "$query" ]] || { usage; exit 2; }
need curl
need python3
endpoint=search
((profile == 0)) || endpoint=search_with_profile
# Python quotes query as JSON, so Lean/math symbols and quotes remain intact.
request="$(python3 - "$query" "$limit" <<'PY'
import json, sys
print(json.dumps({"query": [sys.argv[1]], "num_results": int(sys.argv[2]), "rerank": False}))
PY
)"
url="http://127.0.0.1:$port/$endpoint"
if ((as_json)); then
    curl --fail --silent --show-error --connect-timeout 3 --max-time 180 \
        -H 'Content-Type: application/json' -d "$request" "$url"
    printf '\n'
else
    curl --fail --silent --show-error --connect-timeout 3 --max-time 180 \
        -H 'Content-Type: application/json' -d "$request" "$url" | python3 -m json.tool
fi
