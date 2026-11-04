#!/usr/bin/env bash
# Install upstream LeanSearch v2 with cuVS, optionally fetch its published corpus.
# Current-corpus extraction/rebuilding is intentionally *not* claimed here.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/common.sh"
usage() {
    cat <<'TXT'
Usage: install-leansearch.sh [--fetch-assets]
  --fetch-assets    Download ~5.74 GB published cuVS index (Mathlib 4.28.0-rc1),
                    Qwen3-Embedding-8B, and the reranker tokenizer only.
                    Expect substantial additional disk usage and GPU memory.
Environment: PYTHON_BIN=python3.12 (recommended for cuVS wheels),
             LEANSEARCH_REF=commit-or-tag (optional),
             LEANSEARCH_GIT_URL=url (optional).
TXT
}
fetch=0
while (($#)); do
    case "$1" in
        --fetch-assets) fetch=1; shift ;;
        --help|-h) usage; exit 0 ;;
        *) fail "Unknown option: $1" ;;
    esac
done
need git
py="${PYTHON_BIN:-python3}"
need "$py"
leansearch_paths
mkdir -p "$WORK_ROOT/src" "$WORK_ROOT/venvs" "$VECTORDB_DIR" \
    "$EMBEDDING_MODEL_PATH" "$RERANKER_MODEL_PATH" "$HF_HOME"
if [[ ! -d "$LEANSEARCH_SRC/.git" ]]; then
    git clone --recurse-submodules "${LEANSEARCH_GIT_URL:-https://github.com/frenzymath/LeanSearch-v2.git}" "$LEANSEARCH_SRC"
fi
if [[ -n "${LEANSEARCH_REF:-}" ]]; then
    git -C "$LEANSEARCH_SRC" checkout --detach "$LEANSEARCH_REF"
    git -C "$LEANSEARCH_SRC" submodule update --init --recursive
fi
if [[ ! -x "$LEANSEARCH_VENV/bin/python" ]]; then
    "$py" -m venv "$LEANSEARCH_VENV"
fi
"$LEANSEARCH_VENV/bin/python" -m pip install -e "$LEANSEARCH_SRC"
"$LEANSEARCH_VENV/bin/python" -m pip install -e "$LEANSEARCH_SRC[cuvs]" --extra-index-url https://pypi.nvidia.com
"$LEANSEARCH_VENV/bin/python" -m pip install huggingface_hub
mkdir -p "$WORK_ROOT/leansearch"
git -C "$LEANSEARCH_SRC" rev-parse HEAD > "$WORK_ROOT/leansearch/upstream-revision.txt"
"$LEANSEARCH_VENV/bin/python" -m pip freeze > "$WORK_ROOT/leansearch/installed-packages.txt"
if ((fetch)); then
    # The upstream one-GPU path skips reranker *weights* but still needs its tokenizer.
    "$LEANSEARCH_VENV/bin/python" - "$VECTORDB_DIR" "$EMBEDDING_MODEL_PATH" "$RERANKER_MODEL_PATH" <<'PY'
import sys
from huggingface_hub import snapshot_download

index_dir, embed_dir, tokenizer_dir = sys.argv[1:]
print("Fetching published cuVS index (Lean v4.28.0-rc1 corpus)", flush=True)
snapshot_download(
    repo_id="FrenzyMath/lsv2-mathlib-v4.28.0-rc1-cuvs",
    repo_type="dataset", local_dir=index_dir,
)
print("Fetching embedding model weights (~16 GB FP16)", flush=True)
snapshot_download(repo_id="Qwen/Qwen3-Embedding-8B", local_dir=embed_dir)
print("Fetching reranker tokenizer only (no 8B reranker model weights)", flush=True)
snapshot_download(
    repo_id="Qwen/Qwen3-Reranker-8B", local_dir=tokenizer_dir,
    allow_patterns=["*.json", "*.txt", "*.model", "tokenizer.*", "*.tiktoken"],
)
PY
    for name in metadata.pkl texts.pkl cuvs_index.bin; do
        [[ -s "$VECTORDB_DIR/$name" ]] || fail "Missing cuVS artifact: $VECTORDB_DIR/$name"
    done
    [[ -s "$RERANKER_MODEL_PATH/tokenizer_config.json" ]] || fail 'Missing reranker tokenizer_config.json'
fi
printf 'LeanSearch v2 checkout: %s\n' "$LEANSEARCH_SRC"
printf 'LeanSearch v2 environment: %s\n' "$LEANSEARCH_VENV"
if (( ! fetch )); then
    echo 'Assets not downloaded. Re-run with --fetch-assets for the old Mathlib corpus.'
fi
