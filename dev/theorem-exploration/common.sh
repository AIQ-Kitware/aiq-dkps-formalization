#!/usr/bin/env bash
# Private path helpers only. Each tool retains its native runtime and formats.
set -euo pipefail
EXPLORATION_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
PROJECT_ROOT="$(cd -- "$EXPLORATION_DIR/../.." && pwd -P)"
WORK_ROOT="${THEOREM_EXPLORATION_WORK_ROOT:-$EXPLORATION_DIR/.build}"
LOOGLE_SRC="$WORK_ROOT/src/loogle"
LOOGLE_BIN="$LOOGLE_SRC/.lake/build/bin/loogle"
LEANEXPLORE_VENV="$WORK_ROOT/venvs/leanexplore"
LEANSEARCH_SRC="$WORK_ROOT/src/LeanSearch-v2"
LEANSEARCH_VENV="$WORK_ROOT/venvs/leansearch"

fail() { printf 'error: %s\n' "$*" >&2; exit 1; }
need() { command -v "$1" >/dev/null 2>&1 || fail "Missing '$1' on PATH"; }

# Deliberately keep model data and tool checkouts under the ignored experiment tree.
leanexplore_paths() {
    export LEAN_EXPLORE_CACHE_DIR="${LEAN_EXPLORE_CACHE_DIR:-$WORK_ROOT/leanexplore/cache}"
    export HF_HOME="${HF_HOME:-$WORK_ROOT/huggingface}"
    # Upstream stores `active_version` under ~/.lean_explore, not under
    # LEAN_EXPLORE_CACHE_DIR. Give it a dedicated HOME to keep state local.
    export HOME="${LEANEXPLORE_HOME:-$WORK_ROOT/leanexplore/home}"
    mkdir -p "$HOME"
}
leansearch_paths() {
    export HF_HOME="${HF_HOME:-$WORK_ROOT/huggingface}"
    export VECTORDB_DIR="${VECTORDB_DIR:-$WORK_ROOT/leansearch/index/mathlib-v4.28.0-rc1}"
    export EMBEDDING_MODEL_PATH="${EMBEDDING_MODEL_PATH:-$WORK_ROOT/leansearch/models/Qwen3-Embedding-8B}"
    export RERANKER_MODEL_PATH="${RERANKER_MODEL_PATH:-$WORK_ROOT/leansearch/models/Qwen3-Reranker-8B-tokenizer}"
}
