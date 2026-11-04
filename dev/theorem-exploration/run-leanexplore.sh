#!/usr/bin/env bash
# Call LeanExplore's local Service or local MCP backend. No hosted fallback.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/common.sh"
if [[ "${1:-}" == --help || "${1:-}" == -h ]]; then
    cat <<'TXT'
Usage:
  run-leanexplore.sh [--json] [--limit N] [--rerank-top N] [--package NAME] 'query'
  run-leanexplore.sh --mcp
The query path calls the upstream Service class (never the remote CLI).
MCP runs upstream's stdio server using --backend local.
TXT
    exit 0
fi
[[ -x "$LEANEXPLORE_VENV/bin/python" ]] || fail 'First run ./dev/theorem-exploration/install-leanexplore.sh --fetch-assets'
leanexplore_paths
# If a model is missing, fail instead of downloading implicitly during a search.
export HF_HUB_OFFLINE=1
export TRANSFORMERS_OFFLINE=1
export HF_DATASETS_OFFLINE=1
if [[ "${1:-}" == --mcp ]]; then
    shift
    [[ $# == 0 ]] || fail '--mcp accepts no additional arguments'
    exec "$LEANEXPLORE_VENV/bin/lean-explore" mcp serve --backend local
fi
exec "$LEANEXPLORE_VENV/bin/python" "$EXPLORATION_DIR/leanexplore-query.py" "$@"
