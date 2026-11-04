#!/usr/bin/env bash
# Install the local LeanExplore runtime; fetch data/models only on request.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/common.sh"
usage() {
    cat <<'TXT'
Usage: install-leanexplore.sh [--fetch-assets]
  --fetch-assets   Download native search database and both 0.6B Qwen models.
                   Required once before an offline query.
Environment: PYTHON_BIN=python3.12, LEANEXPLORE_PIP_SPEC='lean-explore[local]'
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
py="${PYTHON_BIN:-python3}"
need "$py"
leanexplore_paths
mkdir -p "$WORK_ROOT/venvs" "$LEAN_EXPLORE_CACHE_DIR" "$HF_HOME"
if [[ ! -x "$LEANEXPLORE_VENV/bin/python" ]]; then
    "$py" -m venv "$LEANEXPLORE_VENV"
fi
"$LEANEXPLORE_VENV/bin/python" -m pip install "${LEANEXPLORE_PIP_SPEC:-lean-explore[local]}"
"$LEANEXPLORE_VENV/bin/python" -m pip show lean-explore > "$WORK_ROOT/leanexplore-package.txt"
if ((fetch)); then
    "$LEANEXPLORE_VENV/bin/lean-explore" data fetch
    # Force both models to disk now; runtime launchers prohibit HF downloads.
    "$LEANEXPLORE_VENV/bin/python" - <<'PY'
from huggingface_hub import snapshot_download
for repo in ("Qwen/Qwen3-Embedding-0.6B", "Qwen/Qwen3-Reranker-0.6B"):
    print(f"Fetching {repo} for later offline queries", flush=True)
    snapshot_download(repo_id=repo)
PY
fi
printf 'LeanExplore venv: %s\n' "$LEANEXPLORE_VENV"
if (( ! fetch )); then
    echo 'Assets not downloaded. Re-run with --fetch-assets before offline use.'
fi
