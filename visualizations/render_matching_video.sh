#!/usr/bin/env bash
set -euo pipefail
matching_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$matching_dir"
exec uv run --extra slides python -m dkvis.matching_video "$@"
