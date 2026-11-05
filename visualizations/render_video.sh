#!/usr/bin/env bash
set -euo pipefail
presentation_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$presentation_dir"
exec uv run --extra slides python -m dkvis.presentation video "$@"
