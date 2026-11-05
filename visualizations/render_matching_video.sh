#!/usr/bin/env bash
set -euo pipefail
matching_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$matching_dir"
# Preserve the original command and default deck; later --deck arguments win.
exec ./render_video.sh --deck matching-proof "$@"
