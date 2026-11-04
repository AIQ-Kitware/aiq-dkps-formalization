#!/usr/bin/env bash
# Clone/build upstream Loogle using the *project's* Lean toolchain.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/common.sh"
if [[ "${1:-}" == --help || "${1:-}" == -h ]]; then
    echo 'Usage: install-loogle.sh'
    echo 'Environment: LOOGLE_REF=commit-or-tag (optional), LOOGLE_GIT_URL=url (optional)'
    exit 0
fi
[[ $# == 0 ]] || fail 'install-loogle.sh takes no arguments'
need git
need lake
[[ -f "$PROJECT_ROOT/lean-toolchain" ]] || fail 'Missing project lean-toolchain'
mkdir -p "$WORK_ROOT/src" "$WORK_ROOT/loogle"
if [[ ! -d "$LOOGLE_SRC/.git" ]]; then
    git clone "${LOOGLE_GIT_URL:-https://github.com/nomeata/loogle.git}" "$LOOGLE_SRC"
fi
if [[ -n "${LOOGLE_REF:-}" ]]; then
    # The previous install intentionally changed upstream lean-toolchain.
    git -C "$LOOGLE_SRC" restore -- lean-toolchain
    git -C "$LOOGLE_SRC" checkout --detach "$LOOGLE_REF"
fi
cp "$PROJECT_ROOT/lean-toolchain" "$LOOGLE_SRC/lean-toolchain"
printf 'Building Loogle against %s\n' "$(cat "$PROJECT_ROOT/lean-toolchain")"
(
    cd "$LOOGLE_SRC"
    lake exe cache get
    lake build
)
[[ -x "$LOOGLE_BIN" ]] || fail "Build completed but executable missing: $LOOGLE_BIN"
git -C "$LOOGLE_SRC" rev-parse HEAD > "$WORK_ROOT/loogle/upstream-revision.txt"
cp "$PROJECT_ROOT/lean-toolchain" "$WORK_ROOT/loogle/project-lean-toolchain.txt"
printf 'Loogle: %s\n' "$LOOGLE_BIN"
printf 'Upstream revision: %s\n' "$(cat "$WORK_ROOT/loogle/upstream-revision.txt")"
