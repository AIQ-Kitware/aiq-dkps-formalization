#!/usr/bin/env bash
# Install the external tools needed to run the AIQ challenge comparator check.
#
# This installs:
#   - leanprover/comparator, pinned to THIS repository's Lean toolchain (see below)
#   - lean4export, from comparator's pinned Lake dependency
#   - nanoda, the independent kernel  (needs cargo; optional but wanted)
#   - landrun, the sandbox            (needs go;    optional)
#
# Only git and lake are hard requirements. The two optional tools are genuinely
# different in kind, and the script says so rather than treating them alike:
#
#   nanoda IS a check. Comparator replays the exported proof through a second,
#   independent kernel. Without it you are running one kernel, not two.
#
#   landrun is a sandbox, not a check. It confines the exporter; it does not
#   affect what is compared. `run_challenge_comparator.sh --fake-landrun` runs the
#   same commands unsandboxed and the comparison is unchanged.
#
# The comparator checkout is pinned to this repository's `lean-toolchain`, and that
# is not optional. lean4export reads our `.olean` files directly, so an exporter
# built at a different Lean version fails with `incompatible header` -- which looks
# like a broken statement rather than a version mismatch. Comparator's own pin has
# been ahead of ours before (v4.34.0-rc2 against v4.34.0-rc1 on 2026-08-28). See
# dev/journals/comparator-statement-export-matching-2026-06-14.md.
#
# Defaults mirror the setup that worked on Jon's machine. Override paths with:
#   AIQ_COMPARATOR_TOOL_ROOT=/path/to/tools bash scripts/install_comparator_tools.sh
#
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOL_ROOT="${AIQ_COMPARATOR_TOOL_ROOT:-$HOME/code/lean-tools}"
COMPARATOR_REPO="${AIQ_COMPARATOR_REPO:-$TOOL_ROOT/comparator}"
COMPARATOR_URL="${AIQ_COMPARATOR_URL:-https://github.com/leanprover/comparator.git}"
NANODA_REPO="${AIQ_NANODA_REPO:-$TOOL_ROOT/nanoda_lib}"
NANODA_URL="${AIQ_NANODA_URL:-https://github.com/ammkrn/nanoda_lib.git}"
LANDRUN_GO_REF="${AIQ_LANDRUN_GO_REF:-main}"
GO_BIN="$(go env GOPATH 2>/dev/null)/bin"

need_cmd() {
    if ! command -v "$1" >/dev/null 2>&1; then
        echo "error: required command not found: $1" >&2
        exit 1
    fi
}

have_cmd() { command -v "$1" >/dev/null 2>&1; }

need_cmd git
need_cmd lake

mkdir -p "$TOOL_ROOT"

if have_cmd go; then
    printf 'Installing landrun from github.com/zouuup/landrun/cmd/landrun@%s\n' "$LANDRUN_GO_REF"
    go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_GO_REF"
else
    echo "note: go not found, so landrun is not installed."
    echo "      landrun is the sandbox, not a check. Run comparator with"
    echo "      --fake-landrun; the comparison is unaffected."
fi

if [ ! -d "$COMPARATOR_REPO/.git" ]; then
    if [ -e "$COMPARATOR_REPO" ]; then
        echo "error: $COMPARATOR_REPO exists but is not a git checkout" >&2
        exit 1
    fi
    echo "Cloning comparator into $COMPARATOR_REPO"
    git clone "$COMPARATOR_URL" "$COMPARATOR_REPO"
else
    echo "Updating existing comparator checkout at $COMPARATOR_REPO"
    git -C "$COMPARATOR_REPO" fetch origin main
    current_branch="$(git -C "$COMPARATOR_REPO" branch --show-current || true)"
    if [ "$current_branch" = "main" ] || [ "$current_branch" = "master" ]; then
        git -C "$COMPARATOR_REPO" pull --ff-only || {
            echo "warning: could not fast-forward comparator checkout; continuing with existing checkout" >&2
        }
    else
        echo "warning: comparator checkout is on branch '$current_branch'; not changing branches" >&2
    fi
fi

# Pin the comparator checkout to this repository's Lean. lean4export reads our
# oleans, so a mismatch fails with `incompatible header` at export time.
REPO_TOOLCHAIN="$(tr -d '[:space:]' < "$REPO_ROOT/lean-toolchain")"
CURRENT_TOOLCHAIN="$(tr -d '[:space:]' < "$COMPARATOR_REPO/lean-toolchain" 2>/dev/null || echo '')"
if [ "$CURRENT_TOOLCHAIN" != "$REPO_TOOLCHAIN" ]; then
    echo "Pinning comparator to this repository's toolchain: $REPO_TOOLCHAIN"
    echo "  (comparator's own pin was: ${CURRENT_TOOLCHAIN:-none})"
    printf '%s\n' "$REPO_TOOLCHAIN" > "$COMPARATOR_REPO/lean-toolchain"
fi

echo "Building comparator"
(
    cd "$COMPARATOR_REPO"
    lake build comparator
)

echo "Building lean4export from comparator's pinned dependency"
(
    cd "$COMPARATOR_REPO/.lake/packages/lean4export"
    lake build lean4export
)

NANODA_BIN=""
if have_cmd cargo; then
    if [ ! -d "$NANODA_REPO/.git" ]; then
        if [ -e "$NANODA_REPO" ]; then
            echo "error: $NANODA_REPO exists but is not a git checkout" >&2
            exit 1
        fi
        echo "Cloning nanoda into $NANODA_REPO"
        git clone "$NANODA_URL" "$NANODA_REPO"
    fi
    echo "Building nanoda (the independent kernel)"
    (
        cd "$NANODA_REPO"
        cargo build --release
    )
    NANODA_BIN="$NANODA_REPO/target/release/nanoda_bin"
    if [ ! -x "$NANODA_BIN" ]; then
        echo "error: nanoda built but $NANODA_BIN is missing" >&2
        exit 1
    fi
else
    echo "WARNING: cargo not found, so nanoda is not installed."
    echo "         nanoda is a CHECK, not a sandbox: without it comparator replays"
    echo "         the proof through one kernel instead of two. Install Rust and"
    echo "         re-run this script before treating a comparator PASS as complete."
fi

COMPARATOR_BIN="$COMPARATOR_REPO/.lake/build/bin/comparator"
LEAN4EXPORT_BIN="$COMPARATOR_REPO/.lake/packages/lean4export/.lake/build/bin/lean4export"
LANDRUN_BIN="$GO_BIN/landrun"

for exe in "$COMPARATOR_BIN" "$LEAN4EXPORT_BIN"; do
    if [ ! -x "$exe" ]; then
        echo "error: expected executable missing: $exe" >&2
        exit 1
    fi
done

NANODA_DIR="${NANODA_BIN:+$(dirname "$NANODA_BIN"):}"

ENV_FILE="$TOOL_ROOT/aiq-comparator-env.sh"
cat > "$ENV_FILE" <<EOF_ENV
# Source this file to use the comparator tools installed for aiq-dkps-formalization.
# nanoda is found by name on PATH, as \`nanoda_bin\`.
export PATH="$NANODA_DIR$GO_BIN:$COMPARATOR_REPO/.lake/build/bin:\$PATH"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN"
EOF_ENV
if [ -x "$LANDRUN_BIN" ]; then
    echo "export COMPARATOR_LANDRUN=\"$LANDRUN_BIN\"" >> "$ENV_FILE"
fi

cat <<EOF_DONE

Comparator tools installed.

comparator:  $COMPARATOR_BIN
lean4export: $LEAN4EXPORT_BIN   (built at $REPO_TOOLCHAIN)
nanoda:      ${NANODA_BIN:-NOT INSTALLED -- one kernel, not two}
landrun:     ${LANDRUN_BIN:-}$([ -x "$LANDRUN_BIN" ] || echo '   NOT INSTALLED -- use --fake-landrun')

env file:    $ENV_FILE

Run the challenge check from the repository root with:

  bash scripts/run_challenge_comparator.sh

or, for the Palomar submission entries:

  scripts/verify_palomar.sh

Or, for a shell with the tools configured:

  source "$ENV_FILE"

EOF_DONE
