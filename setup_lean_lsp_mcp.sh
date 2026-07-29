#!/usr/bin/env bash
# Install and register the lean-lsp-mcp server (https://github.com/oOo0oOo/lean-lsp-mcp)
# so Claude Code can query this repository's Lean proof state directly: goals at a
# `sorry`, diagnostics, hover types, mathlib search, and tactic trial runs.
#
# The Lean toolchain itself is not installed here; elan/lake must already be present.
#
# The MCP server is registered against an absolute --lean-project-path pointing at this
# repository, so it resolves this project regardless of where Claude Code is launched
# from. The server command and its PATH are likewise registered absolutely, because the
# environment this script runs in is not the environment Claude will spawn the server in.

set -Eeuo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export ELAN_HOME
export PATH="$ELAN_HOME/bin:$HOME/.local/bin:$PATH"

SERVER_NAME="${SERVER_NAME:-lean-lsp}"
SMOKE_TIMEOUT="${SMOKE_TIMEOUT:-120}"
# Empty means "whatever uvx resolves today". Pin it to freeze the server interface that
# the smoke test below asserts against.
LEAN_LSP_MCP_VERSION="${LEAN_LSP_MCP_VERSION:-}"
SCOPE="local"
DO_REGISTER=1
DO_SMOKE_TEST=1
CLAUDE_DIRS=()

# Set once registration actually touches the Claude config, so the closing summary
# cannot claim a registration that never happened.
REGISTERED=0
SKIP_REASON=""

# Filled in by build_server_cmd.
SERVER_CMD=()
UVX_PREFIX=()
MCP_PATH_DIRS=()
MCP_PATH=""

log() {
    printf '[setup_lean_lsp_mcp] %s\n' "$*"
}

warn() {
    printf '[setup_lean_lsp_mcp] warning: %s\n' "$*" >&2
}

fail() {
    printf '[setup_lean_lsp_mcp] error: %s\n' "$*" >&2
    exit 1
}

usage() {
    cat <<'EOF'
Usage: ./setup_lean_lsp_mcp.sh [options]

Options:
  --claude-dir DIR   Directory you launch Claude Code from. Repeatable.
                     `local` scope is keyed to this directory, so the server is only
                     visible in sessions started there. Defaults to this repo root.
  --scope SCOPE      local (default), project, or user.
                       local   - private to you, per --claude-dir, not committed
                       project - writes .mcp.json in --claude-dir, shared via git.
                                 NOTE: the entry embeds an absolute path to this
                                 checkout, so it will not resolve on another
                                 machine or clone. Prefer local or user.
                       user    - visible in every project on this machine
  --no-register      Install/verify prerequisites only; do not touch Claude config.
  --no-smoke-test    Skip the stdio handshake check.
  -h, --help         Show this help.

Environment:
  SERVER_NAME            Name to register the server under. Default: lean-lsp.
  SMOKE_TIMEOUT          Seconds to wait for the smoke-test handshake. Default: 120.
  LEAN_LSP_MCP_VERSION   Pin the server package, e.g. 0.29.0. Default: unpinned.
                         Pin this if an upstream release changes the CLI flags, the
                         tool names, or the MCP protocol version asserted below.

Examples:
  ./setup_lean_lsp_mcp.sh
  ./setup_lean_lsp_mcp.sh --claude-dir ../..          # superproject checkout
  ./setup_lean_lsp_mcp.sh --scope user
  LEAN_LSP_MCP_VERSION=0.29.0 ./setup_lean_lsp_mcp.sh
EOF
}

parse_args() {
    while [ $# -gt 0 ]; do
        case "$1" in
            --claude-dir)
                [ $# -ge 2 ] || fail "--claude-dir requires a directory argument"
                CLAUDE_DIRS+=("$2")
                shift 2
                ;;
            --scope)
                [ $# -ge 2 ] || fail "--scope requires an argument"
                SCOPE="$2"
                shift 2
                ;;
            --no-register)   DO_REGISTER=0; shift ;;
            --no-smoke-test) DO_SMOKE_TEST=0; shift ;;
            -h|--help)       usage; exit 0 ;;
            *)               fail "unknown argument: $1 (try --help)" ;;
        esac
    done

    case "$SCOPE" in
        local|user) ;;
        project)
            # .mcp.json is committed, but --lean-project-path has to be absolute for the
            # server to resolve this project from an arbitrary launch directory. Those
            # two facts are in tension and the result is only valid on this machine.
            warn "project scope writes a committed .mcp.json containing the absolute path"
            warn "$REPO_ROOT, which will not resolve on another machine or clone."
            ;;
        *) fail "invalid --scope '$SCOPE' (expected local, project, or user)" ;;
    esac

    case "$SMOKE_TIMEOUT" in
        ''|*[!0-9]*) fail "SMOKE_TIMEOUT must be a whole number of seconds (got '$SMOKE_TIMEOUT')" ;;
    esac

    if [ "${#CLAUDE_DIRS[@]}" -eq 0 ]; then
        CLAUDE_DIRS=("$REPO_ROOT")
    fi

    # Resolve to absolute paths up front: the launch directory is what `local` scope is
    # keyed on, so it must be reported accurately even when --no-register skips the
    # code path that would otherwise resolve it.
    local i dir
    for i in "${!CLAUDE_DIRS[@]}"; do
        dir="${CLAUDE_DIRS[$i]}"
        [ -d "$dir" ] || fail "--claude-dir does not exist: $dir"
        CLAUDE_DIRS[$i]="$(cd "$dir" && pwd)"
    done

    if [ "$SCOPE" = user ] && [ "${#CLAUDE_DIRS[@]}" -gt 1 ]; then
        warn "--scope user registers a single global entry; the extra --claude-dir"
        warn "arguments have no effect and are ignored."
    fi
}

install_uv_if_needed() {
    if command -v uvx >/dev/null 2>&1; then
        log "uv is already installed: $(command -v uvx)"
        return
    fi

    # The installer otherwise picks a destination from XDG_BIN_HOME / CARGO_HOME, which
    # we would neither log correctly nor add to PATH. Pin it so both stay true.
    local uv_bin="$HOME/.local/bin"
    log "installing uv into $uv_bin"
    if command -v curl >/dev/null 2>&1; then
        curl -LsSf https://astral.sh/uv/install.sh | UV_INSTALL_DIR="$uv_bin" sh
    elif command -v wget >/dev/null 2>&1; then
        wget -qO- https://astral.sh/uv/install.sh | UV_INSTALL_DIR="$uv_bin" sh
    else
        fail "curl or wget is required to install uv"
    fi

    export PATH="$uv_bin:$PATH"
    command -v uvx >/dev/null 2>&1 || fail "uv install completed, but uvx is not on PATH"
}

# Not every repo carrying this script ships a toolchain installer, so point at whichever
# one is actually here instead of naming a file that may not exist.
toolchain_hint() {
    if [ -x "$REPO_ROOT/setup_lean.sh" ]; then
        printf 'Run ./setup_lean.sh first.'
    else
        printf 'Install elan first: https://lean-lang.org/install/'
    fi
}

verify_lean_tools() {
    command -v lake >/dev/null 2>&1 || fail "lake not found on PATH. $(toolchain_hint)"
    command -v lean >/dev/null 2>&1 || fail "lean not found on PATH. $(toolchain_hint)"
    log "lake: $(lake --version | head -1)"
}

# --lean-project-path must point at a Lake project root or the server starts, connects,
# and then fails every tool call. Runs first in main(), so a misplaced copy of this
# script is caught before anything is installed or written.
verify_lean_project() {
    [ -f "$REPO_ROOT/lean-toolchain" ] ||
        fail "$REPO_ROOT has no lean-toolchain; it is not a Lean project root."
    [ -f "$REPO_ROOT/lakefile.toml" ] || [ -f "$REPO_ROOT/lakefile.lean" ] ||
        fail "$REPO_ROOT has no lakefile.toml or lakefile.lean; lean-lsp-mcp needs a Lake root."
    log "Lean project root: $REPO_ROOT ($(head -1 "$REPO_ROOT/lean-toolchain"))"
}

check_ripgrep() {
    if command -v rg >/dev/null 2>&1; then
        log "ripgrep found at $(command -v rg); lean_local_search will be available"
    else
        warn "ripgrep (rg) not found. The lean_local_search tool will be degraded or unavailable."
    fi
}

# The server elaborates files on demand. Without prebuilt .olean artifacts the very first
# tool call has to compile Mathlib and will time out, which reads as a broken server.
# This is a presence check, not a freshness check: a stale or partial build still passes.
check_build_artifacts() {
    if [ -d "$REPO_ROOT/.lake/build/lib" ]; then
        log "build artifacts present under .lake/build/lib"
        return
    fi

    warn "no .lake/build artifacts found. The first MCP tool call will time out while Lean"
    warn "compiles dependencies. Run 'lake build' in $REPO_ROOT before using the server."
}

# Append a directory to the registered PATH, ignoring blanks and duplicates.
path_add() {
    local dir="$1" existing
    [ -n "$dir" ] || return 0
    for existing in "${MCP_PATH_DIRS[@]}"; do
        if [ "$existing" = "$dir" ]; then
            return 0
        fi
    done
    MCP_PATH_DIRS+=("$dir")
}

# Add the directory holding $1, if $1 resolves at all.
path_add_tool() {
    local resolved
    resolved="$(command -v "$1" 2>/dev/null)" || return 0
    path_add "$(dirname "$resolved")"
}

# Claude Code spawns the server from its own environment. When Claude is launched from a
# desktop or VS Code process rather than a login shell, that environment need not contain
# elan's bin or uv's install directory: a bare `uvx` would not resolve, and even if it did
# the server could not find `lake`/`lean` to drive the Lean LSP. That failure presents as
# 'Connected' plus tool calls that never return, so pin both the binary and the PATH.
#
# The PATH is built from where the dependencies actually resolved, not from a fixed list.
# A fixed list silently drops tools installed under ~/.cargo/bin, a Homebrew prefix, or
# any other custom location — which would make the checks above report a dependency as
# present and then register an environment that cannot see it.
build_server_cmd() {
    local uvx_bin tool
    uvx_bin="$(command -v uvx)"

    UVX_PREFIX=("$uvx_bin")
    if [ -n "$LEAN_LSP_MCP_VERSION" ]; then
        UVX_PREFIX+=(--from "lean-lsp-mcp==$LEAN_LSP_MCP_VERSION")
    fi
    UVX_PREFIX+=(lean-lsp-mcp)

    SERVER_CMD=("${UVX_PREFIX[@]}" --lean-project-path "$REPO_ROOT")

    MCP_PATH_DIRS=()
    path_add "$ELAN_HOME/bin"
    path_add "$(dirname "$uvx_bin")"
    # lake/lean drive the LSP; rg backs lean_local_search; git is used for project lookups.
    for tool in lake lean rg git; do
        path_add_tool "$tool"
    done
    path_add /usr/local/bin
    path_add /usr/bin
    path_add /bin
    MCP_PATH="$(IFS=:; printf '%s' "${MCP_PATH_DIRS[*]}")"
}

# Populate the uv tool cache now, so the first tool call inside Claude Code is not
# competing with a package download against the MCP startup timeout.
prefetch_server() {
    log "prefetching lean-lsp-mcp via uvx"
    local version
    version="$("${UVX_PREFIX[@]}" --version 2>&1 | tail -1)" ||
        fail "failed to run '${UVX_PREFIX[*]}'"
    log "server package: $version"
    if [ -z "$LEAN_LSP_MCP_VERSION" ]; then
        log "(unpinned; set LEAN_LSP_MCP_VERSION to freeze this)"
    fi
}

# Where the entry we are about to write actually lands, so it can be backed up.
config_path_for() {
    if [ "$SCOPE" = project ]; then
        printf '%s/.mcp.json\n' "$1"
    else
        printf '%s/.claude.json\n' "${CLAUDE_CONFIG_DIR:-$HOME}"
    fi
}

# The hand-editing instructions for when the claude CLI is unavailable. The three scopes
# use two different layouts: `local` entries are nested under their launch directory in
# projects{}, while `project` and `user` entries sit at the top level of their own file.
# Printing the top-level shape for `local` — the default — would send most users to the
# wrong place, so branch on scope and let json.dumps handle quoting.
print_manual_config() {
    local target
    target="$(config_path_for "${CLAUDE_DIRS[0]}")"

    printf '\nAdd this by hand to %s:\n\n' "$target"

    if ! command -v python3 >/dev/null 2>&1; then
        printf '  server name: %s\n  command:     %s\n  args:        %s\n' \
            "$SERVER_NAME" "${SERVER_CMD[0]}" "${SERVER_CMD[*]:1}"
        printf '  env:         PATH=%s\n               ELAN_HOME=%s\n\n' "$MCP_PATH" "$ELAN_HOME"
        if [ "$SCOPE" = local ]; then
            printf '  Nest it under projects -> %s -> mcpServers.\n\n' "${CLAUDE_DIRS[0]}"
        else
            printf '  Put it under the top-level mcpServers object.\n\n'
        fi
        return
    fi

    SERVER_NAME="$SERVER_NAME" SCOPE="$SCOPE" MCP_PATH="$MCP_PATH" \
    ELAN_HOME="$ELAN_HOME" CLAUDE_DIR="${CLAUDE_DIRS[0]}" \
        python3 - "${SERVER_CMD[@]}" <<'PY'
import json, os, sys

cmd = sys.argv[1:]
servers = {os.environ["SERVER_NAME"]: {
    "type": "stdio",
    "command": cmd[0],
    "args": cmd[1:],
    "env": {"PATH": os.environ["MCP_PATH"], "ELAN_HOME": os.environ["ELAN_HOME"]},
}}
if os.environ["SCOPE"] == "local":
    doc = {"projects": {os.environ["CLAUDE_DIR"]: {"mcpServers": servers}}}
else:
    doc = {"mcpServers": servers}
print("\n".join("  " + line for line in json.dumps(doc, indent=2).splitlines()))
print()
PY
}

register_one() {
    # Already validated and made absolute by parse_args.
    local claude_dir="$1"

    if [ "$SCOPE" = user ]; then
        log "registering '$SERVER_NAME' (scope=user) for every project on this machine"
    else
        log "registering '$SERVER_NAME' (scope=$SCOPE) for sessions launched from $claude_dir"
    fi

    # `claude mcp add` refuses a name that already exists (exit 1, no overwrite), so a
    # re-run has to remove first or it would silently leave a stale entry behind. That
    # makes the sequence non-atomic: back the config up so a failed add cannot leave the
    # user with neither the old entry nor the new one.
    local cfg backup="" cfg_existed=0
    cfg="$(config_path_for "$claude_dir")"
    if [ -f "$cfg" ]; then
        cfg_existed=1
        backup="$(mktemp "${TMPDIR:-/tmp}/setup_lean_lsp_mcp.XXXXXX")"
        cp -p "$cfg" "$backup"
    fi

    # A missing entry is the normal first-run case; a present one is a prior
    # configuration being replaced, which is worth saying out loud.
    if ( cd "$claude_dir" && claude mcp remove "$SERVER_NAME" -s "$SCOPE" >/dev/null 2>&1 ); then
        warn "replaced a pre-existing '$SERVER_NAME' entry in $SCOPE scope"
    fi

    if ! ( cd "$claude_dir" &&
           claude mcp add "$SERVER_NAME" -s "$SCOPE" \
               -e "PATH=$MCP_PATH" -e "ELAN_HOME=$ELAN_HOME" -- "${SERVER_CMD[@]}" ); then
        if [ "$cfg_existed" -eq 1 ]; then
            # The backup holds live Claude configuration, so it is deleted as soon as it
            # has served its purpose and kept only when it is the sole surviving copy.
            if cp -p "$backup" "$cfg"; then
                rm -f "$backup"
                warn "restored $cfg to its pre-run contents"
            else
                warn "could not restore $cfg; your pre-run config is saved at $backup"
            fi
        elif [ -e "$cfg" ]; then
            # There was no config here before this run, so a file now is one a failed add
            # left behind — possibly half-written. Nothing of the user's is lost with it.
            rm -f "$cfg"
            warn "removed $cfg, which the failed registration created"
        fi
        fail "claude mcp add failed for $claude_dir"
    fi

    if [ -n "$backup" ]; then
        rm -f "$backup"
    fi
}

register_server() {
    if [ "$DO_REGISTER" -eq 0 ]; then
        SKIP_REASON="--no-register was passed"
        log "skipping registration (--no-register)"
        return
    fi

    if ! command -v claude >/dev/null 2>&1; then
        SKIP_REASON="the 'claude' CLI is not on PATH"
        warn "the 'claude' CLI is not on PATH; skipping automatic registration."
        print_manual_config >&2
        return
    fi

    # user scope is a single global entry, so iterating --claude-dir would just
    # remove and re-add the same record, warning about "replacing" its own work.
    if [ "$SCOPE" = user ]; then
        register_one "${CLAUDE_DIRS[0]}"
    else
        # Each directory is individually transactional; a failure part-way through
        # leaves the directories already processed registered, and fail() says which.
        local dir
        for dir in "${CLAUDE_DIRS[@]}"; do
            register_one "$dir"
        done
    fi
    # The add commands succeeded. Whether Claude can subsequently connect is what
    # STEP 2 of the closing summary asks the user to confirm.
    REGISTERED=1
}

# Drive the server over stdio and confirm it completes an MCP handshake and advertises
# tools. Runs before registration so a broken server never reaches anyone's config.
#
# The exchange follows the MCP lifecycle: initialize, wait for the response, only then
# send notifications/initialized and the first real request. stdin is held open until
# the reply arrives; closing it early shuts the server down mid-request, which looks
# like a hang. A server that starts but never answers is the realistic failure on an
# unbuilt checkout, so the whole exchange is bounded by SMOKE_TIMEOUT.
smoke_test() {
    if [ "$DO_SMOKE_TEST" -eq 0 ]; then
        log "skipping smoke test (--no-smoke-test)"
        return
    fi

    command -v python3 >/dev/null 2>&1 ||
        fail "python3 is required for the smoke test (or pass --no-smoke-test)"

    log "smoke test: MCP handshake + tools/list (timeout ${SMOKE_TIMEOUT}s)"

    # Runs the exact argv and PATH that get registered, so this tests the real thing.
    SMOKE_TIMEOUT="$SMOKE_TIMEOUT" MCP_PATH="$MCP_PATH" \
        python3 - "${SERVER_CMD[@]}" <<'PY' || fail "smoke test failed"
import json, os, signal, subprocess, sys, tempfile

cmd = sys.argv[1:]
# Clamped: signal.alarm(0) cancels the alarm, which would restore the unbounded wait.
timeout = max(1, int(os.environ["SMOKE_TIMEOUT"]))
env = {**os.environ, "PATH": os.environ["MCP_PATH"]}


class SmokeTimeout(Exception):
    pass


class ProtocolError(Exception):
    pass


def on_alarm(signum, frame):
    raise SmokeTimeout


def send(msg):
    proc.stdin.write(json.dumps(msg) + "\n")
    proc.stdin.flush()


def read_reply(want_id):
    """Consume stdout until the response to `want_id` arrives."""
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            # Under the stdio transport the server may log freely to stderr but must not
            # write anything to stdout that is not an MCP message. Tolerating noise here
            # would pass a server that a strict client rejects.
            raise ProtocolError(f"non-MCP output on stdout: {line[:200]!r}")
        if msg.get("id") != want_id:
            continue
        if "error" in msg:
            err = msg["error"] or {}
            raise ProtocolError(f"{err.get('message')} (code {err.get('code')})")
        return msg.get("result", {})
    raise ProtocolError("server closed its output before replying")


errlog = tempfile.TemporaryFile(mode="w+")
proc = subprocess.Popen(
    cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errlog,
    text=True, bufsize=1, env=env,
)

tools = None
failure = None
timed_out = False
# PEP 475 retries interrupted reads unless the handler raises, so the handler raises.
signal.signal(signal.SIGALRM, on_alarm)
signal.alarm(timeout)
try:
    send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "protocolVersion": "2024-11-05", "capabilities": {},
        "clientInfo": {"name": "setup_lean_lsp_mcp", "version": "1"}}})
    # The lifecycle forbids sending anything else until initialize has been answered.
    info = read_reply(1).get("serverInfo", {})
    print(f"[setup_lean_lsp_mcp] connected to {info.get('name')} {info.get('version')}")

    send({"jsonrpc": "2.0", "method": "notifications/initialized"})
    send({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
    tools = read_reply(2).get("tools")
except SmokeTimeout:
    timed_out = True
    failure = f"no reply within {timeout}s; the server started but never answered"
except ProtocolError as exc:
    failure = f"MCP handshake failed: {exc}"
except (BrokenPipeError, OSError) as exc:
    failure = f"server exited during the handshake ({exc})"
finally:
    signal.alarm(0)
    proc.terminate()
    try:
        proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        proc.kill()

if failure is None and not tools:
    failure = "server advertised no tools"

if failure:
    print(f"[setup_lean_lsp_mcp] error: {failure}", file=sys.stderr)
    errlog.seek(0)
    stderr_tail = errlog.read().strip().splitlines()[-15:]
    if stderr_tail:
        print("[setup_lean_lsp_mcp] last lines of server stderr:", file=sys.stderr)
        for line in stderr_tail:
            print(f"[setup_lean_lsp_mcp]   {line}", file=sys.stderr)
    else:
        print("[setup_lean_lsp_mcp] the server produced no stderr output.", file=sys.stderr)
    if timed_out:
        print("[setup_lean_lsp_mcp] hint: run 'lake build' in this repo first, or raise",
              file=sys.stderr)
        print("[setup_lean_lsp_mcp]       the budget with SMOKE_TIMEOUT=<seconds>.",
              file=sys.stderr)
    sys.exit(1)

names = sorted(t["name"] for t in tools)
print(f"[setup_lean_lsp_mcp] server advertises {len(names)} tools")
preview = ", ".join(names[:6]) + (", ..." if len(names) > 6 else "")
print("[setup_lean_lsp_mcp]   " + preview)
for required in ("lean_goal", "lean_diagnostic_messages"):
    if required not in names:
        print(f"[setup_lean_lsp_mcp] error: missing tool {required}", file=sys.stderr)
        sys.exit(1)
PY
}

# Describes what registration actually did. `local` and `project` scope are keyed to the
# launch directory; `user` scope is not, so the directory list would be misleading there.
registration_summary() {
    if [ "$SCOPE" = user ]; then
        printf 'Registered in user scope: visible from every directory on this machine.\n'
    else
        printf "Registered ($SCOPE scope) for sessions launched from:\n"
        printf '    %s\n' "${CLAUDE_DIRS[@]}"
    fi
}

scope_troubleshooting() {
    if [ "$SCOPE" = user ]; then
        cat <<'EOF'
      If it is missing, the entry did not land in your user config. Re-run this
      script and check for errors from 'claude mcp add'.
EOF
    else
        cat <<EOF
      If it is missing, you are launching Claude from a directory this script did
      not register. '$SCOPE' scope is keyed to the launch directory. Re-run with:
          ./setup_lean_lsp_mcp.sh --claude-dir /path/you/launch/claude
      or register everywhere at once:
          ./setup_lean_lsp_mcp.sh --scope user
EOF
    fi
}

# Nothing was registered, so the session-restart instructions do not apply and printing
# them would describe a setup that does not exist.
print_unregistered_summary() {
    cat <<EOF

================================================================================
[setup_lean_lsp_mcp] PREREQUISITES VERIFIED — nothing was registered
================================================================================

The Claude config was not modified, because $SKIP_REASON.
No Claude Code session will see '$SERVER_NAME' until it is registered.

  To register now:
      ./setup_lean_lsp_mcp.sh

  Or add it by hand:
$(print_manual_config)
EOF
}

print_next_steps() {
    if [ "$REGISTERED" -eq 0 ]; then
        print_unregistered_summary
        return
    fi

    cat <<EOF

================================================================================
[setup_lean_lsp_mcp] MANUAL STEPS REQUIRED — the setup is not usable yet
================================================================================

Everything above is done. The following steps cannot be automated, because a
Claude Code session connects to its MCP servers once, at startup. The session you
ran this script from will never see '$SERVER_NAME', no matter what the config says.

  STEP 1 (required) — Start a NEW Claude Code session.

      Terminal CLI:      exit and run 'claude' again.
      VS Code extension: open a new Claude Code chat/session. A full restart of
                         VS Code is normally NOT needed. If the server still does
                         not appear, reload the window:
                           Ctrl/Cmd+Shift+P -> "Developer: Reload Window"

  STEP 2 (required) — Verify the server is connected.

      Run:   claude mcp list
      Want:  $SERVER_NAME: ... lean-lsp-mcp ... - OK Connected

$(scope_troubleshooting)

  STEP 3 (recommended) — Confirm Lean itself responds, not just the server.

      'OK Connected' only means the process started. It does NOT mean Lean
      resolved this project. In the new session, ask Claude for the proof goal at
      a sorry. Pick a live one:

          rg -n --glob '*.lean' --glob '!.lake' '^\s*sorry\s*$' | head -1

      then ask, substituting that file and line:

          "use lean_goal on Path/To/File.lean line 42"

      Expect a proof state. The FIRST call against a Mathlib-heavy file must
      elaborate it and can take several minutes. A reply with partial: true, or
      goal status 'still_elaborating', means Lean is still working: poll again.
      That is not an error and the server is not dead.

--------------------------------------------------------------------------------
$(registration_summary)
Lean project resolved by the server (absolute, independent of launch dir):
    $REPO_ROOT
Server command and environment as registered (independent of your shell):
    ${SERVER_CMD[*]}
    PATH=$MCP_PATH
    ELAN_HOME=$ELAN_HOME
--------------------------------------------------------------------------------

Useful tools for this repo's remaining proof debt:
    lean_goal                 goal state at a sorry, by file path and line number
    lean_diagnostic_messages  errors and warnings for a file
    lean_multi_attempt        try candidate tactics without editing the file
    lean_verify               axiom check for a theorem (catches sorryAx)
    lean_local_search         find an existing declaration before inventing a lemma name

EOF
}

main() {
    parse_args "$@"
    # Cheapest and most fundamental check first: refuse a non-Lean root before this
    # script installs a package manager or touches anyone's configuration.
    verify_lean_project
    install_uv_if_needed
    verify_lean_tools
    check_ripgrep
    check_build_artifacts
    build_server_cmd
    prefetch_server
    # Prove the server works before writing it into anyone's configuration.
    smoke_test
    register_server
    print_next_steps
    log "done"
}

main "$@"
