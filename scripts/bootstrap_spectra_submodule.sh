#!/usr/bin/env bash
set -euo pipefail

UPSTREAM_URL="https://github.com/adambornemann-glitch/Spectra.git"
FORK_URL=""
SPECTRA_REF="8dbaaf6728d1342ae16acf79fd7eef7c59b37e63"
WORK_BRANCH="dkps-lean-4.32"
CREATE_FORK=0
ENABLE_LAKE=0
FORCE_LAKE=0

usage() {
    cat <<'USAGE'
Usage: scripts/bootstrap_spectra_submodule.sh [options]

Create or initialize external/Spectra as a real Git submodule, pin the audited
upstream commit, configure upstream and fork remotes, and leave the checkout on
a contribution branch rather than detached HEAD.

Options:
  --upstream-url URL   canonical upstream repository
  --fork-url URL       contribution fork remote; defaults to the authenticated gh user
  --ref REV            audited Spectra commit/tag/branch to pin
  --branch NAME        local contribution branch
  --create-fork        create the authenticated user's Spectra fork when absent
  --enable-lake        enable the path dependency after submodule setup
  --force-lake         enable despite a toolchain mismatch
  -h, --help           show this help
USAGE
}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --upstream-url) UPSTREAM_URL="$2"; shift 2 ;;
        --fork-url) FORK_URL="$2"; shift 2 ;;
        --ref) SPECTRA_REF="$2"; shift 2 ;;
        --branch) WORK_BRANCH="$2"; shift 2 ;;
        --create-fork) CREATE_FORK=1; shift ;;
        --enable-lake) ENABLE_LAKE=1; shift ;;
        --force-lake) FORCE_LAKE=1; ENABLE_LAKE=1; shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
if [ -z "$ROOT" ]; then
    echo "run this script from inside the DKPS Git repository" >&2
    exit 1
fi
cd "$ROOT"

github_slug_from_url() {
    local url="$1"
    url="${url%.git}"
    case "$url" in
        git@github.com:*) printf '%s\n' "${url#git@github.com:}" ;;
        ssh://git@github.com/*) printf '%s\n' "${url#ssh://git@github.com/}" ;;
        https://github.com/*) printf '%s\n' "${url#https://github.com/}" ;;
        http://github.com/*) printf '%s\n' "${url#http://github.com/}" ;;
        *) return 1 ;;
    esac
}

can_read_remote() {
    GIT_TERMINAL_PROMPT=0 GIT_SSH_COMMAND="ssh -o BatchMode=yes" \
        git ls-remote "$1" HEAD >/dev/null 2>&1
}

GH_LOGIN=""
if command -v gh >/dev/null 2>&1 && gh auth status >/dev/null 2>&1; then
    GH_LOGIN="$(gh api user --jq .login)"
fi

if [ -z "$FORK_URL" ]; then
    if [ -n "$GH_LOGIN" ]; then
        FORK_URL="git@github.com:${GH_LOGIN}/Spectra.git"
    else
        FORK_URL="git@github.com:Erotemic/Spectra.git"
    fi
fi

UPSTREAM_SLUG="$(github_slug_from_url "$UPSTREAM_URL" || true)"
FORK_SLUG="$(github_slug_from_url "$FORK_URL" || true)"
if [ -z "$UPSTREAM_SLUG" ]; then
    echo "cannot derive a GitHub repository slug from upstream URL: $UPSTREAM_URL" >&2
    exit 1
fi
if [ -z "$FORK_SLUG" ]; then
    echo "cannot derive a GitHub repository slug from fork URL: $FORK_URL" >&2
    exit 1
fi
FORK_REPO="${FORK_SLUG#*/}"

if [ "$CREATE_FORK" -eq 1 ]; then
    if ! command -v gh >/dev/null 2>&1; then
        echo "gh is required for --create-fork" >&2
        exit 1
    fi
    gh auth status >/dev/null
    if ! gh repo view "$FORK_SLUG" --json nameWithOwner >/dev/null 2>&1; then
        # With an explicit repository argument, gh rejects --remote even when
        # written as --remote=false. The default already avoids cloning and
        # adding a remote, so create the fork with no remote-related flags.
        gh repo fork "$UPSTREAM_SLUG" --fork-name "$FORK_REPO"
    fi
    if ! gh repo view "$FORK_SLUG" --json nameWithOwner >/dev/null 2>&1; then
        echo "fork creation did not produce the expected repository: $FORK_SLUG" >&2
        echo "pass --fork-url for the account or organization that owns the fork" >&2
        exit 1
    fi
fi

if git config -f .gitmodules --get-regexp '^submodule\.external/Spectra\.path$' >/dev/null 2>&1; then
    git submodule sync -- external/Spectra
    git submodule update --init -- external/Spectra
elif [ -e external/Spectra ] && [ ! -d external/Spectra/.git ]; then
    echo "external/Spectra exists but is not a submodule checkout" >&2
    exit 1
else
    mkdir -p external
    git submodule add "$UPSTREAM_URL" external/Spectra
fi

# Keep the committed submodule URL canonical and publicly cloneable.
git config -f .gitmodules submodule.external/Spectra.url "$UPSTREAM_URL"
git submodule sync -- external/Spectra

if git -C external/Spectra remote get-url upstream >/dev/null 2>&1; then
    git -C external/Spectra remote set-url upstream "$UPSTREAM_URL"
else
    git -C external/Spectra remote add upstream "$UPSTREAM_URL"
fi

if git -C external/Spectra remote get-url fork >/dev/null 2>&1; then
    git -C external/Spectra remote set-url fork "$FORK_URL"
else
    git -C external/Spectra remote add fork "$FORK_URL"
fi

# The clone-created origin remains canonical upstream. Contributions use fork.
git -C external/Spectra remote set-url origin "$UPSTREAM_URL"
git -C external/Spectra fetch upstream
if TARGET="$(git -C external/Spectra rev-parse "$SPECTRA_REF^{commit}" 2>/dev/null)"; then
    :
else
    git -C external/Spectra fetch upstream "$SPECTRA_REF"
    TARGET="$(git -C external/Spectra rev-parse FETCH_HEAD)"
fi

if git -C external/Spectra show-ref --verify --quiet "refs/heads/$WORK_BRANCH"; then
    git -C external/Spectra switch "$WORK_BRANCH"
    CURRENT="$(git -C external/Spectra rev-parse HEAD)"
    if ! git -C external/Spectra merge-base --is-ancestor "$TARGET" "$CURRENT"; then
        echo "existing branch $WORK_BRANCH is not based on audited target $TARGET" >&2
        echo "refusing to rewrite contribution history" >&2
        exit 1
    fi
else
    git -C external/Spectra switch -c "$WORK_BRANCH" "$TARGET"
fi

git -C external/Spectra config remote.pushDefault fork

git add .gitmodules external/Spectra

echo "Spectra submodule initialized at $TARGET"
echo "working branch: $WORK_BRANCH"
echo "upstream remote: $UPSTREAM_URL"
echo "fork remote: $FORK_URL"
if command -v gh >/dev/null 2>&1 && gh repo view "$FORK_SLUG" --json nameWithOwner >/dev/null 2>&1; then
    echo "fork repository: $FORK_SLUG"
    if can_read_remote "$FORK_URL"; then
        echo "push with: git -C external/Spectra push -u fork $WORK_BRANCH"
    else
        echo "the fork exists, but SSH access was not verified"
        echo "push after GitHub SSH authentication is configured:"
        echo "  git -C external/Spectra push -u fork $WORK_BRANCH"
    fi
else
    echo "fork not found; create it, then push with:"
    echo "  gh repo fork $UPSTREAM_SLUG --fork-name $FORK_REPO"
    echo "  git -C external/Spectra push -u fork $WORK_BRANCH"
fi

if [ "$ENABLE_LAKE" -eq 1 ]; then
    if [ "$FORCE_LAKE" -eq 1 ]; then
        python3 scripts/enable_spectra_lake_dependency.py --force
    else
        python3 scripts/enable_spectra_lake_dependency.py
    fi
fi

echo "parent repository changes are staged; inspect them before committing"
