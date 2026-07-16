#!/usr/bin/env bash
set -euo pipefail

readonly upstream_url="https://github.com/adambornemann-glitch/Spectra.git"
readonly upstream_commit="8dbaaf6728d1342ae16acf79fd7eef7c59b37e63"

root=$(git rev-parse --show-toplevel)
cd "$root"

python3 scripts/verify_vendored_spectra.py

# The previous snapshot overlay staged deletion of the original gitlink. Restore
# the path, then replace the old private-fork gitlink in the index *before*
# asking the public upstream remote to initialize the submodule. Otherwise Git
# tries to fetch the obsolete private commit from upstream and fails.
git restore --source=HEAD --staged external/Spectra
git update-index --add --cacheinfo 160000,"$upstream_commit",external/Spectra

git config -f .gitmodules submodule.external/Spectra.path external/Spectra
git config -f .gitmodules submodule.external/Spectra.url "$upstream_url"
git add .gitmodules

git submodule sync -- external/Spectra
git submodule update --init --force -- external/Spectra

git -C external/Spectra remote set-url origin "$upstream_url"
git -C external/Spectra fetch --no-tags origin "$upstream_commit"
git -C external/Spectra checkout --detach "$upstream_commit"

git add external/Spectra
python3 scripts/verify_spectra_reference.py

echo "Restored external/Spectra as a read-only reference submodule."
echo "Reference and vendor snapshot both point to $upstream_commit."
echo "The DKPS build still uses vendor/Spectra."
