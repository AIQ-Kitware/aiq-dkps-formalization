#!/usr/bin/env bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

python3 scripts/verify_vendored_spectra.py
./scripts/restore_spectra_reference_submodule.sh

echo "Vendored clean Spectra snapshot finalized."
echo "The build uses vendor/Spectra, while external/Spectra remains an upstream reference."
