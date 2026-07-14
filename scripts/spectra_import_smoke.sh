#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
if [ -z "$ROOT" ]; then
    echo "run this script from inside the DKPS Git repository" >&2
    exit 1
fi
cd "$ROOT"

if ! grep -q '^# BEGIN local Spectra development dependency$' lakefile.toml; then
    echo "Spectra is not enabled in lakefile.toml" >&2
    echo "run: python3 scripts/enable_spectra_lake_dependency.py" >&2
    exit 1
fi

mkdir -p .lake/dkps-smoke
SMOKE=.lake/dkps-smoke/SpectraImports.lean
cat > "$SMOKE" <<'EOF'
import Spectra.ProjValMeasure.Basic
import Spectra.Operator.Bounded
import Spectra.QuantumMechanics.Channels.PolarDecomp

#check Spectra.ProjValMeasure
#check Spectra.Operator.SelfAdjointOperator.ofBounded
#check Spectra.QuantumMechanics.Channels.polar_decomposition
EOF

lake update Spectra
lake env lean "$SMOKE"
