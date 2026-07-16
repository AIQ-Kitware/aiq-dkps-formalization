#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

python3 scripts/remove_spectra_submodule_bridge_experiment.py
python3 scripts/apply_spectra_lightweight_bridge_fix.py

if ! git -C external/Spectra diff --quiet --; then
    echo "Spectra submodule has tracked modifications; bridge policy requires a clean submodule" >&2
    git -C external/Spectra status --short >&2
    exit 1
fi

if test -n "$(git -C external/Spectra ls-files --others --exclude-standard)"; then
    echo "Spectra submodule has untracked files; bridge policy requires a clean submodule" >&2
    git -C external/Spectra status --short >&2
    exit 1
fi

lake build DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.Basic
lake build DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.PVMSubspace
lake build DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.OperatorAbsoluteValue
lake build DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.SinAngle
lake build DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotation
lake build DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.All
