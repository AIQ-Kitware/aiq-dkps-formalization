#!/usr/bin/env python3
"""Verify that the named repository helpers are present at their recorded paths."""
from __future__ import annotations

from pathlib import Path
import os
import sys

PACKAGE = Path(__file__).resolve().parents[1]

def locate_repo() -> Path:
    explicit = os.environ.get("REPO_ROOT")
    candidates = [Path(explicit)] if explicit else []
    candidates += [Path.cwd(), PACKAGE.parent]
    for candidate in candidates:
        if (candidate / "DavisKahan").is_dir() and (candidate / "ForTauCeti").is_dir():
            return candidate.resolve()
    raise SystemExit("cannot locate repository root; set REPO_ROOT=/path/to/aiq-dkps-formalization")

REPO = locate_repo()

REPO_LEDGER = {
    "DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean": [
        "structure PaperUnitaryInvariantNorm",
        "theorem prefixGauge_le_of_all_kyFan_le",
        "theorem mem_of_all_mul_kyFan_le",
        "theorem mul_gauge_le_of_all_mul_kyFan_le",
    ],
    "DavisKahan/Sources/DavisKahan1970/Ideals/NormCorrespondence.lean": [
        "structure PaperSymmetricNormingFunction",
        "toPaperNorm",
    ],
    "ForTauCeti/Analysis/Normed/FiniteLpGauge.lean": [
        "def lpGauge",
        "def linftyGauge",
        "def lpSymmetricGauge",
        "def linftySymmetricGauge",
    ],
    "ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean": [
        "theorem approximationNumber_le_norm_sub",
        "theorem exists_rank_le_norm_sub_lt_approximationNumber_add",
        "theorem approximationNumber_add_le",
    ],
    "ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean": [
        "theorem le_approximationNumber_of_linearIndependent",
    ],
    "ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean": [
        "theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber",
    ],
    "DavisKahan/DoubleAngle/KyFanOrthonormal.lean": [
        "theorem sum_le_kyFanApproximationGauge_of_orthonormal",
    ],
    # Repointed 2026-07-30 (lane CLAIM-DOC): `edward (aiq-gpu)`'s 023b2ceb promoted
    # the bounded Riccati block out of Experimental into production, by path only.
    "DavisKahan/Riccati/BoundedCore.lean": [
        "theorem solvesRiccati_iff_pointwise",
    ],
    "DavisKahan/Riccati/UnboundedReduction.lean": [
        "theorem strongSolvesRiccati_iff_pointwise",
    ],
    "DavisKahan/Riccati/UnboundedExistence.lean": [
        "structure ContractiveReducingGraphSelection",
        "theorem strongSolvesRiccati",
    ],
    "DavisKahan/SpectralTheory/ClosedOperator/Basic.lean": [
        "theorem IsSymmetric.toLinearMap_inner_eq",
        "theorem IsSelfAdjoint.isSymmetric",
    ],
    # Repointed 2026-07-30 (lane CLAIM-DOC).  The two bundled wrappers
    # `SemiboundedBelow.toLinearMap_bound` / `SemiboundedAbove.toLinearMap_bound`
    # were deleted as dead by 9e10b784 -- zero callers, and the bundled predicate is
    # a reducible abbrev, so a caller uses the ForTauCeti twins by defeq.  The
    # grounding is therefore on the canonical definitions, which is where the
    # mathematics now lives.
    "ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean": [
        "def SemiboundedBelow",
        "def SemiboundedAbove",
    ],
    # EXTERNAL as of 2026-07-30 (lane SPECTRA-FORK): the vendored Spectra source was
    # deleted from this repository.  This is a grounding reference to the donor, not an
    # import -- rule 6 still forbids importing it -- and the three theorems live in
    # UNMODIFIED upstream code, so they are not in `retired/patches-Spectra/` either: a
    # diff only carries what changed.  The reference is therefore verifiable only against
    # upstream, and `main()` reports it as EXTERNAL rather than passing or failing it.
    # Silently dropping it would erase a real provenance claim; failing on it would make
    # the gate red for something no local checkout can answer.
    "retired/Spectra/Spectra/SpectralTheory/Algebra.lean": [
        "theorem spectralProjection_congr",
        "theorem energy_lower_bound_of_spectralProjection_Iic_eq_zero",
        "theorem energy_upper_bound_of_spectralProjection_Ici_eq_zero",
    ],
}

FORBIDDEN = [
    "minimalClosure_mem_of_weakSubmajorized",
    "exists_polarFactor",
    "approximationNumber_polarFunctionalCalculus",
    "exists_orthonormal_approximateSingularSystem_initialSegment",
    "iSup_lpPrefix_eq_rpow_tsum",
    "rpow_ne_top_iff_of_pos",
    "tsum_ofReal_ne_top_iff_summable",
    "tendsto_ofReal_zero_iff",
    "stable_exactSingularPair_doubleAngleTangent_le",
    "approximateLeadingFamilies_remove_error",
    "sharp_unbounded_from_boundedOffDiagonalRiccati",
    "doubleAngleTangentScalar_continuousOn",
]


#: Grounding references whose source is no longer in this repository.  Verifiable only
#: against the upstream coordinates recorded in `retired/patches-Spectra/README.md`.
EXTERNAL_PREFIXES = ("retired/Spectra/",)

UPSTREAM_NOTE = ("github.com/adambornemann-glitch/Spectra @ "
                 "8dbaaf6728d1342ae16acf79fd7eef7c59b37e63")


def main() -> int:
    errors: list[str] = []
    external: list[str] = []
    for rel, needles in REPO_LEDGER.items():
        path = REPO / rel
        if rel.startswith(EXTERNAL_PREFIXES):
            external.append(f"{rel} ({len(needles)} references)")
            continue
        if not path.is_file():
            errors.append(f"missing source file: {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                errors.append(f"missing declaration text {needle!r} in {rel}")

    lean_text = "\n".join(
        path.read_text(encoding="utf-8")
        for path in PACKAGE.rglob("*.lean")
    )
    for name in FORBIDDEN:
        if name in lean_text:
            errors.append(f"forbidden speculative helper remains: {name}")

    for marker in ("sorry", "admit", "axiom"):
        for line_no, line in enumerate(lean_text.splitlines(), 1):
            if line.lstrip().startswith(marker + " ") or line.strip() == marker:
                errors.append(f"proof placeholder {marker!r} near aggregate line {line_no}")

    if errors:
        print("grounding audit FAILED", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print("grounding audit passed")
    print(f"checked {len(REPO_LEDGER) - len(external)} repository source files")
    if external:
        print(f"{len(external)} grounding reference(s) are EXTERNAL and were not checked "
              f"locally -- the donor source is no longer vendored:")
        for item in external:
            print(f"  - {item}")
        print(f"  verify against {UPSTREAM_NOTE}")
        print("  (rebuild recipe: retired/patches-Spectra/README.md)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
