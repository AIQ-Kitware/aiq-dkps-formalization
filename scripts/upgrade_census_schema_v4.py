#!/usr/bin/env python3
"""One-shot migration of the source census from schema 3 to schema 4.

Schema 3 recorded a single `status` per item, which conflated two independent
questions that a fresh math agent has to answer separately:

    is the mathematics done?      -- `status`
    is it verified by the build?  -- nothing recorded this

Those came apart badly.  Rows carried `compiled_*` for declarations that live
only under `DavisKahan/Experimental`, which no default target builds; other
rows named declarations in the wrong namespace, and the checker never noticed
because it matched only the short name after the last dot.  Section 8 rows
named four theorems that were never written at all.

Schema 4 adds a second, compile-backed axis:

    `verification`  -- what the Lean build actually certifies, checkable by
                       scripts/probe_census_declarations.py
    `blocked_by`    -- which entry in the new top-level `blockers` table stands
                       between this row and completion

and splits `lean_declarations` (names that exist) from `planned_declarations`
(names the census aspires to), so that "every name in `lean_declarations`
resolves" becomes an enforceable invariant rather than a hope.

This script is idempotent and is kept for provenance; routine edits go
straight into the JSON.
"""
from __future__ import annotations

import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
CENSUS = ROOT / "dev/davis-kahan-1970-full-source-census.json"

# ---------------------------------------------------------------------------
# Corrections established by probing every name against the real build.
# `ForMathlib.DavisKahan.Experimental.*` is a *namespace inside production
# files*; it is unrelated to the `DavisKahan/Experimental/` directory, and
# conflating the two is what produced most of these.
# ---------------------------------------------------------------------------
RENAMES = {
    "ForMathlib.DavisKahan.spectraCanonicalIntertwiner":
        "ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraCanonicalIntertwiner",
    "ForMathlib.IsAcute":
        "ForMathlib.DavisKahan.IsAcute",
    "ForMathlib.approximationSingularValue_comp_strongProjection_tendsto":
        "ForMathlib.DavisKahan.Experimental.ExactSinTheta."
        "approximationSingularValue_comp_strongProjection_tendsto",
    "ForMathlib.DavisKahan.directGenuineOrderedSylvesterEngine_lowerUpper":
        "ForMathlib.DavisKahan.Experimental.ExactSinTheta."
        "directGenuineOrderedSylvesterEngine_lowerUpper",
    "ForMathlib.DavisKahan.sinTwoTheta_reflectionResidual_of_spectrum_gap":
        "ForMathlib.DavisKahan.Experimental.SpectraBridge."
        "sinTwoTheta_reflectionResidual_of_spectrum_gap",
    "ForMathlib.DavisKahan.sinTwoTheta_addBounded_of_spectrum_gap":
        "ForMathlib.DavisKahan.Experimental.SpectraBridge."
        "sinTwoTheta_addBounded_of_spectrum_gap",
    "ForMathlib.DavisKahan1970.PaperTheorem61Data":
        "ForMathlib.DavisKahan.Experimental.ExactSinTheta.PaperTheorem61Data",
    "ForMathlib.DavisKahan1970.UnboundedSinThetaData":
        "ForMathlib.DavisKahan.Experimental.ExactSinTheta.UnboundedSinThetaData",
    "ForMathlib.DavisKahan1970.PaperUnitaryInvariantNorm":
        "ForMathlib.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm",
    "ForMathlib.DavisKahan1970.PaperUnitaryInvariantNorm."
    "prefixGauge_le_of_all_kyFan_le_hetero":
        "ForMathlib.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm."
        "prefixGauge_le_of_all_kyFan_le_hetero",
    "ForMathlib.DavisKahanTheory.tanTheta_genuineSpectrum":
        "ForMathlib.DavisKahanExt.tanTheta_genuineSpectrum",
}

# Named in the census but never written; they move out of `lean_declarations`
# so that field keeps meaning "this exists".
NEVER_WRITTEN = {
    "ForMathlib.DavisKahan1970.Section8.theorem8_1_selectedBranch_and_spectralRepulsion",
    "ForMathlib.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData",
    "ForMathlib.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData",
    "ForMathlib.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch",
}

VERIFICATION_DEFINITIONS = {
    "proved_in_build": (
        "Every declaration resolves against DavisKahan.All. The default build "
        "carries no sorry and no axiom, so this is a proof, continuously "
        "re-checked by CI."
    ),
    "proved_conditional": (
        "Declarations resolve against DavisKahan.All and are proved, but the "
        "source conclusion is stated relative to a hypothesis record that no "
        "value is ever constructed for, so the paper's claim is assumed rather "
        "than derived."
    ),
    "partially_in_build": (
        "Some declarations resolve against DavisKahan.All and some do not, so "
        "the row's source claim is only partly guarded by CI. "
        "`declarations_outside_build` lists the unguarded ones."
    ),
    "proved_outside_build": (
        "Declarations compile, but only under DavisKahan/Experimental, which "
        "no default target builds. The mathematics is done; it is not guarded "
        "against regression and is not reachable from the source facade."
    ),
    "not_compiling": (
        "Declarations are written but their package does not compile, so "
        "nothing is certified."
    ),
    "absent": "No declaration exists.",
    "not_applicable": (
        "A documented research question or exposition item. No formalization "
        "is intended, so the row is not proof debt and must not be counted as "
        "a gap."
    ),
}

BLOCKERS = {
    "contour-integration-library": {
        "title": "Operator-valued contour integration and Riesz projections",
        "kind": "hard_math",
        "detail": (
            "DavisKahan/Experimental/InfiniteDimensional/Sylvester/Resolvent.lean "
            "calls Contour.integral, Contour.IsClosed, Contour.Rectifiable, "
            "Contour.index and Contour.cauchyIndicatorFormula. None of these is "
            "defined in this repository, in Mathlib, or in vendored Spectra: the "
            "module was written against an API that was never implemented. This "
            "is the single largest remaining item. Resolvent sits on the critical "
            "path via Sylvester.Basic, so the other three never-compiled "
            "Experimental modules (Core.CompatibilitySinTwoTheta, Ideals.Symmetric, "
            "GraphSubspace) unblock nothing on their own."
        ),
    },
    "two-subspace-classification": {
        "title": "Two-projection canonical decomposition and multiplicity theory",
        "kind": "hard_math",
        "detail": (
            "Section 3's classification results need the Halmos two-subspace "
            "canonical form together with spectral multiplicity functions, and "
            "the infinite-dimensional existence statement needs cardinal-valued "
            "dimension bookkeeping rather than a finite-rank stand-in."
        ),
    },
    "free-beam-closed-operator": {
        "title": "Free-beam closed fourth-derivative operator on L2(0,1)",
        "kind": "hard_math",
        "detail": (
            "Section 9's numerical example needs the analytic model itself: the "
            "closed fourth-derivative operator with the source's boundary "
            "conditions, as an unbounded self-adjoint operator."
        ),
    },
    "free-beam-third-eigenvalue": {
        "title": "The spectral bound alpha_3 > 500",
        "kind": "hard_math",
        "detail": (
            "A concrete transcendental eigenvalue estimate for the free-beam "
            "model. Together with free-beam-closed-operator this is what a "
            "FreeBeamFiniteDataCertificate would have to supply."
        ),
    },
    "section9-certificate-discharge": {
        "title": "Construct the Section 9 certificates",
        "kind": "mixed",
        "detail": (
            "Section 9 compiles, but every source conclusion is stated relative "
            "to FreeBeamFiniteDataCertificate (Section9/ExactData.lean) or "
            "TheoremOutputCertificate (Section9/FullExample.lean), and no value "
            "of either type is ever constructed. The certificate fields are the "
            "paper's numerical claims. Discharging the analytic ones needs "
            "free-beam-closed-operator and free-beam-third-eigenvalue; the rest "
            "is instantiating theorems the repository already proves."
        ),
    },
    "promote-direct-rotation-from-experimental": {
        "title": "Promote the direct-rotation minimality results into the build",
        "kind": "mechanical",
        "detail": (
            "DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean "
            "compiles and is sorry-free, so these results are proved; they are "
            "simply not reachable from any default target. Moving them into "
            "DavisKahan/FiniteDimensional puts them under CI."
        ),
    },
    "promote-sharpness-from-experimental": {
        "title": "Promote the sharpness/optimality witnesses into the build",
        "kind": "mechanical",
        "detail": (
            "DavisKahan/Experimental/FiniteDimensional/Sharpness.lean compiles "
            "and is sorry-free. The constant-optimality and ratio-limit "
            "witnesses are proved but outside every default target."
        ),
    },
    "promote-tan-theta-genuine-from-experimental": {
        "title": "Promote the genuine-spectrum tan Theta theorem into the build",
        "kind": "mechanical",
        "detail": (
            "DavisKahan/Experimental/InfiniteDimensional/TanTheta/"
            "GenuineSpectrum.lean compiles and is sorry-free."
        ),
    },
    "exact-source-wrappers": {
        "title": "Source-numbered wrappers over already-proved general theorems",
        "kind": "mechanical",
        "detail": (
            "The mathematics is in the build in a more general form; what is "
            "missing is a statement carrying the paper's numbering, scope and "
            "hypotheses, so the facade can cite it."
        ),
    },
}

VERIFICATION = {
    # proved and in the build, but the conclusion is certificate-gated
    "DK-9-model": ("proved_conditional", ["section9-certificate-discharge",
                                          "free-beam-closed-operator",
                                          "free-beam-third-eigenvalue"]),
    "DK-9.1-9.4": ("proved_conditional", ["section9-certificate-discharge"]),
    "DK-9.5-9.7": ("proved_conditional", ["section9-certificate-discharge"]),
    "DK-9.8": ("proved_conditional", ["section9-certificate-discharge",
                                      "free-beam-third-eigenvalue"]),
    "DK-9.9-9.11": ("proved_conditional", ["section9-certificate-discharge"]),
    "DK-9-infinite-residual-counterexample": ("proved_in_build", []),
    # proved, compiles, but only under DavisKahan/Experimental
    "DK-3.2-cor": ("proved_outside_build",
                   ["promote-direct-rotation-from-experimental"]),
    "DK-4.1-cor": ("proved_outside_build",
                   ["promote-direct-rotation-from-experimental"]),
    "DK-4.2-prop": ("proved_outside_build",
                    ["promote-direct-rotation-from-experimental"]),
    "DK-4.3-prop": ("proved_outside_build",
                    ["promote-direct-rotation-from-experimental"]),
    "S2-sharpness": ("proved_outside_build",
                     ["promote-sharpness-from-experimental"]),
    "S2-tan-theta": ("proved_outside_build",
                     ["promote-tan-theta-genuine-from-experimental"]),
    # written, but the package does not compile
    "DK-8.1-thm": ("not_compiling", ["contour-integration-library"]),
    "DK-8.2-thm": ("not_compiling", ["contour-integration-library"]),
    # nothing written
    "DK-3.2-prop": ("absent", ["two-subspace-classification"]),
    "DK-3.1-thm": ("absent", ["two-subspace-classification"]),
    "DK-3.1-cor": ("absent", ["two-subspace-classification"]),
    "DK-6.3-lem": ("absent", []),
    # open research questions, explicitly not proof debt
    "DK-10.2": ("not_applicable", []),
    "DK-10.3": ("not_applicable", []),
    "DK-10.4": ("not_applicable", []),
}

# Rows whose remaining work is a source-numbered wrapper over proved general
# mathematics rather than new mathematics.
WRAPPER_ROWS = {
    "S1-block-residual", "DK-3.1-def", "DK-3.2-def", "DK-3.1-prop",
    "DK-3.3-prop", "DK-3.4-prop", "DK-3.5-prop", "DK-4.1-prop",
    "DK-5.1-thm", "DK-5.2-thm", "DK-5.1-lem", "DK-6.3-thm",
    "DK-7-sin2-proof", "DK-7-tan2-proof", "S2-sin-two-theta",
    "S2-tan-two-theta", "S2-unbounded-scope",
}


def head_commit() -> str:
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, check=True).stdout.strip()


def main() -> int:
    data = json.loads(CENSUS.read_text(encoding="utf8"))
    for item in data["items"]:
        decls = item.get("lean_declarations") or []
        renamed = [RENAMES.get(d, d) for d in decls]
        item["lean_declarations"] = [d for d in renamed if d not in NEVER_WRITTEN]
        planned = [d for d in renamed if d in NEVER_WRITTEN]
        if planned:
            item["planned_declarations"] = planned

        verification, blocked = VERIFICATION.get(item["id"], (None, None))
        if verification is None:
            verification = "proved_in_build" if item["lean_declarations"] else "absent"
            blocked = ["exact-source-wrappers"] if item["id"] in WRAPPER_ROWS else []
        item["verification"] = verification
        item["blocked_by"] = blocked

        # key order: keep the two axes adjacent and ahead of the prose
        ordered = {}
        for key in ("id", "section", "source_kind", "source_anchor", "title",
                    "summary", "status", "verification", "blocked_by",
                    "lean_declarations", "planned_declarations", "notes",
                    "next_action"):
            if key in item:
                ordered[key] = item[key]
        for key in item:
            if key not in ordered:
                ordered[key] = item[key]
        item.clear()
        item.update(ordered)

    data["schema_version"] = 4
    data["base_commit"] = head_commit()
    data["verification_definitions"] = VERIFICATION_DEFINITIONS
    data["blockers"] = BLOCKERS
    data["how_to_use"] = (
        "Two independent axes. `status` is the mathematical judgement against "
        "the printed source; `verification` is what the Lean build certifies, "
        "and is checkable -- run scripts/probe_census_declarations.py --verify "
        "to confirm every row still matches the build. To find the frontier, "
        "filter on `verification`: `absent` and `not_compiling` rows need new "
        "work, `proved_outside_build` rows are already proved and only need "
        "wiring, and `blocked_by` names the specific obstruction in `blockers`. "
        "`lean_declarations` names declarations that exist; "
        "`planned_declarations` names ones the census wants but nobody has "
        "written."
    )

    ordered_top = {}
    for key in ("schema_version", "base_commit", "primary_source", "how_to_use",
                "status_definitions", "verification_definitions", "blockers",
                "items"):
        if key in data:
            ordered_top[key] = data[key]
    for key in data:
        ordered_top.setdefault(key, data[key])

    CENSUS.write_text(json.dumps(ordered_top, indent=2, ensure_ascii=False) + "\n",
                      encoding="utf8")
    print(f"census upgraded to schema 4 at {ordered_top['base_commit'][:9]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
