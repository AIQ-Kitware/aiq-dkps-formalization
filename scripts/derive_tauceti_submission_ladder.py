#!/usr/bin/env python3
"""Derive the Tau Ceti submission ladder from the `ForTauCeti` import graph.

`dev/tauceti/submission-ladder.md` answers "what is the most valuable
reorganization for Tau Ceti submission?" by slicing the staging library into
dependency-closed rungs, each reviewable as one topic.

**It was hand-measured, and it went stale the same day it was written.** It
recorded 127 `ForTauCeti` modules; 29 more landed hours later. Every headline
statistic in it -- median closure, leaf count, "cumulative 41 of 127" -- was then
measured against a tree that no longer existed. This tool exists so the ladder is
*derived* rather than maintained: the import graph is the source of truth, and a
number in the document that this tool does not reproduce is a bug in the
document.

A rung is a list of **seed** modules. Its *closed slice* is the dependency
closure of every seed in that rung and all earlier rungs; its *new* modules are
the ones that closure adds over the previous rung. Submitting in rung order
means each PR reviews as one topic against a base Tau Ceti has already accepted.

Usage:
    python3 scripts/derive_tauceti_submission_ladder.py            # report
    python3 scripts/derive_tauceti_submission_ladder.py --check    # exit 1 if the doc disagrees
    python3 scripts/derive_tauceti_submission_ladder.py --json     # machine-readable
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LIB = "ForTauCeti"
LADDER = ROOT / "dev/tauceti/submission-ladder.md"
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)\s*$", re.M)

# Rung seeds, in submission order. Names are written without the `ForTauCeti.`
# prefix, matching how the ladder document lists them.
RUNGS: list[tuple[str, str, list[str]]] = [
    ("A", "Positive square root, operator modulus, polar decomposition", [
        "Analysis.InnerProductSpace.BasisSpan",
        "Analysis.InnerProductSpace.CourantFischer",
        "Analysis.InnerProductSpace.OperatorModulus",
        "Analysis.InnerProductSpace.PartialIsometry",
        "Analysis.InnerProductSpace.PolarDecomposition",
        "Analysis.InnerProductSpace.PositiveSqrt",
        "Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus",
    ]),
    ("B", "Singular values (square and rectangular)", [
        "Analysis.InnerProductSpace.RectangularSingularValues",
        "Analysis.InnerProductSpace.SingularValues",
    ]),
    ("C", "Rectangular approximation numbers", [
        "Analysis.OperatorIdeal.ApproximationNumber.Basic",
        "LinearAlgebra.Dimension.RankComp",
        "SetTheory.Cardinal.Lift",
    ]),
    ("D", "Convex majorization and symmetric gauges", [
        "Analysis.Convex.Majorization",
        "Analysis.InnerProductSpace.KyFan",
        "Analysis.InnerProductSpace.ProjectionGeometry",
        "Analysis.InnerProductSpace.SchurHorn",
        "Analysis.InnerProductSpace.SingularSubspace",
        "Analysis.InnerProductSpace.Spectrum",
        "Analysis.InnerProductSpace.UnitarilyInvariantNorm",
    ]),
    ("E", "Rectangular unitarily invariant norms", [
        "Analysis.InnerProductSpace.AlignedBasis",
        "Analysis.InnerProductSpace.Basic",
        "Analysis.InnerProductSpace.GramMatrix",
        "Analysis.InnerProductSpace.PrincipalAngles",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Basic",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Instances",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Majorization",
        "Analysis.Normed.Operator.LinearIsometry",
    ]),
    ("F", "Ky Fan gauges and operator ideal families", [
        "Analysis.InnerProductSpace.SpectralCutoff",
        "Analysis.OperatorIdeal.ApproximationNumber.Adjoint",
        "Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional",
        "Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction",
        "Analysis.OperatorIdeal.ApproximationNumber.KyFan",
        "Analysis.OperatorIdeal.ApproximationNumber.MinMax",
        "Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper",
        "Analysis.OperatorIdeal.Family.Basic",
        "Analysis.OperatorIdeal.Family.KyFan",
        "Analysis.OperatorIdeal.Family.KyFanDominance",
        "Analysis.OperatorIdeal.Family.OperatorNorm",
        "Analysis.OperatorIdeal.Family.TraceClass",
    ]),
    # Rungs A-F predate the roadmap topic partition and cut across topics T01-T10:
    # they are the approximation-number path, derived before
    # `scripts/check_tauceti_roadmap_topics.py` proved a total, disjoint, acyclic
    # partition of the library into 22 topics.  They are kept because they are a
    # real, reviewed slicing of that stack and shrink PR1 from 37 modules to 3.
    #
    # Rungs G onwards are one rung per topic, in the topic order the partition
    # validates, so that a rung is exactly a roadmap target -- Tau Ceti's own
    # "one topic per PR" unit.  G is the exception it has to be: it completes the
    # ten topics that A-F cut across.  Seeds are each topic's full module list, so
    # a rung cannot silently drift from its roadmap; `--check` reports any seed
    # that no longer names a module.  Lane LADDER-EXT, `jon (yardrat)`, 2026-07-29.
    ("G", "Foundations completion — the rest of topics T01-T10", [
        "Analysis.Convex.Majorization",
        "Analysis.InnerProductSpace.AlignedBasis",
        "Analysis.InnerProductSpace.AngleGeometry",
        "Analysis.InnerProductSpace.Basic",
        "Analysis.InnerProductSpace.BasisSpan",
        "Analysis.InnerProductSpace.CourantFischer",
        "Analysis.InnerProductSpace.EigenvalueChange",
        "Analysis.InnerProductSpace.FiniteFrame",
        "Analysis.InnerProductSpace.FrameFactorization",
        "Analysis.InnerProductSpace.GramMatrix",
        "Analysis.InnerProductSpace.GramOperator",
        "Analysis.InnerProductSpace.HilbertSchmidtEnergy",
        "Analysis.InnerProductSpace.HoffmanWielandt",
        "Analysis.InnerProductSpace.KyFan",
        "Analysis.InnerProductSpace.MoorePenroseInverse",
        "Analysis.InnerProductSpace.NearIsometry",
        "Analysis.InnerProductSpace.OperatorModulus",
        "Analysis.InnerProductSpace.OrthogonalSeries",
        "Analysis.InnerProductSpace.PartialIsometry",
        "Analysis.InnerProductSpace.PolarDecomposition",
        "Analysis.InnerProductSpace.PolarIsometry",
        "Analysis.InnerProductSpace.PolarPartialIsometry",
        "Analysis.InnerProductSpace.PositiveSqrt",
        "Analysis.InnerProductSpace.PrincipalAngles",
        "Analysis.InnerProductSpace.ProjectionBlocks",
        "Analysis.InnerProductSpace.ProjectionGap",
        "Analysis.InnerProductSpace.ProjectionGeometry",
        "Analysis.InnerProductSpace.RectangularSingularValues",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Basic",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.BlockSum",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Instances",
        "Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Majorization",
        "Analysis.InnerProductSpace.ReducingSubspace",
        "Analysis.InnerProductSpace.SchattenNorm",
        "Analysis.InnerProductSpace.SchurHorn",
        "Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus",
        "Analysis.InnerProductSpace.SingularSubspace",
        "Analysis.InnerProductSpace.SingularSystem",
        "Analysis.InnerProductSpace.SingularValues",
        "Analysis.InnerProductSpace.SpectralCutoff",
        "Analysis.InnerProductSpace.SpectralGap",
        "Analysis.InnerProductSpace.SpectralSubspace",
        "Analysis.InnerProductSpace.Spectrum",
        "Analysis.InnerProductSpace.TwoDimensionalSingularValues",
        "Analysis.InnerProductSpace.UnitarilyInvariantNorm",
        "Analysis.Normed.FiniteLpGauge",
        "Analysis.Normed.Operator.LinearIsometry",
        "Analysis.OperatorIdeal.ApproximationNumber.Adjoint",
        "Analysis.OperatorIdeal.ApproximationNumber.Basic",
        "Analysis.OperatorIdeal.ApproximationNumber.Compact",
        "Analysis.OperatorIdeal.ApproximationNumber.Examples",
        "Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional",
        "Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction",
        "Analysis.OperatorIdeal.ApproximationNumber.KyFan",
        "Analysis.OperatorIdeal.ApproximationNumber.MinMax",
        "Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper",
        "Analysis.OperatorIdeal.ApproximationNumber.SameSequence",
        "Analysis.OperatorIdeal.Family.Basic",
        "Analysis.OperatorIdeal.Family.HilbertSchmidt",
        "Analysis.OperatorIdeal.Family.KyFan",
        "Analysis.OperatorIdeal.Family.KyFanDominance",
        "Analysis.OperatorIdeal.Family.OperatorNorm",
        "Analysis.OperatorIdeal.Family.TraceClass",
        "Analysis.SpecialFunctions.Sqrt",
        "LinearAlgebra.Dimension.RankComp",
        "SetTheory.Cardinal.Lift",
    ]),
    ("H", "Hilbert-Schmidt operators (T11)", [
        "Analysis.InnerProductSpace.HilbertSchmidtConjugation",
        "Analysis.InnerProductSpace.HilbertSchmidtLp",
        "Analysis.InnerProductSpace.HilbertSchmidtPythagoras",
        "Analysis.InnerProductSpace.HilbertSchmidtSpace",
    ]),
    ("I", "The Haagerup-Zsido kernel and its Fourier transform (T12)", [
        "Analysis.Fourier.ExponentialAbs",
        "Analysis.Fourier.HaagerupZsido.Defs",
        "Analysis.Fourier.HaagerupZsido.Fourier",
        "Analysis.Fourier.HaagerupZsido.Integrability",
        "Analysis.Fourier.HaagerupZsido.Kernel",
        "Analysis.Fourier.Poisson.CauchyLattice",
        "Analysis.SpecialFunctions.Integral.RationalQuadratic",
        "Analysis.SpecialFunctions.Integral.SineLaplace",
    ]),
    ("J", "One-parameter unitary groups and Stone's theorem (T13)", [
        "Analysis.InnerProductSpace.IntertwiningUnitary",
        "Analysis.InnerProductSpace.OneParameterUnitaryGroup.Basic",
        "Analysis.InnerProductSpace.OneParameterUnitaryGroup.Commutant",
        "Analysis.InnerProductSpace.OneParameterUnitaryGroup.SemigroupBridge",
        "Analysis.InnerProductSpace.OneParameterUnitaryGroup.Stone",
        "Analysis.InnerProductSpace.SkewAdjointExponential",
    ]),
    ("K", "Borel functional calculus and projection-valued measures (T14)", [
        "Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure",
        "Analysis.InnerProductSpace.BorelCalculus.Multiplicative",
        "Analysis.InnerProductSpace.BorelCalculus.Operator",
        "Analysis.InnerProductSpace.BorelCalculus.PVM",
        "Analysis.InnerProductSpace.BorelCalculus.Polarization",
        "Analysis.InnerProductSpace.ProjValMeasure.Additivity",
        "Analysis.InnerProductSpace.ProjValMeasure.Basic",
        "MeasureTheory.CfcMeasurable",
        "MeasureTheory.CompactExists",
        "MeasureTheory.HellySelection",
    ]),
    ("L", "Closed operators on LinearPMap: graphs, constructions and form bounds (T15a)", [
        "Analysis.InnerProductSpace.LinearPMap.Closed",
        "Analysis.InnerProductSpace.LinearPMap.Constructions",
        "Analysis.InnerProductSpace.LinearPMap.GraphCore",
        "Analysis.InnerProductSpace.LinearPMap.Sylvester",
        "Analysis.InnerProductSpace.QuadraticFormBounds",
        "Analysis.InnerProductSpace.SpectralOrder.Complex",
    ]),
    ("M", "Resolvents of self-adjoint LinearPMap operators, and semiboundedness (T15b)", [
        "Analysis.CStarAlgebra.SelfAdjointGapInverse",
        "Analysis.InnerProductSpace.LinearPMap.RealLowerBound",
        "Analysis.InnerProductSpace.LinearPMap.Resolvent",
        "Analysis.InnerProductSpace.LinearPMap.ResolventBound",
        "Analysis.InnerProductSpace.LinearPMap.ResolventOpen",
        "Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent",
        "Analysis.InnerProductSpace.SeparatedIntertwiner",
    ]),
    ("N", "The spectral measure of an unbounded self-adjoint operator, and Stone (T15c)", [
        "Analysis.InnerProductSpace.BlockLowerBound",
        "Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal",
        "Analysis.InnerProductSpace.LinearPMap.SpectralCutOperator",
        "Analysis.InnerProductSpace.LinearPMap.SpectralFormBounds",
        "Analysis.InnerProductSpace.LinearPMap.SpectralGapInverse",
        "Analysis.InnerProductSpace.LinearPMap.SpectralGrid",
        "Analysis.InnerProductSpace.LinearPMap.SpectralMeasure",
        "Analysis.InnerProductSpace.LinearPMap.SpectralMeasure.Construction",
        "Analysis.InnerProductSpace.LinearPMap.SpectralProjectionGroup",
        "Analysis.InnerProductSpace.LinearPMap.SpectralSupport",
        "Analysis.InnerProductSpace.LinearPMap.StoneUniqueness",
        "Analysis.InnerProductSpace.LinearPMap.YosidaApproximation",
    ]),
    ("O", "Sylvester equations and the Rosenblum theorem (T16)", [
        "Analysis.InnerProductSpace.CoerciveUnit",
        "Analysis.InnerProductSpace.HilbertSchmidtBlock",
        "Analysis.InnerProductSpace.Rosenblum",
        "Analysis.InnerProductSpace.Sylvester.Basic",
        "Analysis.InnerProductSpace.Sylvester.BlockEstimate",
        "Analysis.InnerProductSpace.Sylvester.BlockIdentity",
        "Analysis.InnerProductSpace.Sylvester.Bound",
        "Analysis.InnerProductSpace.Sylvester.Generator",
        "Analysis.InnerProductSpace.Sylvester.Group",
        "Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier",
        "Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.DoubledPhase",
        "Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.Fourier",
        "Analysis.InnerProductSpace.Sylvester.Internal.ReciprocalMultiplier.OrbitAction",
        "Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds",
        "Analysis.InnerProductSpace.Sylvester.Interval",
        "Analysis.InnerProductSpace.Sylvester.Operator",
        "Analysis.InnerProductSpace.Sylvester.SpectralDistance",
        "Analysis.InnerProductSpace.Sylvester.SpectralGap",
    ]),
    ("P", "Spectral subspace perturbation: the Davis-Kahan sin-Theta theorems (T17)", [
        "Analysis.InnerProductSpace.BoundedOperator.Projector",
        "Analysis.InnerProductSpace.BoundedOperator.SinTheta",
        "Analysis.InnerProductSpace.DoubleAngle.Vector",
        "Analysis.InnerProductSpace.Residual.AngleEmbedding",
        "Analysis.InnerProductSpace.Residual.Ritz",
        "Analysis.InnerProductSpace.Residual.TrialMap",
        "Analysis.InnerProductSpace.SinTheta.DirectedBounds",
        "Analysis.InnerProductSpace.SinTheta.OperatorNorm",
        "Analysis.InnerProductSpace.SinTheta.Perturbation",
        "Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant",
    ]),
    ("Q", "The Yu-Wang-Samworth statistical variant (T18)", [
        "Analysis.InnerProductSpace.YuWangSamworth.Residual",
        "Analysis.InnerProductSpace.YuWangSamworth.SingularSubspace",
        "Analysis.InnerProductSpace.YuWangSamworth.Statistics",
    ]),
    ("R", "Matrix spectra and spectral measurability (T19)", [
        "Analysis.Matrix.EntrywiseEigenvalue",
        "Analysis.Matrix.EntrywiseOpNorm",
        "Analysis.Matrix.SpectralFunctionMeasurable",
        "Analysis.Matrix.Spectrum",
        "MeasureTheory.Function.ConvergenceInMeasure",
        "MeasureTheory.Measure.Typeclasses.Probability",
    ]),
    ("S", "Sample moments and matrix concentration (T20)", [
        "Probability.Moments.CenteredScatter",
        "Probability.Moments.MatrixConcentration",
        "Probability.Moments.SampleCovariance",
        "Probability.Moments.SampleMean",
        "Probability.Moments.Variance",
    ]),
    ("T", "Matrix rank factorization and positive semidefiniteness (T21)", [
        "LinearAlgebra.Matrix.PosDef",
        "LinearAlgebra.Matrix.RankFactorization",
    ]),
    ("U", "Berge's maximum theorem and approximate minimizers (T22)", [
        "Topology.ApproxMinimizer",
        "Topology.Berge",
    ]),
]


def module_name(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def import_graph() -> dict[str, set[str]]:
    """Every `ForTauCeti` module, mapped to its internal (same-library) imports."""
    graph: dict[str, set[str]] = {}
    for path in sorted((ROOT / LIB).rglob("*.lean")):
        name = module_name(path)
        graph[name] = {
            i for i in IMPORT_RE.findall(path.read_text())
            if i.startswith(LIB + ".")
        }
    return graph


def closure(seeds: set[str], graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(seeds)
    while stack:
        m = stack.pop()
        if m in seen or m not in graph:
            continue
        seen.add(m)
        stack.extend(graph[m])
    return seen


def derive() -> dict:
    graph = import_graph()
    sizes = sorted(len(closure({m}, graph) - {m}) for m in graph)
    n = len(sizes)
    rungs = []
    cumulative: set[str] = set()
    seeds_so_far: set[str] = set()
    for key, title, seeds in RUNGS:
        qualified = {f"{LIB}.{s}" for s in seeds}
        unknown = sorted(s for s in qualified if s not in graph)
        seeds_so_far |= qualified
        slice_ = closure(seeds_so_far, graph)
        new = slice_ - cumulative
        cumulative = slice_
        rungs.append({
            "rung": key, "title": title,
            "new": len(new), "closed_slice": len(slice_),
            "new_modules": sorted(m[len(LIB) + 1:] for m in new),
            "unknown_seeds": [s[len(LIB) + 1:] for s in unknown],
        })
    off = sorted(m[len(LIB) + 1:] for m in set(graph) - cumulative)
    return {
        "total_modules": n,
        "median_internal_closure": sizes[n // 2],
        "mean_internal_closure": round(sum(sizes) / n, 1),
        "internal_leaves": sum(1 for m in graph if not graph[m]),
        "pulling_over_30": sum(1 for s in sizes if s > 30),
        "max_closure": sizes[-1],
        "rungs": rungs,
        "cumulative": len(cumulative),
        "off_ladder": off,
    }


def report(data: dict) -> None:
    print(f"ForTauCeti modules: {data['total_modules']}")
    print(f"  median internal closure {data['median_internal_closure']}, "
          f"mean {data['mean_internal_closure']}, max {data['max_closure']}")
    print(f"  internal leaves {data['internal_leaves']}, "
          f"pulling >30: {data['pulling_over_30']}")
    print()
    for r in data["rungs"]:
        print(f"Rung {r['rung']} — {r['title']}")
        print(f"    {r['new']} new, closed slice {r['closed_slice']}")
        for s in r["unknown_seeds"]:
            print(f"    UNKNOWN SEED (no such module): {s}")
    print()
    print(f"Cumulative on the ladder: {data['cumulative']} of {data['total_modules']}")
    print(f"Off the ladder: {len(data['off_ladder'])}")


def check(data: dict) -> int:
    """Fail when the ladder document disagrees with the tree."""
    problems: list[str] = []
    for r in data["rungs"]:
        for s in r["unknown_seeds"]:
            problems.append(f"rung {r['rung']} seeds a module that does not exist: {s}")
    if not LADDER.exists():
        problems.append(f"{LADDER.relative_to(ROOT)} is missing")
    else:
        text = LADDER.read_text()
        total = data["total_modules"]
        for stale in re.findall(r"of (\d+) `ForTauCeti` modules", text):
            if int(stale) != total:
                problems.append(
                    f"document says 'of {stale} ForTauCeti modules'; "
                    f"the tree has {total}")
        for r in data["rungs"]:
            pat = (rf"### Rung {r['rung']} .*?"
                   rf"\*\*(\d+) new, (?:cumulative )?closed slice (\d+)\.\*\*")
            m = re.search(pat, text, re.S)
            if not m:
                problems.append(f"rung {r['rung']}: no counts found in the document")
            elif (int(m.group(1)), int(m.group(2))) != (r["new"], r["closed_slice"]):
                problems.append(
                    f"rung {r['rung']}: document says {m.group(1)} new / slice "
                    f"{m.group(2)}; derived {r['new']} new / slice {r['closed_slice']}")
    if problems:
        for p in problems:
            print(f"ERROR: {p}")
        print(f"submission ladder: STALE ({len(problems)} finding(s))")
        return 1
    print("submission ladder: OK — document agrees with the import graph")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if the ladder document disagrees with the tree")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    args = parser.parse_args(argv)
    data = derive()
    if args.json:
        json.dump(data, sys.stdout, indent=2)
        print()
        return 0
    if args.check:
        return check(data)
    report(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
