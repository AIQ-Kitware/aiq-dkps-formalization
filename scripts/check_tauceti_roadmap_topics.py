#!/usr/bin/env python3
"""Validate the candidate Tau Ceti roadmap topic design against the import graph.

`ForTauCetiRoadmap/CANDIDATE-TOPIC-DESIGN.md` proposes a partition of every
`ForTauCeti` module into **20 roadmap topics**, ordered so that each is
reviewable on its own against a base Tau Ceti has already accepted.

This tool is what makes that proposal checkable rather than plausible. It
enforces three properties, each of which the first hand-drawn draft violated:

* **Total** — every module in the tree is assigned to exactly one topic. A
  design that quietly omits modules is how 115 of 156 ended up with no
  submission path at all.
* **Disjoint** — no module is claimed by two topics.
* **Acyclic in submission order** — no module imports anything assigned to a
  *later* topic. This is the property that makes a topic submittable: a forward
  reference means the PR cannot compile against what Tau Ceti has accepted so
  far. The first draft had 24; the second had 12; the fixes are recorded in the
  design document, because each one was a fact about the mathematics rather than
  a bookkeeping slip.

Usage:
    python3 scripts/check_tauceti_roadmap_topics.py           # report
    python3 scripts/check_tauceti_roadmap_topics.py --check   # exit 1 on any violation
    python3 scripts/check_tauceti_roadmap_topics.py --topic T15   # list one topic
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[1]
P = "ForTauCeti."
A = "Analysis.InnerProductSpace."
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)\s*$", re.M)

# Topics in submission order. Adding a module to the tree without adding it here
# makes --check fail, which is the point: the design must stay total.
TOPICS: list[tuple[str, str, list[str]]] = [
("T01","Positive square root, operator modulus, functional calculus",
 ["Analysis.SpecialFunctions.Sqrt","Analysis.Normed.Operator.LinearIsometry",A+"Basic",A+"BasisSpan",A+"CourantFischer",
  A+"PositiveSqrt",A+"SelfAdjointFunctionalCalculus",A+"OperatorModulus",A+"Spectrum"]),
("T02","Polar decomposition and partial isometries",
 [A+"PartialIsometry",A+"PolarDecomposition",A+"PolarIsometry",A+"PolarPartialIsometry",A+"NearIsometry"]),
("T03","Singular values and the singular system",
 [A+"SingularValues",A+"RectangularSingularValues",A+"SingularSystem",A+"MoorePenroseInverse"]),
("T04","Gram matrices, orthogonal projections, and spectral subspaces",
 [A+x for x in ["GramMatrix","ProjectionGeometry","ProjectionBlocks","ProjectionGap",
   "ReducingSubspace","SpectralSubspace","SpectralGap","OrthogonalSeries"]]),
("T05","Majorization, Schur-Horn, and unitarily invariant norms",
 ["Analysis.Convex.Majorization",A+"SchurHorn",A+"SingularSubspace",A+"KyFan",
  A+"UnitarilyInvariantNorm"]),
("T06","Principal angles, aligned bases, and finite frames",
 [A+x for x in ["PrincipalAngles","AlignedBasis","FiniteFrame"]]),
("T07","Rectangular unitarily invariant norms",
 [A+"RectangularUnitarilyInvariantNorm",A+"TwoDimensionalSingularValues"]
 +[A+"RectangularUnitarilyInvariantNorm."+x for x in ["Basic","BlockSum","Instances","Majorization"]]),
("T08","Angle geometry and eigenvalue perturbation",
 [A+x for x in ["GramOperator","AngleGeometry","FrameFactorization","HoffmanWielandt","EigenvalueChange"]]),
("T09","Approximation numbers",
 ["SetTheory.Cardinal.Lift","LinearAlgebra.Dimension.RankComp",
  A+"SpectralCutoff"]+["Analysis.OperatorIdeal.ApproximationNumber."+x for x in
  ["Basic","Adjoint","FiniteDimensional","FiniteRestriction","KyFan","MinMax","MinMaxUpper","SameSequence"]]),
("T10","Symmetric operator ideals and Schatten norms",
 ["Analysis.OperatorIdeal.Family."+x for x in ["Basic","HilbertSchmidt","KyFan","KyFanDominance","OperatorNorm","TraceClass"]]
 +[A+"SchattenNorm",A+"HilbertSchmidtEnergy","Analysis.Normed.FiniteLpGauge"]),
("T11","Hilbert-Schmidt operators",
 [A+"HilbertSchmidt"+x for x in ["Lp","Space","Conjugation","Pythagoras"]]),
("T12","The Haagerup-Zsido kernel and its Fourier transform",
 ["Analysis.Fourier.HaagerupZsido."+x for x in ["Defs","Fourier","Integrability"]]
 +["Analysis.Fourier.ExponentialAbs","Analysis.Fourier.HaagerupZsido.Kernel",
   "Analysis.Fourier.Poisson.CauchyLattice"]
 +["Analysis.SpecialFunctions.Integral."+x for x in ["RationalQuadratic","SineLaplace"]]),
("T13","One-parameter unitary groups and Stone's theorem",
 [A+"OneParameterUnitaryGroup."+x for x in ["Basic","Commutant","SemigroupBridge","Stone"]]
 +[A+"IntertwiningUnitary",A+"SkewAdjointExponential"]),
("T14","Borel functional calculus and projection-valued measures",
 [A+"BorelCalculus."+x for x in ["DiagonalMeasure","Multiplicative","Operator","PVM","Polarization"]]
 +[A+"ProjValMeasure.Basic",A+"ProjValMeasure.Additivity",
   "MeasureTheory.CfcMeasurable","MeasureTheory.CompactExists","MeasureTheory.HellySelection"]),
# T15 was one 25-module, 6,700-line topic -- the biggest by both measures and
# nearly three times the median.  Lane T15-SPLIT cut it into the three chains the
# T04-T20 audit found, which barely touch: closedness/graphs, resolvents, and the
# spectral measure.  Keys are suffixed rather than renumbered on purpose: pushing
# T16-T22 up would invalidate every `Txx` reference in the audit files, in
# CANDIDATE-TOPIC-DESIGN.md and in the written roadmaps, for no gain.
# The audit proposed the cut; the import graph moved three modules across it.
# `RealLowerBound` imports `SelfAdjointResolvent`, `SelfAdjointMaximal` imports
# `SpectralMeasure`, and `SpectralGapInverse` imports `SpectralSupport`, so each
# sits one chain later than its subject matter suggests.  Placed by dependency,
# not by name -- `--check` reports a forward reference otherwise.
("T15a","Closed operators on LinearPMap: graphs, constructions and form bounds",
 [A+"LinearPMap."+x for x in ["Closed","Constructions","GraphCore","Sylvester"]]
 +[A+"QuadraticFormBounds",A+"SpectralOrder.Complex"]),
("T15b","Resolvents of self-adjoint LinearPMap operators, and semiboundedness",
 [A+"LinearPMap."+x for x in ["Resolvent","ResolventBound","ResolventOpen",
   "SelfAdjointResolvent","RealLowerBound"]]
 +["Analysis.CStarAlgebra.SelfAdjointGapInverse",A+"SeparatedIntertwiner"]),
("T15c","The spectral measure of an unbounded self-adjoint operator, and Stone",
 [A+"LinearPMap."+x for x in ["SpectralMeasure","SpectralMeasure.Construction","SpectralGrid",
   "SpectralSupport","SpectralFormBounds","SpectralGapInverse","SpectralCutOperator",
   "SpectralProjectionGroup","SelfAdjointMaximal","StoneUniqueness","YosidaApproximation"]]
 +[A+"BlockLowerBound"]),
("T16","Sylvester equations and the Rosenblum theorem",
 [A+x for x in ["Rosenblum","HilbertSchmidtBlock","CoerciveUnit"]]
 +[A+"Sylvester."+x for x in ["Basic","Interval","SpectralDistance",
   "Bound","Operator","BlockIdentity","BlockEstimate","SpectralGap","Generator","Group"]]
 +[A+"Sylvester.Internal.ReciprocalMultiplier"+x for x in
     ["",".OrbitAction",".Fourier",".DoubledPhase"]]
 +[A+"Sylvester.Internal.SpectralBounds"]),
("T17","Spectral subspace perturbation: the Davis-Kahan sin-Theta theorems",
 [A+"SinTheta."+x for x in ["OperatorNorm","Perturbation","DirectedBounds","UnitarilyInvariant"]]
 +[A+"Residual."+x for x in ["AngleEmbedding","Ritz","TrialMap"]]
 +[A+"DoubleAngle.Vector"]+[A+"BoundedOperator."+x for x in ["Basic","Projector","SinTheta"]]),
("T18","The Yu-Wang-Samworth statistical variant",
 [A+"YuWangSamworth."+x for x in ["Residual","SingularSubspace","Statistics"]]),
("T19","Matrix spectra and spectral measurability",
 ["Analysis.Matrix."+x for x in ["EntrywiseEigenvalue","EntrywiseOpNorm","SpectralFunctionMeasurable","Spectrum"]]
 +["MeasureTheory.Function.ConvergenceInMeasure","MeasureTheory.Measure.Typeclasses.Probability"]),
("T20","Sample moments and matrix concentration",
 ["Probability.Moments."+x for x in ["MatrixConcentration","SampleCovariance","SampleMean","Variance"]]
 +["Probability.Moments.CenteredScatter"]),
("T21","Matrix rank factorization and positive semidefiniteness",
 ["LinearAlgebra.Matrix.RankFactorization","LinearAlgebra.Matrix.PosDef"]),
("T22","Berge's maximum theorem and approximate minimizers",
 ["Topology.ApproxMinimizer","Topology.Berge"]),
]


def import_graph() -> dict[str, set[str]]:
    graph = {}
    for path in sorted((ROOT / "ForTauCeti").rglob("*.lean")):
        name = str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
        graph[name] = {i for i in IMPORT_RE.findall(path.read_text())
                       if i.startswith(P)}
    return graph


def analyse() -> dict:
    graph = import_graph()
    assign, dup = {}, []
    for key, _, mods in TOPICS:
        for m in mods:
            q = P + m
            if q in assign:
                dup.append((q, assign[q], key))
            assign[q] = key
    order = {k: i for i, (k, _, _) in enumerate(TOPICS)}
    unknown = sorted(m[len(P):] for m in assign if m not in graph)
    unassigned = sorted(m[len(P):] for m in graph if m not in assign)
    violations = []
    for m, deps in graph.items():
        if m not in assign:
            continue
        for d in deps:
            if d in assign and order[assign[d]] > order[assign[m]]:
                violations.append((assign[m], m[len(P):], assign[d], d[len(P):]))
    return {"graph": graph, "assign": assign, "dup": dup, "unknown": unknown,
            "unassigned": unassigned, "violations": sorted(violations)}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="exit 1 on any violation")
    ap.add_argument("--topic", help="list the modules of one topic")
    ap.add_argument("--needs", action="store_true",
                    help="print each topic's exact prerequisite topics")
    args = ap.parse_args(argv)
    d = analyse()

    if args.topic:
        for key, title, mods in TOPICS:
            if key == args.topic:
                print(f"{key} — {title}  ({len(mods)} modules)")
                for m in sorted(mods):
                    print(f"    {m}")
                return 0
        print(f"no such topic: {args.topic}", file=sys.stderr)
        return 2

    if args.needs:
        order = {k: i for i, (k, _, _) in enumerate(TOPICS)}
        dep = {k: set() for k, _, _ in TOPICS}
        for mod, deps in d["graph"].items():
            for x in deps:
                if d["assign"][x] != d["assign"][mod]:
                    dep[d["assign"][mod]].add(d["assign"][x])
        for key, title, mods in TOPICS:
            need = sorted(dep[key], key=lambda t: order[t])
            print(f"  {key} ({len(mods):3}) needs: "
                  f"{', '.join(need) if need else '— independent'}   {title}")
        return 0

    print(f"modules {len(d['graph'])}   topics {len(TOPICS)}   "
          f"assigned {len(d['assign'])}")
    for q, a, b in d["dup"]:
        print(f"  DUPLICATE  {q[len(P):]}  in {a} and {b}")
    for m in d["unknown"]:
        print(f"  NO SUCH MODULE  {m}")
    for m in d["unassigned"]:
        print(f"  UNASSIGNED  {m}")
    for ta, ma, tb, mb in d["violations"]:
        print(f"  FORWARD REF  {ta}:{ma}  ->  {tb}:{mb}")
    bad = len(d["dup"]) + len(d["unknown"]) + len(d["unassigned"]) + len(d["violations"])
    if not args.check:
        print()
        for key, title, mods in TOPICS:
            print(f"  {key}  {len(mods):3}  {title}")
    if bad:
        print(f"\nroadmap topics: {bad} violation(s)")
        return 1
    print("\nroadmap topics: OK — total, disjoint, and acyclic in submission order")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
