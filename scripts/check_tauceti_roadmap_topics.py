#!/usr/bin/env python3
"""Validate the candidate Tau Ceti roadmap topic design against the import graph.

`ForTauCetiRoadmap/CANDIDATE-TOPIC-DESIGN.md` partitions every `ForTauCeti`
module into fine-grained topics (`T01`..`T22`, with the `T15a/b/c` split),
ordered so that each is reviewable on its own against a base Tau Ceti has
already accepted. Since 2026-07-30 the topics group into a handful of
**holistic roadmap directories** (one directory covers several topics as its
Parts); the grouping is declared by each roadmap README and validated here,
including acyclicity of the roadmap-level DAG.

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
 [A+"PartialIsometry",A+"PolarDecomposition",A+"PolarIsometry",A+"PolarPartialIsometry",
  A+"NearIsometry",A+"IntertwiningUnitary"]),
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
  "Analysis.Normed.Operator.FiniteRankCompact",
  A+"SpectralCutoff"]+["Analysis.OperatorIdeal.ApproximationNumber."+x for x in
  ["Basic","Adjoint","Compact","CompactHilbert","Core","DiagonalExample","DiagonalSequence","Examples",
   "FiniteDimensional","FiniteRestriction","FiniteValueFibers","FiniteValueSeparation",
   "KyFan",
   "LeadingCutoff","MinMax","MinMaxUpper","SameSequence"]]),
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
 +[A+"SkewAdjointExponential"]),
("T14","Borel functional calculus and projection-valued measures",
 [A+"BorelCalculus."+x for x in ["DiagonalMeasure","Multiplicative","Operator","PVM","Polarization"]]
 +[A+"ProjValMeasure.Basic",A+"ProjValMeasure.Additivity",A+"ProjValMeasure.Subspace",
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
 [A+"LinearPMap."+x for x in ["Closed","Constructions","GraphCore","Sylvester",
   "SubmoduleAdjoint"]]
 +[A+"QuadraticFormBounds",A+"SpectralOrder.Complex"]),
("T15b","Resolvents of self-adjoint LinearPMap operators, and semiboundedness",
 [A+"LinearPMap."+x for x in ["Resolvent","ResolventBound","ResolventOpen",
   "SelfAdjointResolvent","RealLowerBound"]]
 +["Analysis.CStarAlgebra.SelfAdjointGapInverse",A+"SeparatedIntertwiner"]),
# `Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank` is approximation-number
# material by subject but sits here by dependency: it imports `LinearPMap.Constructions`
# (T15a) and `LinearPMap.SpectralFormBounds` (T15c), so filing it under T09 makes T09
# unsubmittable -- `--check` reports it as a forward reference, which is how this was
# caught when the module was lifted out of `DavisKahan` on 2026-07-31.
("T15c","The spectral measure of an unbounded self-adjoint operator, and Stone",
 [A+"LinearPMap."+x for x in ["SpectralMeasure","SpectralMeasure.Construction","SpectralGrid",
   "SpectralSupport","SpectralFormBounds","SpectralGapInverse","SpectralCutOperator",
   "SpectralProjectionGroup","SelfAdjointMaximal","StoneUniqueness","YosidaApproximation"]]
 +["Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank"]
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
 +[A+"DoubleAngle.Vector"]+[A+"BoundedOperator."+x for x in ["Projector","SinTheta"]]
 # `SpectralOrder.Real` is form-bound material by subject and would sit with
 # `SpectralOrder.Complex` in T15a -- but it imports `BoundedOperator.Projector`, which is here,
 # so filing it by subject makes T15a unsubmittable. Same lesson as
 # `ApproximationNumber.GramSpectralRank`: file by dependency, and `--check` is what says so.
 # `Complexification.{Basic,FunctionalCalculus}` are the real-complexification transport layer,
 # lifted out of `DavisKahan` on 2026-07-31, and they sit here because `Basic` imports
 # `SpectralOrder.Real`.  `ApproximationNumber.MinMaxReal` is approximation-number material and
 # belongs with T09 by subject, but it is proved *by complexification* and so imports both of
 # them; filing it under T09 would make T09 unsubmittable.  Third time, same rule.
 +[A+"SpectralOrder.Real",A+"Complexification.Basic",A+"Complexification.FunctionalCalculus",
   "Analysis.OperatorIdeal.ApproximationNumber.MinMaxReal"]
 +[A+"ReducedExtension"]),
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


# Directories that deliberately cover no topic. Each entry must say why, so that a
# permanent known-good finding never trains a reader to skim past real ones.
# Empty since the 2026-07-30 consolidation: the pre-split T15 roadmap
# (`UnboundedOperators/`) was absorbed into `SpectralTheory/`, whose Generality
# bar now opens with the U1 decision it was kept for.
INTENTIONAL_ORPHANS: dict[str, str] = {}


def roadmap_coverage() -> tuple[list, list, list, list, dict]:
    """(covered, missing, unexpected orphans, intentional orphans, dir->topics).

    The directory-to-topic mapping is DERIVED, not maintained: each roadmap README
    declares every topic it covers ("**Topic T19 of the candidate design.**"), so
    writing a new roadmap needs no edit here. A hand-maintained map went stale three
    times in one day -- once per roadmap another agent wrote -- and each time it
    reported that agent's finished work as an ORPHAN covering no topic.

    Since the 2026-07-30 consolidation a roadmap directory covers SEVERAL topics
    (the topics are its Parts, in submission order), so every declaration in a
    README counts, not just the first. A topic declared by two directories is an
    error: the partition of topics into roadmaps must stay disjoint too.
    """
    root = ROOT / "ForTauCetiRoadmap"
    dirs = {d.name for d in root.iterdir() if d.is_dir()} if root.exists() else set()

    declared: dict[str, list[str]] = defaultdict(list)   # topic key -> directories
    undeclared: set[str] = set()
    for name in sorted(dirs):
        readme = root / name / "README.md"
        keys = re.findall(r"\*\*Topic\s+(T\d+[a-c]?)\b", readme.read_text(errors="ignore")) \
            if readme.exists() else []
        if keys:
            for k in dict.fromkeys(keys):     # dedup, keep order
                declared[k].append(name)
        else:
            undeclared.add(name)

    known = {k for k, _, _ in TOPICS}
    covered, missing, doubled = [], [], []
    for key, title, _ in TOPICS:
        owners = declared.get(key, [])
        if len(owners) > 1:
            doubled.append(f"topic {key} declared by {', '.join(owners)}")
        (covered if owners else missing).append((key, title, owners[0] if owners else None))

    # a directory claiming a topic the design does not define is an error, not an orphan
    bogus = sorted(f"{d} (declares unknown topic {k})"
                   for k, ds in declared.items() if k not in known for d in ds)
    intentional = sorted(undeclared & set(INTENTIONAL_ORPHANS))
    orphans = sorted(undeclared - set(INTENTIONAL_ORPHANS)) + bogus + doubled

    groups: dict[str, list[str]] = defaultdict(list)     # directory -> topics, design order
    for key, _, _ in TOPICS:
        owners = declared.get(key, [])
        if owners:
            groups[owners[0]].append(key)
    return covered, missing, orphans, intentional, dict(groups)


def roadmap_dag(groups: dict[str, list[str]], topic_needs: dict[str, set[str]]
                ) -> tuple[dict[str, set[str]], list[str]]:
    """Roadmap-level dependency DAG derived from the topic-level needs.

    Returns (dir -> set of prerequisite dirs, cycle diagnostics). The coarse graph
    must be acyclic or the grouping is wrong: two roadmaps that each contain a topic
    the other's topics import cannot be submitted in any order. This is exactly why
    T05-T08 live in one roadmap (geometry->norms 7 edges, norms->geometry 3)."""
    owner = {t: d for d, ts in groups.items() for t in ts}
    needs: dict[str, set[str]] = {d: set() for d in groups}
    for d, ts in groups.items():
        for t in ts:
            for p in topic_needs.get(t, ()):
                if p in owner and owner[p] != d:
                    needs[d].add(owner[p])
    # Kahn's algorithm; anything left over sits on a cycle.
    left = {d: set(ps) for d, ps in needs.items()}
    while True:
        ready = [d for d, ps in left.items() if not ps]
        if not ready:
            break
        for d in ready:
            del left[d]
        for ps in left.values():
            ps.difference_update(ready)
    cycles = [f"roadmap cycle through: {', '.join(sorted(left))}"] if left else []
    return needs, cycles


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


def topic_needs(d: dict) -> dict[str, set[str]]:
    """Each topic's exact prerequisite topics, derived from the import graph."""
    dep: dict[str, set[str]] = {k: set() for k, _, _ in TOPICS}
    for mod, deps in d["graph"].items():
        if mod not in d["assign"]:
            continue
        for x in deps:
            if x in d["assign"] and d["assign"][x] != d["assign"][mod]:
                dep[d["assign"][mod]].add(d["assign"][x])
    return dep


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="exit 1 on any violation")
    ap.add_argument("--topic", help="list the modules of one topic")
    ap.add_argument("--roadmaps", action="store_true",
                    help="which topics have a roadmap, and which do not")
    ap.add_argument("--needs", action="store_true",
                    help="print each topic's exact prerequisite topics")
    args = ap.parse_args(argv)
    if args.roadmaps:
        covered, missing, orphans, intentional, groups = roadmap_coverage()
        d = analyse()
        needs, cycles = roadmap_dag(groups, topic_needs(d))
        sizes = {k: len(mods) for k, _, mods in TOPICS}
        order = {k: i for i, (k, _, _) in enumerate(TOPICS)}
        print(f"roadmap coverage: {len(covered)}/{len(TOPICS)} topics "
              f"across {len(groups)} roadmaps\n")
        for name in sorted(groups, key=lambda n: min(order[t] for t in groups[n])):
            ts = groups[name]
            n = sum(sizes[t] for t in ts)
            need = sorted(needs[name], key=lambda x: min(order[t] for t in groups[x]))
            print(f"  {name:<30} {' '.join(ts):<28} {n:3} modules  "
                  f"needs: {', '.join(need) if need else '— independent'}")
        print()
        for key, title, dd in missing:
            print(f"  MISSING  {key:<5} {title}")
        for dd in orphans:
            print(f"  ORPHAN   ForTauCetiRoadmap/{dd} covers no topic in the design")
        for dd in intentional:
            print(f"  note: ForTauCetiRoadmap/{dd} covers no topic, intentionally "
                  f"({INTENTIONAL_ORPHANS[dd]})")
        for c in cycles:
            print(f"  CYCLE    {c}")
        bad = len(missing) + len(orphans) + len(cycles)
        if bad:
            print(f"\nroadmap coverage: {bad} violation(s)")
            return 1
        print("\nroadmap coverage: OK — every topic covered by exactly one roadmap, "
              "and the roadmap DAG is acyclic")
        return 0

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
        dep = topic_needs(d)
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

    # The coverage layer is part of the gate: every topic must belong to exactly
    # one roadmap directory, and the roadmap-level DAG must be acyclic.
    covered, missing, orphans, intentional, groups = roadmap_coverage()
    _, cycles = roadmap_dag(groups, topic_needs(d))
    for key, title, _dd in missing:
        print(f"  NO ROADMAP  {key}  {title}")
    for dd in orphans:
        print(f"  ORPHAN  ForTauCetiRoadmap/{dd} covers no topic in the design")
    for c in cycles:
        print(f"  CYCLE  {c}")
    bad += len(missing) + len(orphans) + len(cycles)

    if not args.check:
        print()
        for key, title, mods in TOPICS:
            print(f"  {key}  {len(mods):3}  {title}")
    if bad:
        print(f"\nroadmap topics: {bad} violation(s)")
        return 1
    print("\nroadmap topics: OK — total, disjoint, acyclic in submission order, "
          "and every topic is covered by exactly one roadmap")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
