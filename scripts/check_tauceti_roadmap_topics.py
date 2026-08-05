#!/usr/bin/env python3
"""Validate the candidate Tau Ceti roadmap topic design against the import graph.

`dev/tauceti/roadmap-candidate-topic-design.md` partitions every `ForTauCeti`
module into fine-grained topics (`T01`..`T22`, with the `T15a/b/c` split),
ordered so that each is reviewable on its own against a base Tau Ceti has
already accepted. Since 2026-07-30 the topics group into a handful of
**holistic roadmap directories** (one directory covers several topics as its
Parts); the grouping is declared by the internal roadmap-to-topic map and validated
here, including acyclicity of the roadmap-level DAG.

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
 ["Analysis.SpecialFunctions.Sqrt",A+"BasisSpan",A+"CourantFischer",
  A+"PositiveSqrt",A+"SelfAdjointFunctionalCalculus",A+"OperatorModulus",A+"Spectrum"]),
("T02","Polar decomposition and partial isometries",
 [A+"PartialIsometry",A+"RectangularPartialIsometry",A+"Polar.Decomposition",A+"Polar.Isometry",
  A+"Polar.PartialIsometry",A+"NearIsometry",A+"IntertwiningUnitary"]),
("T03","Singular values and the singular system",
 [A+"Singular.Values",A+"RectangularSingularValues",A+"Singular.System",A+"MoorePenroseInverse"]),
("T26","Inner-product identities, linear isometries, Gram rigidity, orthogonal series, "
       "projection geometry, and reducing subspaces",
 ["Analysis.Normed.Operator.LinearIsometry",A+"Basic"]
 +[A+x for x in ["Gram.Matrix","OrthogonalSeries","Projection.Geometry","ReducingSubspace"]]),
("T04","Projection blocks, the projection gap, and spectral subspaces",
 [A+x for x in ["Projection.Blocks","Projection.Gap","Spectral.Gap","Spectral.Subspace"]]),
("T05","Majorization, Schur-Horn, and unitarily invariant norms",
 ["Analysis.Convex.Majorization",A+"SchurHorn",A+"Singular.Subspace",A+"KyFan",
  A+"UnitarilyInvariantSeminorm"]),
("T06","Principal angles, aligned bases, and finite frames",
 [A+x for x in ["PrincipalAngles","AlignedBasis","FiniteFrame"]]),
("T07","Rectangular unitarily invariant norms",
 [A+"RectangularUnitarilyInvariantSeminorm",A+"TwoDimensionalSingularValues"]
 +[A+"RectangularUnitarilyInvariantSeminorm."+x for x in ["Basic","BlockSum","Instances","Majorization"]]),
("T08","Angle geometry and eigenvalue perturbation",
 [A+x for x in ["Gram.Operator","AngleGeometry","FrameFactorization","HoffmanWielandt","EigenvalueChange"]]),
("T09","Approximation numbers",
 ["SetTheory.Cardinal.Lift","LinearAlgebra.Dimension.RankComp",
  "Analysis.Normed.Operator.FiniteRankCompact",
  A+"Spectral.Cutoff"]+["Analysis.OperatorIdeal.ApproximationNumber."+x for x in
  ["Basic","Adjoint","Compact","CompactHilbert","Core","DiagonalExample","DiagonalSequence","Examples",
   "FiniteDimensional","FiniteRestriction","FiniteValueFibers","FiniteValueSeparation",
   "KyFan",
   "LeadingCutoff","MinMax","MinMaxUpper","SameSequence"]]),
("T10","Symmetric operator ideals and Schatten norms",
 ["Analysis.OperatorIdeal.Family."+x for x in ["Basic","HilbertSchmidt","KyFan","KyFanDominance","OperatorNorm","Schatten","TraceClass"]]
 # `ApproximationNumber.EnergyComparison` is approximation-number material by subject and
 # would sit in T09, but it imports `Family.HilbertSchmidt` (here), so filing it there makes
 # T09 unsubmittable.  Fourth module to hit this; file by dependency and let `--check` say so.
 +["Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison"]
 +[A+"SchattenNorm",A+"HilbertSchmidt.Energy","Analysis.Normed.FiniteLpGauge","Topology.ENNRealLiminf"]
 # `OperatorIdeal.SymmetricGauge` is the Gohberg--Krein symmetric norming function and the
 # abstraction the three concrete gauges are instances of; it belongs with the ideal families
 # it will induce, and it imports only Mathlib, so it sorts to the front of this topic.
 +["Analysis.OperatorIdeal.SymmetricGauge"]
 # Added 2026-08-01 when merging `fable/sylvester-upstream-leaves`, which brought three
 # modules and no topic for any of them, so the partition stopped being total and both
 # `--check` gates went red.  All three are the same subject as the line above:
 # `Normed.SymmetricGauge` is the sequence-space gauge, `Normed.SchattenGauge` the `ℓᵖ`
 # instance of it, and `Family.SymmetricGauge` the ideal family it induces.
 # **`CANDIDATE-TOPIC-DESIGN.md` still does not list them, and that file is `jon`'s.**
 +["Analysis.Normed.SymmetricGauge","Analysis.Normed.SchattenGauge",
   "Analysis.OperatorIdeal.Family.SymmetricGauge"]),
("T11","Hilbert-Schmidt operators",
 [A+"HilbertSchmidt."+x for x in ["Lp","Space","Conjugation","Pythagoras"]]),
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
("T15c","The spectral measure of an unbounded self-adjoint operator, and Stone",
 [A+"LinearPMap."+x for x in ["SpectralMeasure","SpectralMeasure.Construction","SpectralGrid",
   "SpectralSupport","SpectralFormBounds","SpectralGapInverse","SpectralCutOperator",
   "SpectralProjectionGroup","SelfAdjointMaximal","StoneUniqueness","YosidaApproximation"]]
 +[A+"BlockLowerBound"]),
("T23","Approximation numbers and finite ranks of spectral bands",
 ["Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank",
  "Analysis.OperatorIdeal.ApproximationNumber.FinitePVMSelection",
  "Analysis.OperatorIdeal.ApproximationNumber.GramBandPolar"]),
("T16","Sylvester equations and the Rosenblum theorem",
 [A+x for x in ["Rosenblum","CoerciveUnit"]]
 +[A+"Sylvester."+x for x in ["Basic","Interval","SpectralDistance","Bound","Operator"]]
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
   ]
 +[A+"ReducedExtension"]),
("T18","The Yu-Wang-Samworth statistical variant",
 [A+"YuWangSamworth."+x for x in ["Residual","SingularSubspace","Statistics"]]),
("T19","Matrix spectra and spectral measurability",
 ["Analysis.Matrix."+x for x in ["EntrywiseEigenvalue","EntrywiseOpNorm","SpectralFunctionMeasurable","Spectrum"]]
 +["MeasureTheory.Function.ConvergenceInMeasure","MeasureTheory.Measure.Typeclasses.Probability"]),
("T20","Sample moments and matrix concentration",
 ["Probability.Moments."+x for x in ["MatrixConcentration","SampleSecondMoment","SampleMean","Variance"]]
 +["Probability.Moments.CenteredScatter"]),
("T21","Matrix rank factorization and positive semidefiniteness",
 ["LinearAlgebra.Matrix.RankFactorization","LinearAlgebra.Matrix.PosDef"]),
("T22","Berge's maximum theorem and approximate minimizers",
 ["Topology.ApproxMinimizer","Topology.Berge"]),
("T24","Real approximation numbers by complexification",
 ["Analysis.OperatorIdeal.ApproximationNumber.MinMaxReal"]),
("T25","The Hilbert-Schmidt Sylvester flow",
 [A+x for x in ["HilbertSchmidt.Block","Sylvester.BlockEstimate","Sylvester.BlockIdentity",
                "Sylvester.Generator","Sylvester.Group","Sylvester.SpectralGap"]]),
]


# Directories that deliberately cover no topic. Each entry must say why, so that a
# permanent known-good finding never trains a reader to skim past real ones.
# Empty since the 2026-07-30 consolidation: the pre-split T15 roadmap
# (`UnboundedOperators/`) was absorbed into `SpectralTheory/`, whose Generality
# bar now opens with the U1 decision it was kept for.
INTENTIONAL_ORPHANS: dict[str, str] = {}


#: Reserved row of the topic map: topics delivered in `ForTauCeti` that no roadmap
#: proposes.  They stay out of the roadmap graph rather than being force-fitted into a
#: roadmap whose mathematics does not cover them.
UNROADMAPPED = "(delivered, not roadmapped)"


def roadmap_coverage() -> tuple[list, list, list, list, dict]:
    """(covered, missing, unexpected orphans, intentional orphans, dir->topics).

    Public roadmap prose deliberately contains no internal topic keys.  The mapping
    therefore lives in `dev/tauceti/roadmap-topic-map.md`, whose table assigns
    each leaf roadmap directory the fine-grained topics it owns.  A leaf roadmap is a
    directory containing `Suggested.lean`; family indexes and `internal/` are not
    roadmaps and are ignored by construction.
    """
    root = ROOT / "submodules/TauCetiRoadmap/TauCetiRoadmap"
    topic_map = ROOT / "dev" / "tauceti" / "roadmap-topic-map.md"

    # The topic map covers this repository's family only; the submodule carries 24 other
    # families whose Suggested.lean files are not ours to deliver.
    family = "OperatorTheory"
    all_leaves = ({p.parent.relative_to(root).as_posix()
                   for p in root.rglob("Suggested.lean")} if root.exists() else set())
    leaf_dirs = {d for d in all_leaves
                 if d.startswith(family + "/") or d == "BergeMaximumTheorem"}

    rows: dict[str, list[str]] = {}
    if topic_map.exists():
        text = topic_map.read_text(errors="ignore")
        row_re = re.compile(
            r"^\|\s*`([^`]+)`\s*\|\s*((?:T\d+[a-c]?\s*)+)\|\s*$", re.M)
        for directory, raw_keys in row_re.findall(text):
            rows[directory] = re.findall(r"T\d+[a-c]?", raw_keys)

    # A topic may be delivered in `ForTauCeti` and deliberately not proposed in any
    # roadmap.  The map records those against this reserved row; they are neither
    # unowned nor part of the roadmap dependency graph.
    unroadmapped = set(rows.pop(UNROADMAPPED, []))

    declared: dict[str, list[str]] = defaultdict(list)   # topic key -> directories
    for directory, keys in rows.items():
        for key in dict.fromkeys(keys):
            declared[key].append(directory)

    known = {k for k, _, _ in TOPICS}
    covered, missing, doubled, deliberate = [], [], [], []
    for key, title, _ in TOPICS:
        owners = declared.get(key, [])
        if len(owners) > 1:
            doubled.append(f"topic {key} declared by {', '.join(owners)}")
        if key in unroadmapped:
            deliberate.append(f"{key}  {title}")
            continue
        (covered if owners else missing).append((key, title, owners[0] if owners else None))

    bogus_topics = sorted(
        f"{directory} (declares unknown topic {key})"
        for key, directories in declared.items() if key not in known
        for directory in directories)
    unmapped_leaves = sorted(leaf_dirs - set(rows))
    missing_leaves = sorted(
        f"{directory} (mapped directory has no Suggested.lean)"
        for directory in set(rows) - leaf_dirs)
    bogus_unroadmapped = sorted(f"{UNROADMAPPED} declares unknown topic {k}"
                                for k in unroadmapped if k not in known)
    orphans = unmapped_leaves + missing_leaves + bogus_topics + doubled + bogus_unroadmapped

    groups: dict[str, list[str]] = defaultdict(list)     # directory -> topics, design order
    for key, _, _ in TOPICS:
        owners = declared.get(key, [])
        if owners:
            groups[owners[0]].append(key)
    return covered, missing, orphans, deliberate, dict(groups)


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
            print(f"  ORPHAN   {dd} covers no topic in the design")
        for row in intentional:
            print(f"  note: {row} — delivered, not proposed by any roadmap")
        for c in cycles:
            print(f"  CYCLE    {c}")
        bad = len(missing) + len(orphans) + len(cycles)
        if bad:
            print(f"\nroadmap coverage: {bad} violation(s)")
            return 1
        print("\nroadmap coverage: OK — every roadmapped topic covered by exactly one "
              "roadmap, and the roadmap DAG is acyclic")
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
        print(f"  ORPHAN  {dd} covers no topic in the design")
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
