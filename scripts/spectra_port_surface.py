#!/usr/bin/env python3
"""Aggregate the compiled-environment Spectra census into the port-surface ledger.

Consumes the JSONL produced by ``scripts/ExportSpectraUsage.lean`` and joins it
against two trees:

* ``vendor/Spectra`` — to attribute every used constant to the donor module and
  file that declares it, which is what a provenance record has to cite;
* the pinned ``external/TauCeti`` checkout — to decide, per donor module,
  whether Tau Ceti *collides* with it (has its own object for the same idea),
  is *absent* (a genuine donor gap), or *supersedes* it.

Only files **tracked** in ``external/TauCeti`` count as upstream Tau Ceti.  The
checkout also carries an untracked copy of our own ``ForTauCeti`` staging export
(``scripts/export_for_tauceti.py`` writes it there), and counting that as
upstream would report our own staged work as pre-existing Tau Ceti coverage.

Writes ``dev/tauceti/spectra-port-surface.json``.  Pass ``--check`` to verify the
committed ledger still matches the tree without rewriting it.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
from pathlib import Path

# --------------------------------------------------------------------------
# Lean source scanning
# --------------------------------------------------------------------------

# `namespace`/`end` also occur as ordinary English inside docstrings ("...the
# namespace from outside."), and a scanner that believes them silently corrupts
# every attribution after that line.  Strip comments before tracking scopes.
BLOCK_OPEN = re.compile(r"/-")
BLOCK_CLOSE = re.compile(r"-/")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?₀-₉]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z0-9_.'₀-₉]+)\s*$")
END = re.compile(r"^end\s+([A-Za-z0-9_.'₀-₉]+)\s*$")


def strip_comments(text: str) -> list[str]:
    """Blank out block comments and line comments, preserving line numbering."""
    out, depth = [], 0
    for line in text.splitlines():
        if depth == 0 and "--" in line and not line.lstrip().startswith("/-"):
            line = line.split("--", 1)[0]
        rebuilt, i = [], 0
        while i < len(line):
            if depth == 0 and line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth > 0 and line.startswith("/-", i):
                depth += 1
                i += 2
            else:
                if depth == 0:
                    rebuilt.append(line[i])
                i += 1
        out.append("".join(rebuilt))
    return out


def declared_names(root: Path) -> dict[str, str]:
    """Map fully-qualified declaration name -> module name, for a Lean library root."""
    found: dict[str, str] = {}
    for path in sorted(root.rglob("*.lean")):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        scopes: list[str] = []
        for line in strip_comments(path.read_text(errors="ignore")):
            m = NAMESPACE.match(line)
            if m:
                scopes.append(m.group(1))
                continue
            m = END.match(line)
            if m:
                if scopes and scopes[-1] == m.group(1):
                    scopes.pop()
                continue
            m = DECL.match(line)
            if m:
                found.setdefault(".".join(scopes + [m.group(2)]), module)
    return found


def owning_module(const: str, declared: dict[str, str]) -> str:
    """Attribute a constant to the module declaring its longest declared prefix.

    Structure projections (`Foo.bar`), constructors (`Foo.mk`), instance-derived
    names and `_proof_N` auxiliaries never appear as source declarations, so an
    exact lookup misses them; they belong to whatever declares the object.
    """
    parts = const.split(".")
    for k in range(len(parts), 0, -1):
        prefix = ".".join(parts[:k])
        if prefix in declared:
            return declared[prefix]
    return "?"


# --------------------------------------------------------------------------
# Cluster assignment
# --------------------------------------------------------------------------

# Clusters A-E are the donor clusters already named in
# dev/tauceti/convergence-matrix.md, Wave 5.  F is added here: the Cayley /
# Stone / one-parameter-group bridge, which Wave 5 folded into Wave 3's
# semigroup convergence but which has its own DKPS consumer surface.
CLUSTERS = [
    ("A", "self-adjoint unbounded operators, resolvent and spectrum", (
        "Spectra.Operator.SelfAdjoint", "Spectra.Operator.Symmetric",
        "Spectra.Operator.Bounded", "Spectra.Operator.KatoRellich",
        "Spectra.Operator.Unitary.Basic", "Spectra.Operator.Unitary.Conjugation",
        "Spectra.Resolvent.Defs", "Spectra.Resolvent.Spectrum",
        "Spectra.Resolvent.Range", "Spectra.Resolvent.Identities",
        "Spectra.Resolvent.SpecialCases",
    )),
    ("B", "PVMs, spectral measures and Borel functional calculus", (
        "Spectra.ProjValMeasure.Basic", "Spectra.ProjValMeasure.Map",
        "Spectra.SpectralTheory.Measure.PVM",
        "Spectra.SpectralTheory.Measure.Convergence",
        "Spectra.SpectralTheory.Measure.GeneratorLink",
        "Spectra.SpectralTheory.Calculus.Bounded",
        "Spectra.SpectralTheory.Calculus.SpectralGapInverse",
        "Spectra.SpectralTheory.ResolventForm",
        "Spectra.Bochner.Borel.CDF",
        "Spectra.QuantumMechanics.BornRule.PVM",
        "Spectra.QuantumMechanics.BornRule.Moments",
    )),
    ("C", "polar decomposition and partial isometries", (
        "Spectra.QuantumMechanics.Channels.PolarDecomp",
    )),
    ("D", "Hilbert-Schmidt, tensor products and trace class", (
        "Spectra.Spaces.Tensor.Hilbert", "Spectra.Spaces.Tensor.HilbertSchmidt",
        "Spectra.Spaces.Tensor.HilbertSchmidtFlow",
        "Spectra.SpectralTheory.Antilinear.ConjugateSpace",
    )),
    ("F", "Cayley transform, Stone bridge and one-parameter groups", (
        "Spectra.OneParameterUnitaryGroup.Basic",
        "Spectra.YosidaHille.Basic", "Spectra.YosidaHille.Helpers",
        "Spectra.CayleyTransform.Mobius",
        "Spectra.CayleyTransform.Generator.InverseAction",
        "Spectra.CayleyTransform.Generator.Pushforward",
    )),
]

MISATTRIBUTED = "X"
MISATTRIBUTED_LABEL = (
    "DKPS-authored declarations living inside `namespace Spectra.*` — "
    "not donor material, and a provenance hazard until re-homed"
)

# Per-cluster disposition, decided by reading the pinned checkout.  Two columns,
# because "Tau Ceti already has this" is ambiguous in this repository: the
# `external/TauCeti` working tree also contains our own untracked `ForTauCeti`
# export, and conflating the two reports our staged work as upstream coverage.
#
#   upstream  - what the 629 *tracked* modules of the pinned Tau Ceti contain.
#   staged    - what `ForTauCeti/` in this repository contains.
#
# Values:
#   `collides`   an object for the same mathematics already exists; the port is
#                a reconciliation, and porting the donor verbatim would install
#                a second parallel hierarchy.
#   `partial`    covered at lower generality (finite-dimensional, bounded-only)
#                — a near miss that must not be mistaken for a substitute.
#   `absent`     nothing there; Spectra is a genuine donor and this is an
#                addition needing its own roadmap target.
DISPOSITION = {
    "A": {"upstream": "partial", "staged": "collides"},
    "B": {"upstream": "absent", "staged": "partial"},
    "C": {"upstream": "absent", "staged": "collides"},
    "D": {"upstream": "absent", "staged": "collides"},
    "E": {"upstream": "absent", "staged": "absent"},
    "F": {"upstream": "collides", "staged": "absent"},
    MISATTRIBUTED: {"upstream": "n/a", "staged": "n/a"},
}


def cluster_of(module: str) -> tuple[str, str]:
    if module == MISATTRIBUTED:
        return MISATTRIBUTED, MISATTRIBUTED_LABEL
    for key, label, mods in CLUSTERS:
        if module in mods:
            return key, label
    return "?", "unassigned"


# --------------------------------------------------------------------------

def tracked_tauceti_modules(repo: Path) -> list[str]:
    tc = repo / "external" / "TauCeti"
    if not (tc / ".git").exists():
        return []
    out = subprocess.run(
        ["git", "-C", str(tc), "ls-files", "TauCeti"],
        capture_output=True, text=True, check=False).stdout
    return sorted(p[len("TauCeti/"):-len(".lean")].replace("/", ".")
                  for p in out.splitlines() if p.endswith(".lean"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl", type=Path,
                    help="output of scripts/ExportSpectraUsage.lean")
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--check", action="store_true",
                    help="compare against the committed ledger instead of rewriting it")
    args = ap.parse_args()
    repo = args.repo

    rows = [json.loads(line) for line in args.jsonl.read_text().splitlines() if line.strip()]
    declared = declared_names(repo / "vendor" / "Spectra")

    uses: collections.Counter[str] = collections.Counter()
    consumers: dict[str, set[str]] = collections.defaultdict(set)
    for row in rows:
        for const in row["spectra"]:
            uses[const] += 1
            consumers[const].add(row["consumerModule"])

    by_module: dict[str, dict[str, dict]] = collections.defaultdict(dict)
    for const, count in uses.items():
        module = owning_module(const, declared)
        if module == "?":
            # A `Spectra.*` constant that no vendored file declares was written
            # by us into the donor's namespace.  It is not a port obligation; it
            # is a naming defect, and it has to be visible as one — otherwise the
            # eventual attribution ledger credits Spectra for our theorem.
            module = MISATTRIBUTED
        by_module[module][const] = {
            "uses": count,
            "consumerModules": sorted(consumers[const]),
        }

    clusters: dict[str, dict] = {}
    for module, consts in by_module.items():
        key, label = cluster_of(module)
        entry = clusters.setdefault(key, {
            "label": label,
            "disposition": DISPOSITION.get(key, {"upstream": "unknown", "staged": "unknown"}),
            "donorModules": {},
        })
        entry["donorModules"][module] = {
            "lines": len((repo / "vendor" / "Spectra"
                          / (module.replace(".", "/") + ".lean")).read_text(
                              errors="ignore").splitlines())
            if (repo / "vendor" / "Spectra" / (module.replace(".", "/") + ".lean")).exists()
            else None,
            "constants": consts,
        }

    ledger = {
        "note": "Regenerate with scripts/ExportSpectraUsage.lean + scripts/spectra_port_surface.py.",
        "spectraUpstreamCommit": "8dbaaf6728d1342ae16acf79fd7eef7c59b37e63",
        "productionConsumerDeclarations": len(rows),
        "distinctSpectraConstants": len(uses),
        "donorModules": len(by_module),
        "trackedTauCetiModules": len(tracked_tauceti_modules(repo)),
        "clusters": clusters,
    }

    target = repo / "dev" / "tauceti" / "spectra-port-surface.json"
    rendered = json.dumps(ledger, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not target.exists():
            print(f"missing {target}", file=sys.stderr)
            return 1
        if target.read_text() != rendered:
            print(f"{target} is stale; rerun without --check", file=sys.stderr)
            return 1
        print(f"{target} matches the tree")
        return 0
    target.write_text(rendered)
    print(f"wrote {target}: {len(uses)} constants, {len(by_module)} donor modules, "
          f"{len(rows)} production consumers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
