#!/usr/bin/env python3
"""Build and audit the complete general sine-theta source surface.

The default repository target intentionally does not cover this source tree.
This tool therefore rebuilds the relevant roots explicitly before trusting
printed dependency information. Optional natural-input extensions are audited
through their separate facade so the compiler-accepted source facade remains a
stable regression target.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import pathlib
import re
import subprocess
import sys
import tempfile
from collections import deque
from typing import Iterable

EXPECTED_FOUNDATIONS = frozenset({"propext", "Classical.choice", "Quot.sound"})

BASE_BUILD_TARGETS = (
    "DavisKahan.SinTheta.Real.Specializations",
    "DavisKahan.Sources.DavisKahan1970.GeneralSinTheta",
    "DavisKahan.Sources.DavisKahan1970.FullPartIII",
)

EXTENSION_BUILD_TARGETS = (
    "DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras",
    "DavisKahan.SinTheta.Natural.GenuineGeneralized",
    "DavisKahan.SinTheta.Natural.Reducing",
    "DavisKahan.SinTheta.Natural.Bounded",
    "DavisKahan.SinTheta.Natural.GapConvenience",
    "DavisKahan.SinTheta.NaturalTwoSubspace",
    "DavisKahan.SinTheta.Natural.Examples",
    "DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions",
    "DavisKahan.Sources.DavisKahan1970.FullPartIIIExtensions",
)

BASE_ENDPOINTS = (
    "ForMathlib.DavisKahan1970.sinTheta",
    "ForMathlib.DavisKahan1970.sinTheta_complex",
    "ForMathlib.DavisKahan1970.sinTheta_real",
    "ForMathlib.DavisKahan1970.sinTheta_real_spectralSubspace",
    "ForMathlib.DavisKahan1970.generalizedSinTheta",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_complementaryBlock",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_finiteInterval",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_boundedSpecialization",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_real",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_real_complementaryBlock",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_real_spectralSubspace",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_boundedSpecialization_real",
)

EXTENSION_ENDPOINTS = (
    "ForMathlib.DavisKahan1970.sinTheta_spectralSubspace",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_spectralSubspace",
    "ForMathlib.DavisKahan1970.sinTheta_reducingSubspace_complex",
    "ForMathlib.DavisKahan1970.sinTheta_reducingSubspace_real",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_reducingSubspace_complex",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_reducingSubspace_real",
    "ForMathlib.DavisKahan1970.sinTheta_bounded_spectralSubspace",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_bounded_spectralSubspace",
    "ForMathlib.DavisKahan1970.sinTheta_bounded_real_spectralSubspace",
    "ForMathlib.DavisKahan1970.generalizedSinTheta_bounded_real_spectralSubspace",
)

DIRECT_AUDIT_FILES = (
    pathlib.Path("DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullUnboundedAudit.lean"),
)
EXTENSION_AUDIT_FILE = pathlib.Path(
    "DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullGeneralSinThetaExtensionsAudit.lean"
)

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_'.]+)\s*$", re.MULTILINE)
MARKER_RE = re.compile(r"GENERAL_SIN_THETA_AUDIT_BEGIN\s+(.+?)\n(.*?)GENERAL_SIN_THETA_AUDIT_END", re.DOTALL)
FOUNDATION_RE = re.compile(r"\[([^\]]*)\]")
BYPASS_RE = re.compile(r"\b(?:sorry|admit|native_decide|axiom)\b")


@dataclasses.dataclass
class CommandResult:
    command: list[str]
    returncode: int
    output: str


def run(command: list[str], cwd: pathlib.Path) -> CommandResult:
    print("+", " ".join(command), flush=True)
    proc = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return CommandResult(command, proc.returncode, proc.stdout)


def find_root() -> pathlib.Path:
    here = pathlib.Path.cwd().resolve()
    for candidate in (here, *here.parents):
        if (candidate / "lakefile.toml").exists() or (candidate / "lakefile.lean").exists():
            return candidate
    raise SystemExit("repository root not found")


def module_to_source(root: pathlib.Path, module: str) -> pathlib.Path | None:
    path = root / (module.replace(".", "/") + ".lean")
    return path if path.exists() else None


def source_to_module(root: pathlib.Path, source: pathlib.Path) -> str:
    return source.relative_to(root).with_suffix("").as_posix().replace("/", ".")


def local_module_graph(root: pathlib.Path) -> tuple[dict[str, list[str]], list[tuple[str, str]]]:
    modules: dict[str, pathlib.Path] = {}
    for top in ("DavisKahan", "ForMathlib"):
        for source in (root / top).rglob("*.lean"):
            modules[source_to_module(root, source)] = source
    graph: dict[str, list[str]] = {}
    missing: list[tuple[str, str]] = []
    for module, source in modules.items():
        imports = IMPORT_RE.findall(source.read_text(encoding="utf8"))
        graph[module] = [item for item in imports if item in modules]
        for item in imports:
            if item.startswith(("DavisKahan.", "ForMathlib.")) and item not in modules:
                missing.append((module, item))
    return graph, missing


def import_cycles(graph: dict[str, list[str]]) -> list[list[str]]:
    state: dict[str, int] = {}
    stack: list[str] = []
    cycles: list[list[str]] = []

    def visit(module: str) -> None:
        state[module] = 1
        stack.append(module)
        for imported in graph[module]:
            mark = state.get(imported, 0)
            if mark == 0:
                visit(imported)
            elif mark == 1:
                start = stack.index(imported)
                cycles.append([*stack[start:], imported])
        stack.pop()
        state[module] = 2

    for module in graph:
        if state.get(module, 0) == 0:
            visit(module)
    return cycles


def transitive_imports(graph: dict[str, list[str]], roots: Iterable[str]) -> set[str]:
    seen: set[str] = set()
    queue = deque(roots)
    while queue:
        module = queue.popleft()
        if module in seen:
            continue
        seen.add(module)
        queue.extend(graph.get(module, ()))
    return seen


def changed_lean_bypasses(root: pathlib.Path) -> list[str]:
    result = run(["git", "status", "--short"], root)
    if result.returncode != 0:
        return ["git status failed"]
    findings: list[str] = []
    for line in result.output.splitlines():
        if len(line) < 4:
            continue
        rel = pathlib.Path(line[3:])
        if rel.suffix != ".lean" or not (root / rel).exists():
            continue
        for number, text in enumerate((root / rel).read_text(encoding="utf8").splitlines(), 1):
            if BYPASS_RE.search(text):
                findings.append(f"{rel}:{number}:{text.strip()}")
    return findings


def compiled_artifact_status(root: pathlib.Path) -> tuple[list[str], list[str]]:
    missing: list[str] = []
    stale: list[str] = []
    build_root = root / ".lake/build/lib/lean"
    for top in ("DavisKahan", "ForMathlib"):
        for source in (root / top).rglob("*.lean"):
            relative = source.relative_to(root).with_suffix(".olean")
            artifact = build_root / relative
            if not artifact.exists():
                missing.append(str(source.relative_to(root)))
            elif artifact.stat().st_mtime < source.stat().st_mtime:
                stale.append(str(source.relative_to(root)))
    return missing, stale


def make_audit_source(import_module: str, endpoints: Iterable[str]) -> str:
    lines = [f"import {import_module}", ""]
    for endpoint in endpoints:
        lines.extend([
            f'#eval IO.println "GENERAL_SIN_THETA_AUDIT_BEGIN {endpoint}"',
            f"#print axioms {endpoint}",
            '#eval IO.println "GENERAL_SIN_THETA_AUDIT_END"',
        ])
    return "\n".join(lines) + "\n"


def parse_foundations(output: str, endpoints: Iterable[str]) -> dict[str, list[str] | None]:
    result: dict[str, list[str] | None] = {name: None for name in endpoints}
    for match in MARKER_RE.finditer(output):
        name = match.group(1).strip()
        body = match.group(2)
        lists = FOUNDATION_RE.findall(body)
        if not lists:
            result[name] = []
            continue
        items = [item.strip() for item in lists[-1].split(",") if item.strip()]
        result[name] = items
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--extensions", action="store_true", help="also build and audit optional natural-input extensions")
    parser.add_argument("--no-build", action="store_true", help="skip rebuilding targets; dependency output may then be stale")
    parser.add_argument("--strict-unbuilt", action="store_true", help="fail if any local Lean source lacks a current compiled artifact")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    root = find_root()
    graph, missing_imports = local_module_graph(root)
    cycles = import_cycles(graph)
    endpoints = [*BASE_ENDPOINTS]
    target_modules = [*BASE_BUILD_TARGETS]
    import_module = "DavisKahan.Sources.DavisKahan1970.GeneralSinTheta"
    if args.extensions:
        endpoints.extend(EXTENSION_ENDPOINTS)
        target_modules.extend(EXTENSION_BUILD_TARGETS)
        import_module = "DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions"

    summary: dict[str, object] = {
        "base_commit": run(["git", "rev-parse", "HEAD"], root).output.strip(),
        "extensions": args.extensions,
        "targets": target_modules,
        "endpoints": endpoints,
        "missing_imports": missing_imports,
        "import_cycles": cycles,
        "proof_bypasses_in_changed_lean": changed_lean_bypasses(root),
    }

    build_ok = True
    if not args.no_build:
        build = run(["lake", "build", *target_modules], root)
        print(build.output, end="")
        build_ok = build.returncode == 0
        summary["build_ok"] = build_ok
        if build_ok:
            for audit_file in DIRECT_AUDIT_FILES:
                direct = run(["lake", "env", "lean", str(audit_file)], root)
                print(direct.output, end="")
                if direct.returncode != 0:
                    build_ok = False
            if args.extensions:
                direct = run(["lake", "env", "lean", str(EXTENSION_AUDIT_FILE)], root)
                print(direct.output, end="")
                if direct.returncode != 0:
                    build_ok = False

    dependency_result: dict[str, list[str] | None] = {}
    dependency_clean = False
    if build_ok:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", prefix="GeneralSinThetaAudit_",
            dir=root, delete=False, encoding="utf8"
        ) as file:
            audit_path = pathlib.Path(file.name)
            file.write(make_audit_source(import_module, endpoints))
        try:
            audit = run(["lake", "env", "lean", str(audit_path)], root)
            print(audit.output, end="")
        finally:
            audit_path.unlink(missing_ok=True)
        dependency_result = parse_foundations(audit.output, endpoints)
        dependency_clean = audit.returncode == 0 and all(
            deps is not None and frozenset(deps) == EXPECTED_FOUNDATIONS
            for deps in dependency_result.values()
        )
    summary["dependency_results"] = dependency_result
    summary["dependency_clean"] = dependency_clean

    missing_oleans, stale_oleans = compiled_artifact_status(root)
    summary["missing_oleans"] = missing_oleans
    summary["stale_oleans"] = stale_oleans

    extension_cone = transitive_imports(
        graph,
        ["DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions"]
        if args.extensions else ["DavisKahan.Sources.DavisKahan1970.GeneralSinTheta"],
    )
    summary["legacy_ordered_engine_reachable"] = (
        "DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineOrderedEngineLegacy"
        in extension_cone
    )

    ok = (
        build_ok
        and dependency_clean
        and not missing_imports
        and not cycles
        and not summary["proof_bypasses_in_changed_lean"]
        and not summary["legacy_ordered_engine_reachable"]
    )
    if args.strict_unbuilt:
        ok = ok and not missing_oleans and not stale_oleans

    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("General sine-theta source audit:", "CLEAN" if ok else "OPEN")
        if missing_oleans:
            print(f"Unbuilt local modules: {len(missing_oleans)}")
        if stale_oleans:
            print(f"Stale local modules: {len(stale_oleans)}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
