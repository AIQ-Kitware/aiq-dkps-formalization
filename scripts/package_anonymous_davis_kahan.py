#!/usr/bin/env python3
"""Build a small anonymous source archive for the Davis--Kahan formalization.

The archive contains the transitive *local* Lean import closure of
DavisKahan/All.lean, plus the minimal Lake metadata needed to build it.
It intentionally excludes Git history, papers, dev logs, screenshots,
submodules, and unrelated formalizations.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import zipfile
from pathlib import Path

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")
HEX_TOKEN_RE = re.compile(r"(?<![0-9A-Fa-f])[0-9A-Fa-f]{7,40}(?![0-9A-Fa-f])")

# Identity-bearing strings that must not survive into the artifact.
LEAK_PATTERNS = [
    re.compile(r"\bJon\b", re.I),
    re.compile(r"\bCrall\b", re.I),
    re.compile(r"\bKitware\b", re.I),
    re.compile(r"\bErotemic\b", re.I),
    re.compile(r"\bAIQ(?:-Kitware)?\b", re.I),
    re.compile(r"jon[._-]?crall", re.I),
    re.compile(r"aiq[-_]dkps[-_]formalization", re.I),
    re.compile(r"github\.com/AIQ-Kitware", re.I),
]


def run_git(repo: Path, *args: str) -> str:
    cmd = ["git", "-c", f"safe.directory={repo}", *args]
    return subprocess.check_output(cmd, cwd=repo, text=True).strip()


def find_repo(start: Path) -> Path:
    root = subprocess.check_output(
        ["git", "-c", f"safe.directory={start.resolve()}", "-C", str(start), "rev-parse", "--show-toplevel"],
        text=True,
    ).strip()
    return Path(root).resolve()


def require_clean(repo: Path) -> None:
    dirty = run_git(repo, "status", "--porcelain")
    if dirty:
        raise SystemExit(
            "Refusing to package a dirty working tree. Commit/stash changes first, "
            "or rerun with --allow-dirty."
        )


def module_path(repo: Path, module: str) -> Path | None:
    path = repo / (module.replace(".", "/") + ".lean")
    return path if path.is_file() else None


def local_import_closure(repo: Path, entries: list[Path]) -> list[Path]:
    """Return every repo-local Lean source transitively imported by entries."""
    seen: set[Path] = set()
    stack = [p.resolve() for p in entries]

    while stack:
        path = stack.pop()
        if path in seen:
            continue
        if not path.is_file() or repo not in path.parents:
            raise SystemExit(f"Invalid local entry/import: {path}")
        seen.add(path)

        text = path.read_text(encoding="utf-8")
        for line in text.splitlines():
            match = IMPORT_RE.match(line)
            if not match:
                continue
            for module in match.group(1).split():
                dep = module_path(repo, module)
                if dep is not None:
                    stack.append(dep.resolve())

    return sorted(seen)


def local_commit_aliases(repo: Path) -> tuple[list[str], dict[str, str]]:
    commits = [x for x in run_git(repo, "rev-list", "--all").splitlines() if x]
    aliases = {sha: f"anoncommit{idx:04d}" for idx, sha in enumerate(sorted(commits), 1)}
    return commits, aliases


def anonymize_text(text: str, commits: list[str], aliases: dict[str, str]) -> str:
    # Header/provenance identities.
    text = re.sub(
        r"Copyright \(c\) 2026 Kitware, Inc\. All rights reserved\.",
        "Copyright (c) 2026 Anonymous Authors. All rights reserved.",
        text,
        flags=re.I,
    )
    text = re.sub(r"^Authors?:.*$", "Authors: Anonymous", text, flags=re.I | re.M)
    text = re.sub(r"`edward \(aiq-gpu\)`", "`a parallel development`", text, flags=re.I)
    text = re.sub(r"`jon \(toothbrush\)`", "`an anonymous contributor`", text, flags=re.I)
    text = re.sub(r"\bJon\s+Crall\b", "Anonymous Author", text, flags=re.I)
    text = re.sub(r"\bJon\b", "Anonymous Contributor", text, flags=re.I)
    text = re.sub(r"\bKitware(?:,\s*)?Inc\.?", "Anonymous Authors", text, flags=re.I)
    text = re.sub(r"\bKitware\b", "Anonymous Institution", text, flags=re.I)
    text = re.sub(r"\bErotemic\b", "anonymous-user", text, flags=re.I)
    text = re.sub(r"jon[._-]?crall", "anonymous-user", text, flags=re.I)

    # Repository / organization identifiers.
    text = re.sub(
        r"https?://github\.com/AIQ-Kitware/aiq-dkps-formalization(?:\.git)?",
        "https://example.invalid/anonymous-davis-kahan-formalization",
        text,
        flags=re.I,
    )
    text = re.sub(r"aiq[-_]dkps[-_]formalization", "anonymous-davis-kahan-formalization", text, flags=re.I)
    text = re.sub(r"\bAIQ-Kitware\b", "Anonymous Organization", text, flags=re.I)
    text = re.sub(r"\bAIQ\b", "anonymous project", text, flags=re.I)
    text = re.sub(r"aiq-gpu", "anonymous development", text, flags=re.I)

    # Replace references to this repository's own commits, including abbreviated SHAs.
    def replace_commit(match: re.Match[str]) -> str:
        token = match.group(0).lower()
        matches = [sha for sha in commits if sha.startswith(token)]
        if len(matches) == 1:
            return aliases[matches[0]]
        return match.group(0)

    return HEX_TOKEN_RE.sub(replace_commit, text)


def slim_lakefile(manifest: dict) -> str:
    packages = {p["name"]: p for p in manifest["packages"]}
    mathlib = packages["mathlib"]
    return f'''name = "anonymous_davis_kahan_formalization"
version = "0.1.0"
defaultTargets = ["DavisKahan.All"]

[leanOptions]
pp.unicode.fun = true
autoImplicit = false

[[require]]
name = "mathlib"
git = "{mathlib['url']}"
rev = "{mathlib['rev']}"

[[lean_lib]]
name = "ForTauCeti"
globs = ["ForTauCeti.*"]
leanOptions = {{ warningAsError = true, weak.linter.mathlibStandardSet = true, weak.linter.style.longFile = 1500, weak.linter.style.longFileDefValue = 1500, weak.linter.style.header = false }}

[[lean_lib]]
name = "DavisKahan"
'''


def audit_tree(root: Path, commits: list[str]) -> None:
    commit_prefixes = {sha[:n] for sha in commits for n in range(7, 41)}
    failures: list[str] = []

    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        rel = path.relative_to(root)
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            failures.append(f"unexpected binary file: {rel}")
            continue

        for pattern in LEAK_PATTERNS:
            if pattern.search(str(rel)) or pattern.search(text):
                failures.append(f"identity pattern {pattern.pattern!r}: {rel}")

        for match in HEX_TOKEN_RE.finditer(text):
            if match.group(0).lower() in commit_prefixes:
                failures.append(f"source-repository commit id {match.group(0)}: {rel}")

    if failures:
        preview = "\n".join(f"  - {x}" for x in failures[:50])
        extra = "" if len(failures) <= 50 else f"\n  ... and {len(failures) - 50} more"
        raise SystemExit(f"Anonymization audit failed:\n{preview}{extra}")


def write_zip(tree: Path, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for path in sorted(p for p in tree.rglob("*") if p.is_file()):
            rel = path.relative_to(tree).as_posix()
            info = zipfile.ZipInfo(rel, date_time=(1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            zf.writestr(info, path.read_bytes())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--entry", action="append", default=None,
                        help="repo-relative Lean entry file (default: DavisKahan/All.lean)")
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--allow-dirty", action="store_true")
    args = parser.parse_args()

    repo = find_repo(args.repo)
    if not args.allow_dirty:
        require_clean(repo)

    entry_names = args.entry or ["DavisKahan/All.lean"]
    entries = [repo / name for name in entry_names]
    sources = local_import_closure(repo, entries)

    # This root is harmless/useful for the extracted ForTauCeti lean_lib.
    if (repo / "ForTauCeti.lean").is_file():
        sources.append(repo / "ForTauCeti.lean")
    sources = sorted(set(sources))

    manifest = json.loads((repo / "lake-manifest.json").read_text(encoding="utf-8"))
    commits, aliases = local_commit_aliases(repo)

    output = args.output or (repo.parent / "anonymous-davis-kahan-formalization.zip")
    output = output.resolve()

    with tempfile.TemporaryDirectory(prefix="anon-dk-") as tmp:
        tree = Path(tmp) / "anonymous-davis-kahan-formalization"
        tree.mkdir()

        for src in sources:
            rel = src.relative_to(repo)
            dst = tree / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            text = src.read_text(encoding="utf-8")
            dst.write_text(anonymize_text(text, commits, aliases), encoding="utf-8")

        # Minimal standalone build metadata. No .git, original README, dev logs, etc.
        (tree / "lean-toolchain").write_text(
            (repo / "lean-toolchain").read_text(encoding="utf-8"), encoding="utf-8"
        )
        (tree / "lakefile.toml").write_text(slim_lakefile(manifest), encoding="utf-8")
        if (repo / "LICENSE").is_file():
            license_text = (repo / "LICENSE").read_text(encoding="utf-8")
            (tree / "LICENSE").write_text(
                anonymize_text(license_text, commits, aliases), encoding="utf-8"
            )
        (tree / "README.md").write_text(
            "# Anonymous Davis--Kahan formalization artifact\n\n"
            "This archive contains the transitive local Lean dependencies of "
            "`DavisKahan/All.lean`.\n\n"
            "Build with:\n\n```bash\nlake update\nlake build DavisKahan.All\n```\n",
            encoding="utf-8",
        )

        audit_tree(tree, commits)
        write_zip(tree, output)

    print(f"Wrote {output}")
    print(f"Included {len(sources)} Lean source files")


if __name__ == "__main__":
    main()
