#!/usr/bin/env python3
"""Create a double-blind copy of the tracked repository files.

The copy contains only paths known to Git, omits files handled by a ``crypt``
clean/smudge filter, rewrites known author/institution/repository identifiers in
UTF-8 text files, copies binary files unchanged, and fails if a known identifier
remains in either text or binary payloads.

This intentionally does not copy ``.git`` or Git history. Gitlink/submodule
entries are reported and omitted; their URLs in ``.gitmodules`` are anonymized
with the rest of the text files.
"""
from __future__ import annotations

import argparse
import datetime as datetime_mod
import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Replacement:
    pattern: re.Pattern[str]
    replacement: str


REPLACEMENTS = (
    # Match full email addresses before replacing aliases embedded in their local part.
    Replacement(
        re.compile(r"[A-Z0-9._%+\-]+@(?:kitware\.com|jhu\.edu)", re.I),
        "<ANONYMIZED_EMAIL>",
    ),
    Replacement(re.compile(r"\bJonathan\s+Crall\b", re.I), "<ANONYMIZED_AUTHOR_1>"),
    Replacement(re.compile(r"\bJon\s+Crall\b", re.I), "<ANONYMIZED_AUTHOR_1>"),
    Replacement(re.compile(r"\bjoncrall\b", re.I), "<ANONYMIZED_AUTHOR_1>"),
    Replacement(re.compile(r"\berotemic\b", re.I), "<ANONYMIZED_AUTHOR_1>"),
    Replacement(re.compile(r"\bcrall2026llmresource\b", re.I), "anonymous2026llmresource"),
    Replacement(re.compile(r"\bBrian\s+Hu\b", re.I), "<ANONYMIZED_AUTHOR_2>"),
    Replacement(re.compile(r"\bbrian[._-]hu\b", re.I), "<ANONYMIZED_AUTHOR_2>"),
    Replacement(re.compile(r"\bEdward\s+Wang\b", re.I), "<ANONYMIZED_AUTHOR_3>"),
    Replacement(re.compile(r"\bedward[._-]wang\b", re.I), "<ANONYMIZED_AUTHOR_3>"),
    Replacement(re.compile(r"\bCarey\s+E\.?\s+Priebe\b", re.I), "<ANONYMIZED_AUTHOR_4>"),
    Replacement(re.compile(r"\bCarey\s+Priebe\b", re.I), "<ANONYMIZED_AUTHOR_4>"),
    Replacement(re.compile(r"\bcarey[._-]priebe\b", re.I), "<ANONYMIZED_AUTHOR_4>"),
    Replacement(re.compile(r"\bcpriebe\b", re.I), "<ANONYMIZED_AUTHOR_4>"),
    Replacement(re.compile(r"\bAIQ-Kitware\b", re.I), "<ANONYMIZED_GITHUB_ORG>"),
    Replacement(re.compile(r"\bKitware(?:ans?|,\s*Inc\.)?\b", re.I), "<ANONYMIZED_ORGANIZATION_1>"),
    Replacement(re.compile(r"\bJohns\s+Hopkins\s+University\b", re.I), "<ANONYMIZED_ORGANIZATION_2>"),
    Replacement(re.compile(r"\bJohns\s+Hopkins\b", re.I), "<ANONYMIZED_ORGANIZATION_2>"),
    Replacement(re.compile(r"\bHR001125CE017\b", re.I), "<ANONYMIZED_CONTRACT>"),
)

# Known identity-bearing path components are rewritten independently of file
# contents. Keeping this list explicit avoids broad substitutions of common
# first names elsewhere in the repository.
PATH_REPLACEMENTS = (
    ("dev/posthoc-prompt-analysis/findings/aiq-gpu-edward/",
     "dev/posthoc-prompt-analysis/findings/aiq-gpu-author3/"),
    ("dev/posthoc-prompt-analysis/findings/aivm-2404-edward/",
     "dev/posthoc-prompt-analysis/findings/aivm-2404-author3/"),
    ("dev/posthoc-prompt-analysis/findings/aivm-2404-jon/",
     "dev/posthoc-prompt-analysis/findings/aivm-2404-author1/"),
    ("dev/posthoc-prompt-analysis/findings/toothbrush-jon/",
     "dev/posthoc-prompt-analysis/findings/workstation-author1/"),
)

# These tracked artifacts cannot be safely rewritten in place. The tally tool
# is a zipapp with an author alias embedded in its payload. The anonymizer itself
# contains the private replacement vocabulary by design. Both are omitted and
# listed in ANONYMIZATION_REPORT.txt.
OMIT_PATHS = {
    ".llm_resource_tally/tool",
    "papers/formalization_process_4page/scripts/anonymize_repo.py",
}

# Binary files are not rewritten. These byte strings are therefore checked
# after copying so embedded metadata cannot carry an obvious identity leak.
BINARY_NEEDLES = tuple(
    s.lower().encode("ascii")
    for s in (
        "Jonathan Crall",
        "Jon Crall",
        "joncrall",
        "erotemic",
        "Brian Hu",
        "Edward Wang",
        "Carey E. Priebe",
        "Carey Priebe",
        "AIQ-Kitware",
        "Kitware",
        "Johns Hopkins University",
        "Johns Hopkins",
        "HR001125CE017",
    )
)


def _git(repo: Path, *args: str, input_bytes: bytes | None = None) -> bytes:
    cmd = ["git", "-c", f"safe.directory={repo}", "-C", os.fspath(repo), *args]
    proc = subprocess.run(cmd, input=input_bytes, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if proc.returncode:
        raise RuntimeError(
            f"git command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"{proc.stderr.decode('utf8', errors='replace')}"
        )
    return proc.stdout


def find_repo(start: Path) -> Path:
    start = start.resolve()
    proc = subprocess.run(
        ["git", "-c", "safe.directory=*", "-C", os.fspath(start), "rev-parse", "--show-toplevel"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode:
        raise RuntimeError(proc.stderr.decode("utf8", errors="replace"))
    return Path(proc.stdout.decode("utf8").strip()).resolve()


def tracked_entries(repo: Path) -> list[tuple[str, str]]:
    """Return ``(mode, relative_path)`` pairs from the Git index."""
    raw = _git(repo, "ls-files", "-s", "-z")
    entries: list[tuple[str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        prefix, path_b = record.split(b"\t", 1)
        mode = prefix.split(b" ", 1)[0].decode("ascii")
        path = path_b.decode("utf8")
        entries.append((mode, path))
    return entries


def filter_attributes(repo: Path, paths: list[str]) -> dict[str, str]:
    if not paths:
        return {}
    stdin = b"\0".join(p.encode("utf8") for p in paths) + b"\0"
    raw = _git(repo, "check-attr", "-z", "--stdin", "filter", input_bytes=stdin)
    parts = raw.split(b"\0")
    if parts and parts[-1] == b"":
        parts.pop()
    if len(parts) % 3:
        raise RuntimeError("Unexpected git check-attr -z output")
    result = {}
    for idx in range(0, len(parts), 3):
        path, attr, value = (p.decode("utf8") for p in parts[idx:idx + 3])
        if attr != "filter":
            raise RuntimeError(f"Unexpected Git attribute {attr!r} for {path}")
        result[path] = value
    return result


def anonymize_text(text: str) -> tuple[str, bool]:
    changed = False
    for item in REPLACEMENTS:
        text2, count = item.pattern.subn(item.replacement, text)
        if count:
            changed = True
            text = text2
    return text, changed


def anonymize_path(rel_path: str) -> str:
    result = rel_path
    for source, replacement in PATH_REPLACEMENTS:
        result = result.replace(source, replacement)
    return result


def residual_text_matches(text: str) -> list[str]:
    residual = []
    for item in REPLACEMENTS:
        if item.pattern.search(text):
            residual.append(item.pattern.pattern)
    return residual


def binary_residuals(data: bytes) -> list[str]:
    lower = data.lower()
    return [needle.decode("ascii") for needle in BINARY_NEEDLES if needle in lower]


def prepare_output(output: Path, force: bool) -> None:
    if output.exists():
        if not force:
            raise FileExistsError(f"Output already exists: {output}. Use --force to replace it.")
        if output.is_dir():
            shutil.rmtree(output)
        else:
            output.unlink()
    output.mkdir(parents=True)


def build_anonymous_copy(repo: Path, output: Path, force: bool = False) -> None:
    repo = repo.resolve()
    output = output.resolve()
    try:
        output.relative_to(repo)
    except ValueError:
        pass
    else:
        raise ValueError("Output must be outside the source repository")

    prepare_output(output, force=force)
    entries = tracked_entries(repo)
    paths = [path for _mode, path in entries]
    attrs = filter_attributes(repo, paths)

    changed_paths: list[str] = []
    skipped_crypt: list[str] = []
    skipped_gitlinks: list[str] = []
    omitted_paths: list[str] = []
    copied_binary: list[str] = []
    residual_errors: list[str] = []

    for mode, rel_path in entries:
        if rel_path in OMIT_PATHS:
            omitted_paths.append(rel_path)
            continue
        if mode == "160000":
            skipped_gitlinks.append(rel_path)
            continue
        if attrs.get(rel_path) == "crypt":
            skipped_crypt.append(rel_path)
            continue

        src = repo / rel_path
        anonymous_rel_path = anonymize_path(rel_path)
        dst = output / anonymous_rel_path
        dst.parent.mkdir(parents=True, exist_ok=True)

        if src.is_symlink():
            target = os.readlink(src)
            target2, changed = anonymize_text(target)
            if residual_text_matches(target2):
                residual_errors.append(f"symlink target: {rel_path}")
                continue
            os.symlink(target2, dst)
            if changed:
                changed_paths.append(rel_path)
            continue

        if not src.is_file():
            residual_errors.append(f"tracked path is unavailable as a file: {rel_path}")
            continue

        data = src.read_bytes()
        try:
            text = data.decode("utf8")
        except UnicodeDecodeError:
            shutil.copy2(src, dst)
            copied_binary.append(rel_path)
            found = binary_residuals(data)
            if found:
                residual_errors.append(
                    f"binary metadata: {rel_path}: {', '.join(sorted(set(found)))}"
                )
            continue

        text2, changed = anonymize_text(text)
        leftovers = residual_text_matches(text2)
        if leftovers:
            residual_errors.append(
                f"text residual: {rel_path}: {', '.join(sorted(set(leftovers)))}"
            )
            continue
        dst.write_text(text2, encoding="utf8")
        shutil.copymode(src, dst, follow_symlinks=False)
        if changed:
            changed_paths.append(rel_path)

    if residual_errors:
        shutil.rmtree(output, ignore_errors=True)
        details = "\n".join(f"  - {item}" for item in residual_errors[:100])
        extra = len(residual_errors) - 100
        if extra > 0:
            details += f"\n  - ... {extra} additional residuals"
        raise RuntimeError(
            "Anonymization audit failed; output was removed. Residual identifiers:\n" + details
        )

    commit = _git(repo, "rev-parse", "HEAD").decode("ascii").strip()
    report = output / "ANONYMIZATION_REPORT.txt"
    report.write_text(
        "Double-blind repository copy\n"
        f"Source commit: {commit}\n"
        f"Tracked index entries: {len(entries)}\n"
        f"Text files changed: {len(changed_paths)}\n"
        f"Binary files copied and byte-audited: {len(copied_binary)}\n"
        f"Encrypted-filter paths omitted: {len(skipped_crypt)}\n"
        f"Gitlink/submodule entries omitted: {len(skipped_gitlinks)}\n"
        f"Explicit identity-bearing paths omitted: {len(omitted_paths)}\n"
        + ("Omitted paths:\n" + "".join(f"  - {path}\n" for path in omitted_paths) if omitted_paths else "")
        + "Git history and .git metadata are not included.\n",
        encoding="utf8",
    )

    print(f"Anonymous repository copy: {output}")
    print(f"  changed text files: {len(changed_paths)}")
    print(f"  copied binary files: {len(copied_binary)}")
    print(f"  omitted encrypted paths: {len(skipped_crypt)}")
    print(f"  omitted gitlinks/submodules: {len(skipped_gitlinks)}")
    print(f"  omitted explicit identity-bearing paths: {len(omitted_paths)}")
    if skipped_gitlinks:
        print("  gitlinks omitted:")
        for path in skipped_gitlinks:
            print(f"    - {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=None,
        help="Repository to copy. Defaults to the Git repository containing this script.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Destination outside the repository. Defaults to a timestamped sibling directory.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Replace an existing output directory.",
    )
    args = parser.parse_args()

    start = args.repo.resolve() if args.repo is not None else Path(__file__).resolve().parent
    repo = find_repo(start)
    if args.output is None:
        stamp = datetime_mod.datetime.now(datetime_mod.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        output = repo.parent / f"{repo.name}-anonymized-{stamp}"
    else:
        output = args.output.expanduser().resolve()
    build_anonymous_copy(repo, output, force=args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
