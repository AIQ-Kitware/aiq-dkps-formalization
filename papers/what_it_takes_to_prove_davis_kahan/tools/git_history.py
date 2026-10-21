#!/usr/bin/env python3
"""Read-only Git archaeology for the Davis--Kahan mathematical-history study.

This program never checks out, fetches, resets, or modifies Git refs. All
historical evidence is resolved to a full commit hash and Git blob object ID.
It reports what a repository contained, not what a mathematician knew or proved.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

PAPER = Path(__file__).resolve().parents[1]
DEFAULT_REPO = PAPER.parents[1]
TARGETS = PAPER / "data/history_targets.json"
REVIEWED = PAPER / "data/reviewed_git_evidence.csv"
DEFAULT_OUTPUT = "build/what-it-takes-dk/history"


class EvidenceError(Exception):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_path(value: str) -> str:
    """Require a literal repository-relative file, not a Git option or revision."""
    if not value or "\\" in value or ":" in value or "\x00" in value:
        raise EvidenceError(f"invalid repository path: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or any(p in ("", ".", "..") for p in value.split("/")):
        raise EvidenceError(f"path must be relative with no parent traversal: {value!r}")
    if value.startswith("-"):
        raise EvidenceError(f"path may not begin with '-': {value!r}")
    return value


def safe_ref(ref: str) -> str:
    if not ref or ref.startswith("-") or "\x00" in ref or ":" in ref or " " in ref:
        raise EvidenceError(f"invalid Git revision: {ref!r}")
    return ref


def load_targets(path: Path = TARGETS) -> dict:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if obj.get("schema") != "dk-proof-archaeology/git-history-targets/v1":
        raise EvidenceError(f"unrecognized target schema in {path}")
    return obj["cases"]


def case_config(name: str, path: Path = TARGETS) -> dict:
    cases = load_targets(path)
    if name not in cases:
        raise EvidenceError(f"unknown research case {name!r}; choose {', '.join(sorted(cases))}")
    result = cases[name]
    for p in result["paths"]:
        canonical_path(p)
    return result


@dataclass
class Git:
    root: Path

    def run(self, *argv: str, allowed: tuple[int, ...] = (0,)) -> subprocess.CompletedProcess[bytes]:
        proc = subprocess.run(["git", "-C", str(self.root), *argv],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if proc.returncode not in allowed:
            problem = proc.stderr.decode("utf-8", "replace").strip()
            raise EvidenceError(f"git {' '.join(argv[:4])} failed ({proc.returncode}): {problem}")
        return proc

    def value(self, *argv: str, allowed: tuple[int, ...] = (0,)) -> str:
        return self.run(*argv, allowed=allowed).stdout.decode("utf-8", "replace").strip()

    def check(self) -> None:
        self.value("rev-parse", "--show-toplevel")
        if self.value("rev-parse", "--is-inside-work-tree") != "true":
            raise EvidenceError("--repo must point into a Git working tree")

    def commit(self, ref: str) -> str:
        return self.value("rev-parse", "--verify", safe_ref(ref) + "^{commit}")

    def object_at(self, sha: str, path: str) -> tuple[str, bytes] | None:
        path = canonical_path(path)
        entry = self.run("ls-tree", "-z", sha, "--", path).stdout
        rows = [r for r in entry.split(b"\x00") if r]
        # Exact path match is mandatory: ls-tree can also return an enclosing tree.
        matches = []
        for row in rows:
            metadata, sep, name = row.partition(b"\t")
            if sep and name.decode("utf-8", "surrogateescape") == path:
                fields = metadata.decode("ascii").split()
                if len(fields) == 3:
                    matches.append((fields[0], fields[1], fields[2]))
        if not matches:
            return None
        mode, kind, oid = matches[0]
        if kind != "blob" or mode == "120000":
            raise EvidenceError(f"{sha}:{path} is not a regular file (mode {mode}, type {kind})")
        return oid, self.run("cat-file", "blob", oid).stdout

    def meta(self, sha: str) -> dict:
        raw = self.value("show", "-s", "--format=%H%x1f%P%x1f%aI%x1f%cI%x1f%an%x1f%s", sha)
        parts = raw.split("\x1f", 5)
        if len(parts) != 6:
            raise EvidenceError(f"unexpected git show metadata for {sha}")
        return dict(zip(("commit", "parents", "author_date", "commit_date", "author", "subject"), parts))

    def status(self) -> dict:
        self.check()
        names = self.value("for-each-ref", "--format=%(refname)").splitlines()
        promisor = self.value("config", "--get-regexp", "^remote\\..*\\.promisor$", allowed=(0, 1))
        return {
            "root": self.value("rev-parse", "--show-toplevel"),
            "head": self.commit("HEAD"),
            "shallow": self.value("rev-parse", "--is-shallow-repository") == "true",
            "promisor_remotes": any(line.split()[-1].lower() in ("true", "yes", "1") for line in promisor.splitlines() if line.split()),
            "local_ref_count": len(names),
            "refs": names,
            "head_history_commit_count": int(self.value("rev-list", "--count", "HEAD")),
            "tracked_worktree_dirty": bool(self.value("status", "--porcelain", "--untracked-files=no")),
            "limits": "Git sees only locally available reachable objects. Shallow/promisor/absent refs can hide history; no network fetch is performed."
        }


def lines_of(blob: bytes) -> list[bytes]:
    return blob.splitlines(keepends=True)


def excerpt(blob: bytes, start: int, end: int) -> bytes:
    seq = lines_of(blob)
    if start < 1 or end < start or end > len(seq):
        raise EvidenceError(f"line interval {start}..{end} outside file with {len(seq)} lines")
    return b"".join(seq[start - 1:end])


def snippet_as_text(blob: bytes, start: int, end: int) -> str:
    rows = lines_of(blob)
    return "".join(f"{i}: {rows[i-1].decode('utf-8','replace').rstrip()}\n"
                   for i in range(start, end + 1))


def literal_hits(blob: bytes, needle: str, limit: int = 50) -> list[int]:
    if not needle:
        raise EvidenceError("literal needle must be nonempty")
    return [i for i, line in enumerate(lines_of(blob), start=1)
            if needle.encode("utf-8") in line][:limit]


def quote(git: Git, rev: str, path: str, start: int | None,
          end: int | None, needle: str | None, context: int) -> dict:
    sha = git.commit(rev)
    found = git.object_at(sha, path)
    if found is None:
        raise EvidenceError(f"{path} does not exist at {sha}; inspect Git rename history")
    oid, body = found
    count = len(lines_of(body))
    if needle is not None:
        hits = literal_hits(body, needle)
        if not hits:
            raise EvidenceError(f"literal {needle!r} not found in {sha}:{path}")
        if len(hits) > 1:
            raise EvidenceError(f"literal {needle!r} matches {len(hits)} lines in {sha}:{path}; use --start/--end to pick the intended passage")
        start = max(1, hits[0] - context)
        end = min(count, hits[0] + context)
    if start is None:
        raise EvidenceError("choose --needle or --start and --end")
    if end is None:
        end = start
    raw = excerpt(body, start, end)
    result = {
        "schema": "dk-proof-archaeology/git-excerpt/v1",
        "commit": sha,
        "path": canonical_path(path),
        "blob_oid": oid,
        "file_sha256": digest(body),
        "excerpt_sha256": digest(raw),
        "line_start": start,
        "line_end": end,
        "excerpt": raw.decode("utf-8", "replace"),
        "display": snippet_as_text(body, start, end),
        "commit_metadata": git.meta(sha),
        "git_locator": f"{sha}:{path}#L{start}-L{end}",
        "scope": "Source text present in this Git blob; neither a Lean proof check nor a historical priority claim."
    }
    return result


def parse_follow_log(raw: str) -> list[dict]:
    """Git --follow name-status; NUL-safe path parsing is not possible in line mode.

    Names with LF/tab are unsupported and are rejected rather than misattributed.
    """
    events = []
    for record in raw.split("\x1e"):
        if not record.strip():
            continue
        first, sep, rest = record.partition("\n")
        parts = first.strip().split("\x1f", 3)
        if len(parts) != 4 or not re.fullmatch(r"[a-f0-9]{40,64}", parts[0]):
            raise EvidenceError("unexpected git log record framing; cannot verify history")
        changes = []
        for line in rest.splitlines():
            if not line.strip():
                continue
            fields = line.split("\t")
            if not re.fullmatch(r"[A-Z][0-9]*", fields[0]):
                raise EvidenceError(f"unexpected Git name-status line {line!r}; check path quoting")
            paths = fields[1:]
            if not paths or any(p.startswith('"') or p.endswith('"') for p in paths):
                raise EvidenceError(f"ambiguous quoted git path: {line!r}")
            changes.append({"status": fields[0], "paths": paths})
        events.append({"commit": parts[0], "author_date": parts[1],
                       "commit_date": parts[2], "subject": parts[3], "changes": changes})
    return events


def timeline(git: Git, path: str, ref: str, limit: int, all_refs: bool) -> dict:
    canonical_path(path)
    if limit < 0:
        raise EvidenceError("--limit must be >= 0 (0 means unlimited)")
    ref_sha = git.commit(ref)
    args = ["-c", "core.quotePath=false", "log", "--follow", "-M", "--date=iso-strict",
            "--name-status", "--format=%x1e%H%x1f%aI%x1f%cI%x1f%s", "--no-color"]
    if limit:
        args.append(f"--max-count={limit}")
    args.extend(["--all" if all_refs else ref_sha, "--", path])
    raw = git.value(*args)
    events = parse_follow_log(raw)
    return {
        "schema": "dk-proof-archaeology/git-timeline/v1", "ref": ref_sha,
        "all_refs": all_refs, "requested_path": path,
        "limit": limit, "possibly_truncated": bool(limit and len(events) >= limit),
        "events": events, "count": len(events),
        "caveats": "--follow is Git's rename heuristic for one path (not proof of identity). With --all, parallel branch histories may not form one unambiguous file lineage. Date ordering is not a causation or priority claim."
    }


def pickaxe(git: Git, needle: str, ref: str, limit: int,
            paths: list[str], regex: bool, all_refs: bool) -> dict:
    if not needle:
        raise EvidenceError("pickaxe string/regex must be nonempty")
    if limit < 0:
        raise EvidenceError("--limit must be >= 0")
    sha = git.commit(ref)
    args = ["log", "--date-order", "--format=%H", "--no-patch"]
    if limit:
        args.append(f"--max-count={limit}")
    args.append(("-G" if regex else "-S") + needle)
    args.append("--all" if all_refs else sha)
    if paths:
        args.append("--")
        args.extend(canonical_path(p) for p in paths)
    ids = [x for x in git.value(*args).splitlines() if x]
    return {
        "schema": "dk-proof-archaeology/git-pickaxe/v1", "ref": sha,
        "all_refs": all_refs, "mode": "regex-diff-match" if regex else "literal-count-change",
        "needle": needle, "paths": paths, "limit": limit,
        "possibly_truncated": bool(limit and len(ids) >= limit),
        "events": [git.meta(x) for x in ids],
        "caveat": "Candidates are diff matches/count changes, not proven introduction, origin, correctness, or semantic equivalence. Rename-only changes and edits with balanced occurrences may be omitted."
    }


def ledger_at(git: Git, sha: str, path: str, rowid: str) -> dict | None:
    found = git.object_at(sha, path)
    if found is None:
        return None
    oid, body = found
    try:
        data = json.loads(body)
    except (UnicodeDecodeError, ValueError) as exc:
        raise EvidenceError(f"{sha}:{path} is not valid JSON: {exc}") from exc
    matches = [row for field in ("results", "items")
               for row in data.get(field, [])
               if isinstance(row, dict) and row.get("id") == rowid]
    if len(matches) > 1:
        raise EvidenceError(f"duplicate ledger ID {rowid} in {sha}:{path}")
    if not matches:
        return {"present": False, "blob_oid": oid}
    return {"present": True, "blob_oid": oid, "row": matches[0],
            "row_sha256": digest(json.dumps(matches[0], sort_keys=True, ensure_ascii=False).encode("utf-8"))}


def ledger_history(git: Git, ref: str, path: str, rowid: str, limit: int) -> dict:
    canonical_path(path)
    sha = git.commit(ref)
    if limit < 0:
        raise EvidenceError("--limit must be >= 0")
    # `--follow` is heuristic. Explicitly carry detected prior path names
    # backwards; otherwise `git show OLD:path-at-HEAD` silently misses rows.
    events = timeline(git, path, ref, limit, False)["events"]
    newest_to_oldest = []
    prior_path = path
    for event in events:
        newest_to_oldest.append((event["commit"], prior_path))
        for change in event["changes"]:
            if (change["status"].startswith("R") and len(change["paths"]) == 2
                    and change["paths"][1] == prior_path):
                prior_path = change["paths"][0]
    observed = []
    previous = None
    for commit, historical_path in reversed(newest_to_oldest):
        state = ledger_at(git, commit, historical_path, rowid)
        if state is None:
            state = {"present": False, "ledger_file_missing": True}
        if previous is not None and state.get("row_sha256") == previous.get("row_sha256") and state.get("present") == previous.get("present"):
            continue
        fields_changed = sorted(set(state.get("row", {})) ^ set(previous.get("row", {}) if previous else {}))
        if previous and state.get("present") and previous.get("present"):
            fields_changed += sorted(k for k in set(state["row"]) & set(previous["row"])
                                     if state["row"][k] != previous["row"][k])
        observed.append({"commit": commit, "historical_path": historical_path,
                         "metadata": git.meta(commit),
                         "state": state, "changed_top_level_fields": sorted(set(fields_changed))})
        previous = state
    return {
        "schema": "dk-proof-archaeology/ledger-evolution/v1",
        "ref": sha, "path": path, "row_id": rowid,
        "scanned_ledger_edits": len(events), "limit": limit,
        "possibly_truncated": bool(limit and len(events) >= limit),
        "events": observed,
        "caveats": "This is what the ledger *reported at historical commits*. It does not rerun Lean, certify source correspondence, or turn a recorded acceptance reversal into an incorrect proof. A limited history need not show the first appearance; --follow may miss file renames when content also changes."
    }


def verify_evidence(git: Git, path: Path) -> dict:
    if not path.is_file():
        raise EvidenceError(f"evidence ledger not found: {path}")
    problems = []
    checked = []
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        fieldnames = reader.fieldnames or []
        rows = list(reader)
    keys = ("evidence_id", "case", "claim_id", "commit", "path", "line_start",
            "line_end", "blob_oid", "excerpt_sha256", "review_status", "interpretation", "notes")
    if any(key not in fieldnames for key in keys):
        raise EvidenceError("reviewed evidence CSV does not have the required header")
    ids = set()
    for idx, row in enumerate(rows, start=2):
        errs = []
        eid = row.get("evidence_id", "")
        if not eid or eid in ids:
            errs.append("missing/duplicate evidence_id")
        ids.add(eid)
        if row.get("review_status") not in ("candidate", "reviewed", "rejected"):
            errs.append("invalid review_status")
        if row.get("review_status") == "reviewed" and not row.get("interpretation", "").strip():
            errs.append("reviewed evidence requires interpretation")
        try:
            sha = git.commit(row["commit"])
            if sha != row["commit"]:
                errs.append("commit must be the complete immutable Git SHA")
            found = git.object_at(sha, row["path"])
            if found is None:
                errs.append("file absent at pinned commit")
            else:
                oid, body = found
                a, b = int(row["line_start"]), int(row["line_end"])
                quoted = excerpt(body, a, b)
                if oid != row["blob_oid"]:
                    errs.append("blob OID mismatch")
                if digest(quoted) != row["excerpt_sha256"]:
                    errs.append("excerpt SHA256 mismatch")
        except (EvidenceError, ValueError, KeyError) as exc:
            errs.append(str(exc))
        checked.append({"row": idx, "evidence_id": eid, "valid": not errs, "errors": errs})
        if errs:
            problems.append(idx)
    return {"schema": "dk-proof-archaeology/git-evidence-validation/v1",
            "ledger": str(path), "rows": len(rows), "invalid_rows": problems,
            "checks": checked, "valid": not problems,
            "scope": "Verifies existence and immutability of Git source excerpts, not their mathematical or historical interpretation."}


def collect_case(git: Git, case: str, out: Path, limit: int, all_refs: bool,
                 include_pickaxe: bool = False) -> dict:
    """Batch Git evidence gathering; intentionally never decides historical claims."""
    config = case_config(case)
    out.mkdir(parents=True, exist_ok=True)
    status = git.status()
    ref = git.commit("HEAD")
    produced = []
    failures = []

    def save(path: Path, obj: dict) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        produced.append({"file": path.relative_to(out).as_posix(),
                         "sha256": digest(path.read_bytes()),
                         "count": len(obj.get("events", obj.get("timelines", [])))})

    for path in config["paths"]:
        file_label = re.sub(r"[^A-Za-z0-9_.-]", "_", path)
        try:
            result = timeline(git, path, "HEAD", limit, all_refs)
            save(out / "timelines" / (file_label + ".json"), result)
        except EvidenceError as exc:
            failures.append({"operation": "timeline", "path": path, "error": str(exc)})

    for ledger_path in ("dev/davis-kahan-1970-formalization-result-inventory.json",
                        "dev/davis-kahan-1970-full-source-census.json"):
        for rowid in config["ledger_ids"]:
            try:
                result = ledger_history(git, "HEAD", ledger_path, rowid, limit)
                safeid = re.sub(r"[^A-Za-z0-9_.-]", "_", rowid)
                prefix = "inventory" if "result-inventory" in ledger_path else "census"
                save(out / "ledgers" / f"{prefix}_{safeid}.json", result)
            except EvidenceError as exc:
                failures.append({"operation": "ledger", "path": ledger_path,
                                 "row": rowid, "error": str(exc)})

    if include_pickaxe:
        for index, needle in enumerate(config["needles"], start=1):
            try:
                result = pickaxe(git, needle, "HEAD", limit, [], False, all_refs)
                save(out / "pickaxe" / f"needle_{index}.json", result)
            except EvidenceError as exc:
                failures.append({"operation": "pickaxe", "needle": needle, "error": str(exc)})

    manifest = {"schema": "dk-proof-archaeology/history-packet/v1",
                "case": case, "at_commit": ref,
                "targets_file_sha256": digest(TARGETS.read_bytes()),
                "checkout": status, "limit": limit, "all_refs": all_refs,
                "include_pickaxe": include_pickaxe,
                "files": produced, "failures": failures,
                "reading_rule": "Git source and ledger states are observational candidates. Historical influence and mathematical dependency require separate proof and primary-source review."}
    save(out / "manifest.json", manifest)
    lines = [f"# Historical Git evidence: {case}", "",
             f"Pinned Git HEAD: `{ref}`. Shallow checkout: `{status['shallow']}`; "
             f"promisor remotes: `{status['promisor_remotes']}`.", "",
             "This packet provides navigable *source-history candidates*. It is not a proof of the original mathematical authors' knowledge or a replacement for the compiler-derived theorem graph.", "",
             "## Saved evidence", ""]
    for record in produced:
        lines.append(f"- [`{record['file']}`]({record['file']}) ({record['count']} sampled events; SHA256 `{record['sha256']}`)")
    if failures:
        lines.extend(["", "## Missing or inaccessible history", ""])
        for failed in failures:
            lines.append("- " + json.dumps(failed, ensure_ascii=False))
    lines += ["", "## Investigation checkpoints", "",
              "1. Inspect reported changes in the two source ledgers. Their old statuses are **historical reports**, not replayed Lean verification.",
              "2. Use `git_history.py excerpt --rev ... --path ... --start ... --end ...` to pin the actual changed source passage by commit and blob.",
              "3. Where a path changes, verify the rename with file contents and statement comparison. `--follow` is heuristic.",
              "4. Check mathematical ancestors in original publications; Git timestamps alone never establish scholarly priority.",
              "5. To study proof dependency changes, separately index the two pinned revisions with `leanq`, then run `graph_compare.py`.",
              ""]
    (out / "HISTORY_EVIDENCE.md").write_text("\n".join(lines), encoding="utf-8")
    return manifest


def source_diff(git: Git, old_ref: str, new_ref: str,
                paths: list[str], context: int) -> dict:
    if context < 0 or context > 1000:
        raise EvidenceError("--context must be between 0 and 1000")
    if not paths:
        raise EvidenceError("diff requires one or more --path arguments")
    old_sha, new_sha = git.commit(old_ref), git.commit(new_ref)
    args = ["diff", "--no-ext-diff", "--no-textconv", "--find-renames",
            f"--unified={context}", old_sha, new_sha, "--"]
    args.extend(canonical_path(p) for p in paths)
    patch = git.run(*args).stdout
    return {"schema": "dk-proof-archaeology/historical-source-diff/v1",
            "old_commit": old_sha, "new_commit": new_sha,
            "paths": paths, "patch_sha256": digest(patch),
            "patch": patch.decode("utf-8", "replace"),
            "caveat": "Git source diff only. This does not establish a change in elaborated Lean theorem meaning, proof validity, or historical priority."}


def write_json(payload: dict, destination: str | None, root: Path) -> None:
    if destination:
        dst = Path(destination)
        if not dst.is_absolute():
            dst = root / dst
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(dst)
    else:
        print(json.dumps(payload, indent=2, ensure_ascii=False))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO,
                        help="Git repository, defaults to the current DK formalization checkout")
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("status", help="Object/ref coverage, shallow/promisor warning")
    p.add_argument("--out")
    p = sub.add_parser("excerpt", help="Quote exact source lines at any commit, with blob digest")
    p.add_argument("--rev", required=True)
    p.add_argument("--path", required=True)
    pick = p.add_mutually_exclusive_group(required=True)
    pick.add_argument("--needle", help="unique literal line, not a regex")
    pick.add_argument("--start", type=int)
    p.add_argument("--end", type=int)
    p.add_argument("--context", type=int, default=6)
    p.add_argument("--out")
    p = sub.add_parser("timeline", help="Git --follow candidate file-lineage, including deleted paths")
    p.add_argument("--case", choices=sorted(load_targets()), help="emit timelines for its configured paths")
    p.add_argument("--path", action="append", default=[], help="repeatable literal path")
    p.add_argument("--rev", default="HEAD")
    p.add_argument("--all-refs", action="store_true")
    p.add_argument("--limit", type=int, default=300, help="0 for all recorded history")
    p.add_argument("--out")
    p = sub.add_parser("pickaxe", help="Locate candidate source changes using git log -S/-G")
    p.add_argument("--case", choices=sorted(load_targets()))
    p.add_argument("--needle", required=True)
    p.add_argument("--regex", action="store_true", help="Git -G patch-regex rather than -S literal-count")
    p.add_argument("--path", action="append", default=[], help="restrict to a path (optional)")
    p.add_argument("--rev", default="HEAD")
    p.add_argument("--all-refs", action="store_true")
    p.add_argument("--limit", type=int, default=200)
    p.add_argument("--out")
    p = sub.add_parser("diff", help="Compare source files at two immutable Git revisions")
    p.add_argument("--old", required=True)
    p.add_argument("--new", required=True)
    p.add_argument("--path", action="append", required=True)
    p.add_argument("--context", type=int, default=5, help="diff context lines")
    p.add_argument("--out", help="JSON file containing the complete unified patch")
    p = sub.add_parser("ledger", help="Historical source-census or result-inventory row transitions")
    p.add_argument("--rev", default="HEAD")
    p.add_argument("--path", default="dev/davis-kahan-1970-formalization-result-inventory.json")
    p.add_argument("--row", required=True, help="stable source-result ID")
    p.add_argument("--limit", type=int, default=500, help="0 means entire accessible history")
    p.add_argument("--out")
    p = sub.add_parser("collect-case", help="Bundle path timelines and both historical ledgers without changing Git state")
    p.add_argument("--case", required=True, choices=sorted(load_targets()))
    p.add_argument("--out", help="output directory, defaults to build/what-it-takes-dk/history/CASE")
    p.add_argument("--limit", type=int, default=300, help="per-path history limit; 0 means unlimited")
    p.add_argument("--all-refs", action="store_true", help="include non-HEAD refs for file timelines and pickaxe")
    p.add_argument("--include-pickaxe", action="store_true", help="run full-history diff searches for each configured theorem name")
    p = sub.add_parser("verify", help="Check immutable evidence anchors in the curated CSV")
    p.add_argument("--ledger-file", type=Path, default=REVIEWED)
    p.add_argument("--out")
    args = parser.parse_args(argv)
    try:
        git = Git(args.repo.expanduser().resolve())
        git.check()
        if args.command == "status":
            payload = git.status()
        elif args.command == "excerpt":
            if args.context < 0:
                raise EvidenceError("--context must be nonnegative")
            payload = quote(git, args.rev, args.path, args.start, args.end,
                            args.needle, args.context)
        elif args.command == "timeline":
            paths = list(dict.fromkeys((case_config(args.case)["paths"] if args.case else []) + args.path))
            if not paths:
                raise EvidenceError("timeline needs --case or --path")
            payload = {"schema": "dk-proof-archaeology/git-timelines/v1", "checkout": git.status(),
                       "timelines": [timeline(git, p, args.rev, args.limit, args.all_refs) for p in paths]}
        elif args.command == "pickaxe":
            paths = args.path
            if args.case:
                # Broad history search by default, even when a theorem moved or a file was deleted.
                # Use --path to narrow: requiring current paths would miss old names.
                case_config(args.case)
            payload = pickaxe(git, args.needle, args.rev, args.limit, paths, args.regex, args.all_refs)
            if args.case:
                payload["research_case"] = args.case
        elif args.command == "diff":
            payload = source_diff(git, args.old, args.new, args.path, args.context)
        elif args.command == "ledger":
            payload = ledger_history(git, args.rev, args.path, args.row, args.limit)
        elif args.command == "collect-case":
            out = Path(args.out) if args.out else Path(DEFAULT_OUTPUT) / args.case
            if not out.is_absolute():
                out = git.root / out
            payload = collect_case(git, args.case, out, args.limit, args.all_refs,
                                   args.include_pickaxe)
            print(out / "HISTORY_EVIDENCE.md")
            if payload["failures"]:
                print(f"warning: {len(payload['failures'])} historical probes inaccessible; inspect the packet", file=sys.stderr)
            return 0
        elif args.command == "verify":
            payload = verify_evidence(git, args.ledger_file)
        else:
            raise EvidenceError("unknown command")
        write_json(payload, args.out, git.root)
        if args.command == "verify" and not payload["valid"]:
            return 1
        return 0
    except (EvidenceError, OSError, ValueError) as exc:
        print(f"git-history: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
