#!/usr/bin/env python3
"""Static detectors for the hostile review: duplication, bloat, dead API, naming.

A line-by-line read of 787 Lean files finds what is inside a file. It does not
find that two files 300 modules apart prove the same lemma — no reader holds
that much at once. These detectors do, and they run in seconds, so the reading
pass can be *informed* rather than blind.

**Every detector reports candidates, not findings.** A normalized-statement
collision may be a genuine duplicate, a deliberate specialization, or a
re-export. The reviewer confirms; the scanner only says where to look.

Detectors:

* `--dup` — **near-duplicate theorem statements.** The statement is normalized
  (universes, whitespace, implicit binder names erased) and hashed; collisions
  across files are the candidates.

  **Restricted to `theorem`/`lemma` deliberately.** For a `def` the statement is
  only its *type*, and dozens of unrelated definitions legitimately share
  `(U V : Submodule ℂ E) … : E →L[ℂ] E`. Including them produced 175 groups of
  which nearly all were type collisions between genuinely different objects --
  a detector whose output is mostly noise does not get read. Definitions are
  compared by **body** instead, under `--dupdef`.
* `--big` — **declarations that should be split.** Statement length and proof
  length, worst first. A 200-line proof is not automatically wrong; a 40-line
  *statement* almost always is.
* `--dead` — **definitions with no consumer.** A `def`/`abbrev`/`structure`
  whose name appears nowhere else in the repository. Public API with no user is
  either unfinished or unnecessary, and a reviewer asks which.
* `--defn` — **definitional escapes**, separated from proof escapes. A `def`
  whose *body* is an escape produces an **opaque term**: every theorem stated
  about it is unprovable, not merely unproved, because there is nothing to
  unfold. Counting escapes per file conflates the two and inverts leverage --
  it made `DoubleAngle.lean` (1 escape, gating 75 modules) look like the highest-
  value target when its escape is a theorem *about* a `sorry`-defined operator
  three modules upstream, so it cannot be discharged at all until that operator
  is defined. Found by `jon (yardrat)` 2026-07-30, correcting lane `EXP-UNBLOCK`.
* `--names` — **names that mislead.** Qualifiers asserting the author's opinion
  of the result (`genuine`, `faithful`, `complete`, `sharp`, `real`, `proper`),
  version suffixes, and `Legacy`/`Compat`/`Aux`/`Tmp`.

Usage:
    python3 scripts/audit_scan.py --dup [--min-lines 3]
    python3 scripts/audit_scan.py --big --top 40
    python3 scripts/audit_scan.py --dead
    python3 scripts/audit_scan.py --names
    python3 scripts/audit_scan.py --scope ForTauCeti --dup
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SKIP = ("retired/", "external/", ".lake/", "vendor/")

DECL_RE = re.compile(
    r"^(?P<indent>\s*)"
    r"(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|instance|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.'’!?]*)",
    re.M)
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--.*?$", re.M)


def lean_files(scope: str | None) -> list[pathlib.Path]:
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout
    paths = [p for p in out.splitlines() if p and not p.startswith(SKIP)]
    if scope:
        paths = [p for p in paths if p.startswith(scope)]
    # `git ls-files` reports the *index*, which during a half-staged rename still
    # names a path that no longer exists on disk.  Skipping those turns a
    # traceback into a correct report of the tree as it stands; a detector that
    # crashes mid-refactor is a detector nobody runs mid-refactor.
    return [ROOT / p for p in paths if (ROOT / p).is_file()]


def strip_comments(text: str) -> str:
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def declarations(path: pathlib.Path):
    """Yield (name, kind, statement, proof, start_line) per declaration."""
    text = strip_comments(path.read_text(errors="replace"))
    lines = text.splitlines()
    marks = [(m.start(), m.group("name"), m.group("kind"))
             for m in DECL_RE.finditer(text)]
    for i, (pos, name, kind) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(text)
        chunk = text[pos:end]
        # split statement from proof at the first top-level := or 'by'
        cut = None
        depth = 0
        for j, ch in enumerate(chunk):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0 and chunk.startswith(":=", j):
                cut = j
                break
        stmt = chunk[:cut] if cut is not None else chunk
        proof = chunk[cut:] if cut is not None else ""
        start_line = text.count("\n", 0, pos) + 1
        yield name, kind, stmt, proof, start_line


NORM_SUBS = [
    (re.compile(r"\.\{[^}]*\}"), ""),            # universe annotations
    (re.compile(r"\s+"), " "),                    # whitespace
    (re.compile(r"⦃[^⦄]*⦄|\{[^{}]*:\s*"), "{:"),  # implicit binder names
]


def normalize(stmt: str, name: str) -> str:
    s = stmt
    # drop the declaration keyword and its own name
    s = re.sub(r"^\s*(?:@\[[^\]]*\]\s*)*"
               r"(?:private\s+|protected\s+|noncomputable\s+)*"
               r"(?:theorem|lemma|def|abbrev|structure|instance|inductive)\s+"
               + re.escape(name), "", s)
    for pat, rep in NORM_SUBS:
        s = pat.sub(rep, s)
    return s.strip()


def cmd_dup(files, args) -> int:
    buckets = collections.defaultdict(list)
    for p in files:
        rel = p.relative_to(ROOT).as_posix()
        for name, kind, stmt, proof, line in declarations(p):
            if args.dupdef:
                if kind not in ("def", "abbrev"):
                    continue
                norm = normalize(proof, name)
            else:
                if kind not in ("theorem", "lemma"):
                    continue
                norm = normalize(stmt, name)
            if len(norm) < args.min_chars:
                continue
            h = hashlib.sha1(norm.encode()).hexdigest()[:12]
            buckets[h].append((rel, line, name, norm, proof))
    groups = [v for v in buckets.values()
              if len({f for f, _, _, _, _ in v}) > 1]
    groups.sort(key=len, reverse=True)

    # A *forwarding alias* is not duplication: its whole proof is an application of
    # the very theorem it shares a statement with, so there is one proof and two
    # names -- which is what a compatibility layer is for.  `DavisKahan` has several
    # deliberately (`BoundedOperator/Compat.lean` documents the pattern), and they
    # differ from a real copy in the one way that matters: deleting the alias loses
    # a name, deleting a copy loses nothing.
    #
    # Detected rather than listed, because the alias and its target usually have
    # *different* names -- that is why a name-based check never sees these clusters
    # and only the normalized-statement match finds them.
    def is_forwarder(group) -> bool:
        names = {n for _, _, n, _, _ in group}
        for _, _, name, _, proof in group:
            body = proof.strip()
            if len(body.splitlines()) <= 3 and any(
                    other != name and re.search(r"\b" + re.escape(other) + r"\b", body)
                    for other in names):
                return True
        return False

    forwarders = [g for g in groups if is_forwarder(g)]
    groups = [g for g in groups if not is_forwarder(g)]

    # A `ForTauCetiRoadmap/**/Suggested.lean` statement matching its `ForTauCeti`
    # implementation is the roadmap *working*, not drift: those files say so
    # themselves -- "Bodies are placeholders; the statements are the content",
    # written with "names that follow the staged ForTauCeti implementation".
    #
    # Reported separately rather than dropped, because the match can also go stale
    # in the other direction and someone should be able to see the pairs.  It is
    # split out because on 2026-07-31 a `--dup --scope ForTauCeti` run was 22
    # mirrors and 1 real duplicate, and a report that is 96% expected is a report
    # nobody finishes reading -- the real one had been sitting in it unnoticed.
    def is_mirror(g) -> bool:
        files = {f for f, _, _, _, _ in g}
        road = {f for f in files if f.startswith("ForTauCetiRoadmap/")}
        return bool(road) and bool(files - road)

    mirrors = [g for g in groups if is_mirror(g)]
    groups = [g for g in groups if not is_mirror(g)]

    what = "definition BODIES" if args.dupdef else "theorem STATEMENTS"
    print(f"near-duplicate {what} spanning >1 file: {len(groups)}")
    print(f"declarations involved: {sum(len(g) for g in groups)}\n")
    for g in groups[:args.top]:
        print(f"--- {len(g)} declarations share a normalized statement")
        print(f"    {g[0][3][:150]}")
        for rel, line, name, _, _ in sorted(g):
            print(f"      {rel}:{line}  {name}")
        print()
    if forwarders:
        print(f"forwarding aliases (expected -- one proof, two names): {len(forwarders)}")
        if args.mirrors:
            for g in forwarders:
                for rel, line, name, _, _ in sorted(g):
                    print(f"      {rel}:{line}  {name}")
                print()
        else:
            print("  pass --mirrors to list them")
    if mirrors:
        print(f"roadmap mirrors (expected -- a Suggested.lean signature matching its "
              f"implementation): {len(mirrors)}")
        if args.mirrors:
            for g in mirrors:
                for rel, line, name, _, _ in sorted(g):
                    print(f"      {rel}:{line}  {name}")
                print()
        else:
            print("  pass --mirrors to list them")
    return 0


def cmd_big(files, args) -> int:
    rows = []
    for p in files:
        rel = p.relative_to(ROOT).as_posix()
        for name, kind, stmt, proof, line in declarations(p):
            rows.append((stmt.count("\n") + 1, proof.count("\n") + 1,
                         rel, line, name, kind))
    print("=== longest STATEMENTS (a long statement is usually several theorems) ===")
    for sl, pl, rel, line, name, kind in sorted(rows, reverse=True)[:args.top]:
        print(f"  stmt {sl:4}  proof {pl:5}  {rel}:{line}  {name}")
    print("\n=== longest PROOFS ===")
    for sl, pl, rel, line, name, kind in sorted(
            rows, key=lambda r: -r[1])[:args.top]:
        print(f"  proof {pl:5} stmt {sl:4}  {rel}:{line}  {name}")
    return 0


def cmd_dead(files, args) -> int:
    defined = {}
    for p in files:
        rel = p.relative_to(ROOT).as_posix()
        for name, kind, stmt, _p, line in declarations(p):
            if kind in ("def", "abbrev", "structure"):
                defined.setdefault(name.split(".")[-1], []).append((rel, line, name))
    # The usage corpus is ALWAYS the whole tree, never the scoped subset.  `--scope`
    # restricts which definitions are CANDIDATES, not where their consumers may live:
    # scoping the corpus made every ForTauCeti definition used only by DavisKahan look
    # dead, which is how this reported 25 false positives on 2026-07-30 (`IsOffDiagonal`
    # has 47 repo-wide uses).
    corpus_files = lean_files(None)
    corpus = "\n".join(q.read_text(errors="replace") for q in corpus_files)
    # The token class must NOT contain `.`: with it, `TauCeti.foo` is a single token and
    # a qualified use never counts toward the short name `foo`.  That bug was fixed once
    # on 2026-07-30 and came back in a merge, so the assertion below pins it.
    counts = collections.Counter(re.findall(r"[A-Za-z_][A-Za-z0-9_'’]*", corpus))
    assert counts.get("IsSelfAdjointOperator", 0) != 1 or not corpus_files, \
        "short-name counting is broken again: a qualified use is not being counted"
    dead = [(v[0], k) for k, v in defined.items() if counts[k] <= len(v)]
    print(f"definitions whose short name appears no more often than it is "
          f"defined: {len(dead)}\n")
    for (rel, line, full), short in sorted(dead)[:args.top]:
        print(f"  {rel}:{line}  {full}")
    return 0


BAD_NAME = re.compile(
    r"(?i)(genuine|faithful|literature|truly|actual|proper(?!ty)|"
    r"legacy|compat(?!ible)|_aux|Aux[A-Z]|tmp|_v[0-9]|[a-z]V[0-9]|_old|_new)")


def cmd_names(files, args) -> int:
    hits = collections.defaultdict(list)
    for p in files:
        rel = p.relative_to(ROOT).as_posix()
        for name, kind, _s, _pr, line in declarations(p):
            m = BAD_NAME.search(name)
            if m:
                hits[m.group(1).lower()].append((rel, line, name))
    total = sum(len(v) for v in hits.values())
    print(f"declarations with an opinion-bearing or provisional qualifier: {total}\n")
    for word, items in sorted(hits.items(), key=lambda x: -len(x[1])):
        print(f"--- {word!r}  x{len(items)}")
        for rel, line, name in sorted(items)[:args.top]:
            print(f"      {rel}:{line}  {name}")
        if len(items) > args.top:
            print(f"      ... and {len(items) - args.top} more")
        print()
    return 0


# Start of any declaration.  Used to cut the file into blocks so that a body is
# only ever attributed to the declaration it actually belongs to.
#
# The previous detector was a single regex with `re.S`, whose lazy `(.*?)` ran
# from a declaration's name to the next `:= sorry` ANYWHERE later in the file --
# across blank lines, docstrings and intervening declarations.  So every `def`
# that merely *preceded* an escape was reported as definitional even when it had
# a perfectly good body.  That inverted the one distinction this subcommand
# exists to draw: `spectralProjection` was listed despite its body being
# `(spectralSubspace A s).starProjection`, and `operatorAbsoluteValue` stayed
# listed after it was given the body `CFC.abs T`.  Since the point of `--defn`
# is to separate opaque terms (whose downstream theorems are *unprovable*) from
# merely unproved ones, an over-report here is not a rounding error -- it
# misdirects lane planning, which is exactly what it did.
DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |partial |scoped |unsafe )*"
    r"(def|abbrev|instance|structure|class|theorem|lemma|example|opaque|axiom)"
    r"(?:\s+([A-Za-z_][\w.'\u2019]*))?", re.M)

# Bodies that are themselves an escape.  `:= sorry` and `:= by ... sorry` both
# produce an opaque term, so both count.
BODY_ESCAPE_RE = re.compile(r":=[\s\S]*?\b" + "sor" + r"ry\b")

# Declaration keywords that introduce a *term* rather than a proof.
DEFINITIONAL_KINDS = {"def", "abbrev", "instance", "structure", "class", "opaque"}


def definitional_escapes(text: str) -> list[tuple[str, str]]:
    """The `(kind, name)` of every declaration whose own body is an escape.

    Works blockwise: each declaration owns the text up to the next declaration,
    so a body can never be attributed across a boundary.
    """
    starts = [(m.start(), m.group(1), m.group(2)) for m in DECL_START_RE.finditer(text)]
    out = []
    for i, (pos, kind, name) in enumerate(starts):
        if kind not in DEFINITIONAL_KINDS:
            continue
        end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        if BODY_ESCAPE_RE.search(text[pos:end]):
            # An anonymous `instance : Foo := sorry` is still an opaque term.
            out.append((kind, name or "<anonymous>"))
    return out


def cmd_defn(files, args) -> int:
    """Definitional escapes poison every downstream statement; proof escapes do not."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "ready", ROOT / "scripts" / "check_tauceti_readiness.py")
    ready = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ready)
    tot_d = tot_p = 0
    for p in files:
        text = ready.strip_comments(p.read_text(errors="replace"))
        n = len(ready.ESCAPE_RE.findall(text))
        if not n:
            continue
        defs = definitional_escapes(text)
        tot_d += len(defs)
        tot_p += n - len(defs)
        if defs:
            print(f"{p.relative_to(ROOT)}  ({len(defs)} definitional of {n})")
            for kind, name in defs:
                print(f"      {kind} {name}")
    print(f"\n{tot_d} definitional (opaque terms), {tot_p} proof-only, "
          f"{tot_d + tot_p} total")
    print("Definitional first: a theorem about an opaque term cannot be proved, "
          "only restated.")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dup", action="store_true")
    ap.add_argument("--mirrors", action="store_true",
                    help="with --dup: list the roadmap-mirror groups instead of counting them")
    ap.add_argument("--dupdef", action="store_true",
                    help="duplicate DEFINITION bodies (type alone is not identity)")
    ap.add_argument("--big", action="store_true")
    ap.add_argument("--dead", action="store_true")
    ap.add_argument("--names", action="store_true")
    ap.add_argument("--defn", action="store_true",
                    help="definitional escapes (a sorry-DEFINED term) vs proof escapes")
    ap.add_argument("--scope", help="restrict to a path prefix")
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("--min-chars", type=int, default=60,
                    help="ignore statements shorter than this when hunting duplicates")
    args = ap.parse_args(argv)
    files = lean_files(args.scope)
    print(f"# scanning {len(files)} Lean files"
          f"{' under ' + args.scope if args.scope else ''}\n")
    if args.dup or args.dupdef:
        return cmd_dup(files, args)
    if args.big:
        return cmd_big(files, args)
    if args.dead:
        return cmd_dead(files, args)
    if args.names:
        return cmd_names(files, args)
    if args.defn:
        return cmd_defn(files, args)
    ap.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
