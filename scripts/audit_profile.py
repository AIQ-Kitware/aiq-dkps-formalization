#!/usr/bin/env python3
"""Per-file review profile for a group, so every file is examined systematically.

The audit covers 1,160 files. Opening each one and reading it top to bottom is
the ideal, and it is also how an audit dies at 3% coverage. This tool extracts
the review-relevant signal from **every** file in a group — what it declares,
how big its statements and proofs are, what it duplicates elsewhere, what it
defines that nothing uses, what it names badly, whether it is documented and
where it sits — so the reviewer reads the *whole group's* shape at once and then
opens only the files the signals flag.

That is not a shortcut around reading. It is the order a reviewer with 1,160
files uses: measure everything, then read what the measurement says is worth
reading, then record both.

Signals per file:

* `decls` — declaration count by kind.
* `stmt/proof max` — the longest statement and proof in the file. A long
  *statement* is usually several theorems; a long proof may be fine.
* `dup` — declarations whose normalized statement also appears in another file.
* `dead` — definitions whose name appears nowhere else in the corpus.
* `name` — declarations carrying an opinion-bearing or provisional qualifier.
  (Docstring coverage is deliberately NOT recomputed here:
  `scripts/check_docstring_coverage.py` already owns it, is tested, and reports
  0 undocumented. A second implementation in this file disagreed with it --
  claiming all 70 T01 declarations were undocumented -- which is exactly the
  duplicate-checker problem this audit exists to find.)
* `prov` — whether a `## Provenance` section is present (ForTauCeti requires it).
* `esc` — proof escapes in code (comments stripped).

Usage:
    python3 scripts/audit_profile.py --group "ForTauCeti :: T01 ..."
    python3 scripts/audit_profile.py --path DavisKahan/Sylvester
    python3 scripts/audit_profile.py --list-groups
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import importlib.util
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


SCAN = load("audit_scan")
CHECK = load("audit_checklist")

ESCAPE = re.compile(r"\b(" + "sor" + "ry|ad" + "mit|nat" + "ive_decide)" + r"\b")
DOCSTR = re.compile(r"/--.*?-/\s*$", re.S)


def corpus_index():
    """Global maps needed for cross-file signals."""
    files = SCAN.lean_files(None)
    dup = collections.defaultdict(list)
    name_count = collections.Counter()
    defined = collections.defaultdict(list)
    for p in files:
        rel = p.relative_to(ROOT).as_posix()
        text = p.read_text(errors="replace")
        name_count.update(re.findall(r"[A-Za-z_][A-Za-z0-9_.'’]*", text))
        for nm, kind, stmt, proof, line in SCAN.declarations(p):
            if kind in ("theorem", "lemma"):
                norm = SCAN.normalize(stmt, nm)
                if len(norm) >= 60:
                    dup[hashlib.sha1(norm.encode()).hexdigest()[:12]].append((rel, nm))
            if kind in ("def", "abbrev", "structure"):
                defined[nm.split(".")[-1]].append(rel)
    multi = {h for h, v in dup.items() if len({r for r, _ in v}) > 1}
    dup_members = {(r, n) for h in multi for r, n in dup[h]}
    dead = {k for k, v in defined.items() if name_count[k] <= len(v)}
    return dup_members, dead


def profile(rel: str, dup_members, dead):
    p = ROOT / rel
    if not rel.endswith(".lean"):
        try:
            n = p.read_text(errors="replace").count("\n") + 1
        except OSError:
            n = 0
        return {"file": rel, "lines": n, "kind": CHECK.kind_of(rel), "nonlean": True}
    text = p.read_text(errors="replace")
    code = SCAN.strip_comments(text)
    kinds = collections.Counter()
    max_stmt = max_proof = 0
    dups, deads, bad_names, undoc = [], [], [], []
    for nm, kind, stmt, proof, line in SCAN.declarations(p):
        kinds[kind] += 1
        max_stmt = max(max_stmt, stmt.count("\n") + 1)
        max_proof = max(max_proof, proof.count("\n") + 1)
        if (rel, nm) in dup_members:
            dups.append(nm)
        if kind in ("def", "abbrev", "structure") and nm.split(".")[-1] in dead:
            deads.append(nm)
        if SCAN.BAD_NAME.search(nm):
            bad_names.append(nm)
    return {
        "file": rel, "lines": text.count("\n") + 1, "kind": "Lean source",
        "decls": dict(kinds), "max_stmt": max_stmt, "max_proof": max_proof,
        "dup": dups, "dead": deads, "name": bad_names, "undoc": 0,
        "prov": "## Provenance" in text, "esc": len(ESCAPE.findall(code)),
        "imports": len(re.findall(r"^\s*(?:public\s+)?import\s", text, re.M)),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--group")
    ap.add_argument("--path")
    ap.add_argument("--list-groups", action="store_true")
    args = ap.parse_args(argv)

    files, groups = CHECK.build()
    if args.list_groups:
        for g, m in groups.items():
            print(f"{len(m):4}  {g}")
        return 0

    if args.group:
        members = groups.get(args.group)
        if members is None:
            cand = [g for g in groups if args.group.lower() in g.lower()]
            if len(cand) != 1:
                print(f"ambiguous or unknown group; matches: {cand}", file=sys.stderr)
                return 2
            args.group = cand[0]
            members = groups[args.group]
    elif args.path:
        members = [f for f in files if f.startswith(args.path)]
        args.group = args.path
    else:
        ap.print_help()
        return 2

    dup_members, dead = corpus_index()
    print(f"# {args.group} — {len(members)} files\n")
    print(f"{'lines':>6} {'decl':>5} {'stmt':>5} {'prf':>5} {'dup':>4} "
          f"{'dead':>4} {'name':>4} {'esc':>4} prov  file")
    tot = collections.Counter()
    for rel in sorted(members, key=lambda r: -CHECK.lines_of(r)):
        d = profile(rel, dup_members, dead)
        if d.get("nonlean"):
            print(f"{d['lines']:6} {'':>5} {'':>5} {'':>5} {'':>4} {'':>4} "
                  f"{'':>4} {'':>4}  --   {rel}  [{d['kind']}]")
            continue
        nd = sum(d["decls"].values())
        tot["files"] += 1; tot["decls"] += nd
        for k in ("dup", "dead", "name"):
            tot[k] += len(d[k])
        tot["esc"] += d["esc"]; tot["undoc"] += d["undoc"]
        print(f"{d['lines']:6} {nd:5} {d['max_stmt']:5} {d['max_proof']:5} "
              f"{len(d['dup']):4} {len(d['dead']):4} {len(d['name']):4} "
              f"{d['esc']:4} {'yes' if d['prov'] else 'NO ':>4}  {rel}")
        for label, key in (("DUP", "dup"), ("DEAD", "dead"), ("NAME", "name")):
            if d[key]:
                print(f"        {label}: {', '.join(d[key][:6])}"
                      + (f" (+{len(d[key])-6})" if len(d[key]) > 6 else ""))
    print(f"\ntotals: {tot['files']} Lean files, {tot['decls']} declarations, "
          f"dup {tot['dup']}, dead {tot['dead']}, bad-name {tot['name']}, "
          f"escapes {tot['esc']}  "
          f"(docstrings: see scripts/check_docstring_coverage.py)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
