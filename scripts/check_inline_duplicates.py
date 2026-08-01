#!/usr/bin/env python3
"""Find inline `have` steps that are probably re-proving a lemma that already exists.

**Every check in this repository is name-based, and an inline `have` has no
name.**  That is the blind spot this script exists to narrow, and it was found
twice in one day by hand:

* `{lane:DK-LONGPROOF-1}` cut `exists_rank_le_norm_doubleAngleTangent_sub_lt`
  from 231 body lines to 34.  Fifty of those lines were hand-rolling
  `abs_doubleAngleTangent_sub_le`, which sits **three hundred lines above them in
  the same file**, and whose docstring says it exists so callers need not redo
  the estimate.  Three more lines re-derived `doubleAngleTangent_nonneg`, which
  that file **imports**.
* `{lane:DK-LONGPROOF-3}` cut `norm_projection_sub_projection_graphSubspace` from
  302 to 275 against four Mathlib lemmas: `IsSelfAdjoint.ringInverse`,
  `IsSelfAdjoint.star_mul_self`, `IsSelfAdjoint.mul_star_self` and
  `CStarRing.norm_self_mul_star`.

Two files, no shared author, no shared import, no shared subject, same defect.

## What this is not

**It cannot prove a `have` is a duplicate.**  That needs elaboration, and running
`exact?` over every `have` in two libraries is not a check anyone will run twice.
So this is a *candidate finder*: its output is a worklist for a human or an agent
to confirm, and confirming means trying the named lemma and seeing the proof
shrink.  A finding here is a question, not a verdict.

It is deliberately **not wired into `run_gates.py`**.  It fires on correct code —
a `have` may legitimately restate a global fact in a form the surrounding proof
can use — and a check that fires on correct code trains everyone to ignore the
suite.  That is what `ADVISORY` in `run_gates.py` exists to prevent, and what
`check_merge_losses` already forced once.

## The three signals, and why these three

Each was chosen because it fires on one of the duplicates actually removed, and
between them they cover all six.  `--why` prints which fired.

**`general`** -- the statement, after transitively substituting every local
`set`/`let` definition, names nothing bound inside the proof.  This is the
**weakest** of the three; see "Where `general` misleads" below before ranking by
it.  Catches `hBsa`, `hnorm_sq_eq`, `hRsa`
(only after substitution: `R` unfolds to `Ring.inverse N`, `N` to
`1 + star (X * P) * (X * P)`, `P` to `projection U`).

**`self-contained`** -- the step's *proof* cites no other local `have`.  A step
that needs nothing from its context did not need to be inside the proof.  Catches
`htanv0`, `htau0`, `hBsa`, `hnorm_sq_eq`.  Misses `hRsa`, whose proof does use
two earlier steps -- which is why both signals are needed and why the report is
their union rather than their intersection.

**`repeated`** -- the same statement text, whitespace-normalised, appears on more
than one step anywhere in the scan.  Catches `hPR`, which appears in **two
different theorems** of `GraphSubspace.lean`; that duplicate was found only
because an edit failed with `unknown identifier` in a theorem nobody had read.
This signal does no alpha-renaming, so it finds textual twins only -- a real
limit, and the reason it is one signal of three rather than the whole script.

**It also has a false-positive mode, found on `{lane:DK-LONGPROOF-6}` and worth
checking every time.**  Textual matching cannot see what a local name *denotes*.
`projection_mul_spectraDirectRotation_mul_projection` and its complementary twin
each open with `let P := ...` -- one `projection U`, the other
`complementaryProjection U` -- so `S * P = Q * P` is reported as repeated while
being two different statements, proved from different lemmas.  **Sibling proofs
that share a naming convention will always do this.**  Before extracting, read
the `let`/`set` bindings at both sites; it takes seconds and it is not optional.

**The opposite blind spot is just as real** (`{lane:DK-LONGPROOF-7}`):
`RitzResidual.lean` and `Theorem63FiniteSource.lean` contain the same witness
construction line for line, over `LinearMap`/`𝕜` and `ContinuousLinearMap`/`ℂ`
respectively.  A cross-file scan of the two returns exactly one match, `0 < c`,
which is noise.  **Textual matching reports a match that is not one, and misses
one that is** -- both because it matches text rather than meaning, which is the
same property that makes it cost a second instead of a rebuild.

## Two products from one scan, and how to ask for each

Ranking by proof length was the obvious thing to do and it turned out to answer a
*different* question than the one this script was written for.  The long general
steps at the top of the list are **liftable blocks** -- `hlower` in
`doubleAngleTangent_approximationNumber_le` is 167 lines and is a theorem in
disguise -- while the **duplicates** are short.  Both are worth having; ask for
them separately.

    --min-body 2 --max-body 8 --only repeated   # duplicates: the tight worklist
    --min-body 30                               # blocks that want extracting

`--only repeated` is the highest-precision view and the one to start from: a
statement that appears verbatim on two different steps is a duplicate of
something, whatever that something turns out to be.

Steps whose proof is shorter than `--min-body` are dropped, because a one-line
`have h := foo.1` has nothing to save even when it is technically general.  The
default is 2 rather than 3 because `hBsa`, `hB'sa` and `htanv0` -- three of the
six known duplicates -- have two-line proofs, and a default that misses half the
evidence is the wrong default.

## Where `general` misleads, measured

**`general` is a weak signal and the docstring above oversold it.**  It says a
statement built only from globals and the theorem's binders "*is* a general
lemma, and general lemmas are the ones Mathlib already has".  The first half is
true; the second does not follow.  On a proof whose *subject matter* is general
algebra, nearly every step is general-looking and almost none is redundant.

Measured, not guessed: `{lane:DK-LONGPROOF-4}` took
`eigen_cos_two_theta_bound` (420 lines) because it scored **44 general
candidates**, the densest in the tree -- and **one** survived.  The same lane's
sibling `{lane:DK-LONGPROOF-2}` scored six and four survived.  The difference is
visible in the scores themselves: the first had **0 `repeated`**, the second had
duplicates confirmed by hand.

So: **`repeated` is the signal to rank by**; read `general` as *extraction*
density, and expect it to be mostly false positives on algebra-heavy proofs.
`--only repeated` exists for this reason and is the recommended entry point.

## What it found that reading did not

`hPR` in `GraphSubspace.lean` appears **three** times, not twice.  Two were known
-- one of them only because an edit failed with `unknown identifier` in a theorem
nobody had read -- and the third, in `acuteAngularOperator_spec`, was found by
this script.  That is the argument for the script over more careful reading.

## Honesty about precision

This is textual, not elaborated.  It does not know types, does not resolve
namespaces, and treats a variable bound by `∀` inside a statement the same as any
other token.  Expect false positives; that is the price of a check that runs in
under a second instead of rebuilding two libraries.  What it must not do is
*miss* the six known cases, and `scripts/tests/test_check_inline_duplicates.py`
pins exactly that against the pre-fix revisions in git.

    python3 scripts/check_inline_duplicates.py                 # both libraries
    python3 scripts/check_inline_duplicates.py --lib DavisKahan
    python3 scripts/check_inline_duplicates.py --file path.lean --why
    python3 scripts/check_inline_duplicates.py --min-body 5 --top 20
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

#: Production libraries.  `Experimental/` is excluded everywhere else in this
#: repository's tooling and is excluded here for the same reason: it is a
#: scratch tree and its duplicates are not defects.
LIBRARIES = ("ForTauCeti", "DavisKahan")

OPENERS = "([{⟨⦃"
CLOSERS = ")]}⟩⦄"

#: A step that states something and then proves it.
STEP = re.compile(r"^(?P<indent>\s*)(?P<kw>have|obtain|suffices)\b(?P<rest>.*)$")

#: A local definition whose body can be substituted back into a statement.
BIND = re.compile(r"^\s*(?:set|let)\s+(?P<name>[^\s:=]+)\s*(?::[^=]*)?:=\s*(?P<body>.*?)"
                  r"(?:\s+with\s+\S+)?\s*$")

#: Names a tactic introduces into scope.
INTRO = re.compile(r"^\s*(?:intro|intros|rintro)\s+(?P<names>.*?)\s*$")

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

COMMENT = re.compile(r"--.*$")


def strip_comment(line: str) -> str:
    return COMMENT.sub("", line)


def split_top_level(text: str, token: str) -> tuple[str, str] | None:
    """Split on the first `token` that is not inside brackets.  None if absent."""
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif depth == 0 and text.startswith(token, index):
            return text[:index], text[index + len(token):]
        index += 1
    return None


def normalise(text: str) -> str:
    return " ".join(text.split())


class Step:
    def __init__(self, name: str, statement: str, body: list[str],
                 decl: str, path: pathlib.Path, line: int) -> None:
        self.name = name
        self.statement = statement
        self.body = body
        self.decl = decl
        self.path = path
        self.line = line
        self.signals: list[str] = []

    @property
    def body_length(self) -> int:
        return len([line for line in self.body if line.strip()])

    @property
    def where(self) -> str:
        try:
            shown = self.path.relative_to(ROOT)
        except ValueError:
            shown = self.path
        return f"{shown}:{self.line}"


def declarations(lines: list[str]) -> list[tuple[int, int, str]]:
    """(start, end, name) for each top-level declaration with a body."""
    head = re.compile(r"^(?:@\[[^]]*\]\s*)?(?:public |private |protected |noncomputable |"
                      r"partial |unsafe )*(?:theorem|lemma|def|instance)\s+"
                      r"(?P<name>[^\s({\[:]+)")
    out = []
    starts = [i for i, line in enumerate(lines) if head.match(line)]
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        out.append((start, end, head.match(lines[start]).group("name")))
    return out


def steps_in(path: pathlib.Path) -> list[Step]:
    """Every `have`/`obtain`/`suffices` with an explicit statement, with its proof.

    **Locals are scoped by indentation, and that is not a refinement.**  Without
    it an `intro i` inside one step's proof stays in scope for every later step,
    so a sibling that quantifies over its own `i` reads as depending on the first
    one's.  That single leak lost `htauNonneg` -- one of the six duplicates this
    script exists to find -- while `htau0` twelve lines above it was found.
    """
    lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    found: list[Step] = []
    for start, end, decl in declarations(lines):
        binds: list[tuple[int, str, str]] = []       # (indent, name, body)
        locals_: list[tuple[int, str]] = []          # (indent, name)
        index = start
        while index < end:
            raw = strip_comment(lines[index])
            if not raw.strip():
                index += 1
                continue
            depth = len(raw) - len(raw.lstrip())
            # Leaving a block drops everything introduced inside it.
            binds = [b for b in binds if b[0] <= depth]
            locals_ = [l for l in locals_ if l[0] <= depth]
            bind = BIND.match(raw)
            if bind:
                binds.append((depth, bind.group("name"), bind.group("body").strip()))
                locals_.append((depth, bind.group("name")))
                index += 1
                continue
            intro = INTRO.match(raw)
            if intro:
                locals_.extend((depth, n) for n in IDENT.findall(intro.group("names")))
                index += 1
                continue
            match = STEP.match(raw)
            if not match:
                index += 1
                continue
            head_lines = [match.group("rest")]
            cursor = index
            while cursor + 1 < end and split_top_level(" ".join(head_lines), ":=") is None:
                cursor += 1
                head_lines.append(strip_comment(lines[cursor]))
            head = " ".join(head_lines)
            parts = split_top_level(head, ":=")
            if parts is None:
                index += 1
                continue
            signature = parts[0]
            typed = split_top_level(signature, ":")
            if typed is None:
                index = cursor + 1
                continue
            binder, statement = typed
            name = (IDENT.search(binder).group(0) if IDENT.search(binder) else "_")
            indent = len(match.group("indent"))
            body: list[str] = []
            probe = cursor + 1
            while probe < end:
                line = lines[probe]
                if line.strip() and len(line) - len(line.lstrip()) <= indent:
                    break
                body.append(line)
                probe += 1
            step = Step(name, normalise(statement), body, decl, path, index + 1)
            step._binds = {n: b for _, n, b in binds}              # noqa: SLF001
            step._locals = {n for _, n in locals_}                 # noqa: SLF001
            found.append(step)
            # The step's own name is in scope for everything after it.
            locals_.extend((depth, n) for n in IDENT.findall(binder))
            index = cursor + 1
    return found


def substitute(statement: str, binds: dict[str, str], rounds: int = 8) -> str:
    """Transitively inline local `set`/`let` bodies so the statement stands alone."""
    text = statement
    for _ in range(rounds):
        replaced = False
        for name, body in binds.items():
            pattern = re.compile(rf"(?<![A-Za-z0-9_.']){re.escape(name)}(?![A-Za-z0-9_'])")
            if pattern.search(text):
                text = pattern.sub(f"({body})", text)
                replaced = True
        if not replaced:
            break
    return text


def classify(steps: list[Step], min_body: int, max_body: int | None = None,
             only: str | None = None) -> list[Step]:
    by_statement: collections.Counter = collections.Counter(s.statement for s in steps)
    out = []
    for step in steps:
        if step.body_length < min_body:
            continue
        if max_body is not None and step.body_length > max_body:
            continue
        binds = getattr(step, "_binds", {})
        locals_ = getattr(step, "_locals", set())
        expanded = substitute(step.statement, binds)
        # Names bound by an earlier step, minus those we just substituted away.
        opaque = {n for n in locals_ if n not in binds}
        if not (set(IDENT.findall(expanded)) & opaque):
            step.signals.append("general")
        cited = set(IDENT.findall(" ".join(strip_comment(l) for l in step.body)))
        if not (cited & opaque):
            step.signals.append("self-contained")
        if by_statement[step.statement] > 1:
            step.signals.append("repeated")
        if only and only not in step.signals:
            continue
        if step.signals:
            out.append(step)
    return sorted(out, key=lambda s: -s.body_length)


def lean_files(library: str) -> list[pathlib.Path]:
    root = ROOT / library
    return sorted(p for p in root.rglob("*.lean") if "Experimental" not in p.parts)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--lib", choices=LIBRARIES, help="restrict to one library")
    parser.add_argument("--file", help="scan a single file instead of a library")
    parser.add_argument("--min-body", type=int, default=2,
                        help="ignore steps whose proof is shorter than this (default 2: "
                             "two of the six known duplicates have two-line proofs)")
    parser.add_argument("--max-body", type=int, default=None,
                        help="ignore steps whose proof is longer than this; pair with "
                             "--min-body to ask for duplicates rather than liftable blocks")
    parser.add_argument("--only", choices=("general", "self-contained", "repeated"),
                        help="require this signal (`repeated` is the highest-precision one)")
    parser.add_argument("--top", type=int, default=25, help="how many findings to print")
    parser.add_argument("--why", action="store_true", help="print which signals fired")
    parser.add_argument("--check", action="store_true",
                        help="exit 1 if anything was found (for a human, not a hook -- "
                             "these are candidates, not defects)")
    args = parser.parse_args(argv)

    if args.file:
        paths = [pathlib.Path(args.file)]
    else:
        paths = [p for lib in ([args.lib] if args.lib else LIBRARIES) for p in lean_files(lib)]

    steps: list[Step] = []
    for path in paths:
        steps.extend(steps_in(path))
    findings = classify(steps, args.min_body, args.max_body, args.only)

    print(f"scanned {len(paths)} file(s), {len(steps)} stated step(s) with a proof")
    tally = collections.Counter(sig for f in findings for sig in f.signals)
    bounds = f"--min-body {args.min_body}" + (f" --max-body {args.max_body}"
                                              if args.max_body is not None else "")
    print(f"{len(findings)} candidate(s) at {bounds}"
          + (f" --only {args.only}" if args.only else "")
          + f"; showing {min(args.top, len(findings))}")
    print("  by signal: " + ", ".join(f"{sig} {n}" for sig, n in sorted(tally.items())))
    print("  These are CANDIDATES.  Confirm one by trying the lemma you think it")
    print("  duplicates and seeing the proof shrink; a finding here is a question.")
    print()
    for step in findings[:args.top]:
        why = f"  [{', '.join(step.signals)}]" if args.why else ""
        print(f"  {step.body_length:3d} lines  {step.where}  {step.decl}:{step.name}{why}")
        print(f"            {step.statement[:140]}")
    if len(findings) > args.top:
        print(f"\n  ... {len(findings) - args.top} more not shown (raise --top)")
    return 1 if (args.check and findings) else 0


if __name__ == "__main__":
    sys.exit(main())
