#!/usr/bin/env python3
"""Run every `scripts/check_*.py` with the right flag, and fail if any of them finds something.

**There was no runner.  Every caller wrote its own loop, and each loop got this
wrong differently** -- which is finding AT-6 in `dev/audit/review-audit-tail.md`,
and which this script exists to end.

The classes, measured rather than tabulated (2026-07-31, 29 gates):

  * **9 are soft** -- they print the finding and `return 1 if args.check else 0`,
    so without the flag a defect is indistinguishable from a clean run.
  * **4 accept `--check`** and are strict either way.
  * **16 take no `--check` at all** and are always strict.
  * **2 are advisory** -- see `ADVISORY`.
  * **1 accepts `--check` and is deliberately not given it** -- see
    `CHECK_IS_STRONGER`, which is where deriving the classification from
    `argparse` stops being enough.

  (`--list` prints the current split; the counts above are a snapshot and the
  classification itself is always derived, never read from this comment.)

So the naive runner -- pass `--check` to everything -- is *worse than no runner*:
fourteen gates die with `unrecognized arguments: --check`, turning fourteen
passing checks red while saying nothing about the nine that actually matter.  The
opposite naive runner -- pass nothing -- silently accepts every finding those
nine report.  Both were tried in one session on 2026-07-31.

Two gates -- `check_davis_kahan_1970_source_census` and
`check_distilled_literature_index` -- contain the string `--check` only because
they *pass* it to a renderer subprocess, and neither uses `argparse` at all, so
they ignore every argument silently.  A grep-based classifier gets both wrong;
reading the `argparse` setup gets both right.

## Why the classification is derived and not a list

A hardcoded table of which gates take `--check` is a second thing to keep in
sync with the gates, and **this repository has spent the day fixing exactly that
failure**: manifests, topic tables and roadmaps that named modules and went stale
when the modules moved.  A list here would go stale the first time somebody adds
a gate.  So the runner reads each script's own `argparse` setup and asks it.

## Where deriving it stops working

Reading `argparse` tells you a gate *accepts* `--check`.  It does not tell you
what `--check` **means** there, and one gate means something else by it:
`check_davis_kahan_frontier` is strict on real problems either way, and its
`--check` additionally requires every paper result to be recursively grounded --
a completion target, 59 of 80 today.  **That was found by running the suite, not
by reading the code**, and it is why `CHECK_IS_STRONGER` is a short hand-written
list with a reason per entry rather than another derivation.  Two entries of
judgement beside twenty-seven derivations is the right ratio; twenty-seven
entries of judgement would be the table this script exists to avoid.

## Consequence

With `--check` passed wherever it is both accepted and meant, **every gate is
strict at the point of use**, and the soft/strict split stops mattering to
callers without any of the nine scripts changing.  That is deliberate: making
them strict by default is a nine-file change with nine chances to alter
behaviour, and it is not needed to get the guarantee.

**Do not run `lake` while this is running.**  Five gates invoke `lake` and a
concurrent build makes them fail with `build failed` -- which reads exactly like
a regression and is not one.  On 2026-07-31 that cost a full investigation:
`check_experimental_root_status` reported "lake build DavisKahan.Experimental did
not succeed", and the same build run alone immediately afterwards was green
(9210 jobs).  The suite was racing the author's own editing loop.  Use `--fast`
if you need to keep building; it skips exactly those five.

    python3 scripts/run_gates.py              # every gate
    python3 scripts/run_gates.py --fast       # skip the ones that build Lean
    python3 scripts/run_gates.py --list       # show the classification, run nothing
    python3 scripts/run_gates.py -k namespace # only gates matching a substring
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"

#: Gates that invoke `lake` and take minutes to tens of minutes.  `--fast` skips
#: them.  Being on this list is a statement about runtime only -- every one of
#: them still runs in a full pass, and `--fast` prints what it skipped so a green
#: fast run is never mistaken for a green full run.
SLOW = {
    "check_comparator_signatures",
    "check_davis_kahan_frontier",
    "check_davis_kahan_hidden_foundations",
    "check_experimental_root_status",
    "check_full_part_iii_math_ahead",
}

#: Investigative reports that live in `scripts/check_*.py` but are **not gates**:
#: they fire on ordinary, correct activity, so failing the suite on them would
#: train everyone to ignore the suite.  They are run and their output is shown,
#: but they cannot fail the run.
#:
#: `check_merge_losses` is the case that forced this distinction, and it is the
#: author's own doing: its docstring says `--check` is "for a human after a merge
#: session and not for a hook, because it fires on every legitimate rename".
#: Wiring it into the runner as a gate contradicted its own documentation within
#: an hour of writing it.  A rename is not a defect and never becomes one.
ADVISORY = {
    "check_inline_duplicates":
        "reports inline `have` steps that may be re-proving an existing lemma; it "
        "cannot elaborate, so every finding is a candidate for a human to confirm, "
        "and a `have` may legitimately restate a global fact in a usable form",
    "check_merge_losses":
        "reports every declaration a merge dropped, which includes every rename "
        "and every deliberate retirement; the list is for a human to adjudicate",
    "check_rw_chains":
        "reports `rw` chains the proof-quality rubric calls brittle; three live ones "
        "in ForTauCeti are correct and documented in-source, because `simp only` with "
        "the same lemmas either loops or cannot reach the intermediate shape",
}

#: Gates where `--check` is not the soft/strict toggle it is everywhere else, but
#: a **stronger, aspirational** criterion.  The runner deliberately does *not*
#: pass the flag to these; their default mode is the regression gate.
#:
#: **This is the limit of deriving the classification from `argparse`, and it was
#: found by running the suite rather than by reading the code.**  Accepting
#: `--check` does not tell you what `--check` means.
#: `check_davis_kahan_frontier` is strict on real problems either way; its
#: `--check` *additionally* demands that every paper result be recursively
#: grounded, which is a project-completion target (59 of 80 today).  Passing the
#: flag would make the suite permanently red on an unmet ambition -- the same
#: "trains everyone to ignore it" failure that `ADVISORY` exists to prevent.
CHECK_IS_STRONGER = {
    "check_davis_kahan_frontier":
        "--check demands full recursive grounding of every paper result, a "
        "completion target and not a regression; the default mode is the gate",
}

#: Recognised by reading the script rather than by running `--help`, which for
#: the slow gates would mean starting a Lean build just to ask a question.
CHECK_FLAG = re.compile(r"""add_argument\(\s*["']--check["']""")

#: A gate that reports a finding and exits 0 unless `--check` is passed.
SOFT = re.compile(r"return\s+1\s+if\s+args\.check\s+else\s+0")


class Gate:
    def __init__(self, path: pathlib.Path) -> None:
        self.path = path
        self.name = path.stem
        source = path.read_text(encoding="utf-8")
        self.takes_check = (bool(CHECK_FLAG.search(source))
                            and self.name not in CHECK_IS_STRONGER)
        self.soft = bool(SOFT.search(source))

    @property
    def advisory(self) -> bool:
        return self.name in ADVISORY

    @property
    def kind(self) -> str:
        if self.name in CHECK_IS_STRONGER:
            return "strict, --check withheld (it is a completion target)"
        if self.advisory:
            return "advisory (reported, cannot fail the run)"
        if self.soft:
            return "soft (strict only with --check)"
        if self.takes_check:
            return "strict, accepts --check"
        return "strict, no flag"

    def command(self) -> list[str]:
        argv = [sys.executable, str(self.path)]
        if self.takes_check:
            argv.append("--check")
        return argv


def gates() -> list[Gate]:
    return [Gate(p) for p in sorted(SCRIPTS.glob("check_*.py"))]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast", action="store_true",
                        help="skip the gates that build Lean")
    parser.add_argument("--list", action="store_true",
                        help="print the classification and exit")
    parser.add_argument("-k", "--filter", default="",
                        help="only gates whose name contains this substring")
    parser.add_argument("--timeout", type=int, default=3600,
                        help="per-gate timeout in seconds")
    args = parser.parse_args()

    selected = [g for g in gates() if args.filter in g.name]
    if args.list:
        for gate in selected:
            slow = " [slow]" if gate.name in SLOW else ""
            print(f"{gate.name:<40} {gate.kind}{slow}")
        soft = sum(1 for g in selected if g.soft)
        flag = sum(1 for g in selected if g.takes_check and not g.soft)
        print(f"\n{len(selected)} gate(s): {soft} soft, {flag} strict with a flag, "
              f"{len(selected) - soft - flag} strict with no flag")
        return 0

    skipped = [g.name for g in selected if args.fast and g.name in SLOW]
    to_run = [g for g in selected if not (args.fast and g.name in SLOW)]

    failed: list[tuple[str, str]] = []
    advisories: list[tuple[str, str]] = []
    for gate in to_run:
        print(f"{gate.name:<40} ", end="", flush=True)
        started = time.monotonic()
        try:
            done = subprocess.run(gate.command(), capture_output=True, text=True,
                                  timeout=args.timeout, cwd=ROOT)
            code, output = done.returncode, done.stdout + done.stderr
        except subprocess.TimeoutExpired:
            code, output = 124, f"timed out after {args.timeout}s"
        elapsed = time.monotonic() - started
        if code == 0:
            print(f"OK    {elapsed:6.1f}s")
        elif gate.advisory:
            print(f"NOTE  {elapsed:6.1f}s  (advisory -- {ADVISORY[gate.name]})")
            advisories.append((gate.name, output))
        else:
            print(f"FAIL  {elapsed:6.1f}s  (exit {code})")
            failed.append((gate.name, output))

    print()
    if skipped:
        print(f"SKIPPED {len(skipped)} slow gate(s) because of --fast: "
              f"{', '.join(sorted(skipped))}")
        print("  A green --fast run is not a green run.  These build Lean and are")
        print("  the ones a refactor is most likely to have broken.")
        print()

    for name, output in advisories:
        print(f"----- {name} (advisory, does not fail the run)")
        tail = [line for line in output.strip().split("\n") if line.strip()][-6:]
        for line in tail:
            print(f"  {line}")
        print()

    if not failed:
        print(f"gates: OK -- {len(to_run)} of {len(selected)} passed"
              + (f", {len(skipped)} skipped" if skipped else ""))
        return 0

    for name, output in failed:
        print(f"===== {name}")
        tail = [line for line in output.strip().split("\n") if line.strip()][-12:]
        for line in tail:
            print(f"  {line}")
        print()
    print(f"gates: {len(failed)} of {len(to_run)} FAILED "
          f"({', '.join(name for name, _ in failed)})")
    return 1


if __name__ == "__main__":
    sys.exit(main())
