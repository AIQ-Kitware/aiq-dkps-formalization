# A generator rewrote 21 real files while proving that it rewrites files

**Date:** 2026-07-29. **Context:** fixing `scripts/generate_all_aggregates.py`,
which regenerates the import-only `All.lean` aggregate of every production
directory. Two bugs were found; verifying the fix triggered one of them against
the live tree, and `git add -A` then committed the damage.

## Symptom

`git show --stat` on a commit whose message says *"No .lean file is modified by
this commit"*:

```
 scripts/generate_all_aggregates.py                 |  83 ++++--
 scripts/tests/test_generate_all_aggregates.py      | 156 +++++++++++
 DavisKahan/FiniteDimensional/Core/All.lean         |   3 -
 DavisKahan/FiniteDimensional/SinTheta/All.lean     |   3 -
 DavisKahan/FiniteDimensional/Sylvester/All.lean    |   3 -
 ... 21 aggregates modified, 3 created
```

Every one of those `3 -` deletions is a cross-library `import ForTauCeti.…`
re-export — the migrated Davis–Kahan modules — silently dropped out of the
default build.

## What it was NOT

- **Not the fixed script.** The fix was correct and its tests passed. Running the
  *fixed* generator preserves all 21 re-exports; that was verified before and
  after.
- **Not a bad `git add` pattern alone.** `git add -A` is what *captured* it, but
  the files were already dirty. Staging a narrower path would have hidden the
  damage in the working tree instead of committing it — arguably worse.
- **Not a merge or another agent.** The working tree was clean immediately
  before.

## Root cause

Two independent defects composed:

1. The old entry point was `check = "--check" in sys.argv[1:]`. Any unrecognised
   argument — including `--help` — is "not a check", so it fell through to the
   **write** path. Asking the tool for its usage rewrote the tree.
2. The new regression tests included subprocess cases asserting that a broken
   entry point does *not* write. To prove they actually catch the bug, they were
   run against the **pre-fix** script — and that script was invoked with its
   `ROOT` bound to the **real repository**, because `ROOT` is derived from
   `__file__.parents[1]`.

So the test that existed to pin the bug *executed* the bug, at full scale, on the
live tree. Then `git add -A` swept the result into a commit that claimed to touch
no Lean file.

## Fix

- `argparse`, so `--help` prints usage and an unknown flag exits non-zero.
- Preserve cross-library re-exports: they are read back out of the existing
  aggregate and merged in, sorted by leaf name so each keeps the slot of the
  module it replaced. A re-export whose target file no longer exists is reported
  and dropped.
- **Sandbox the subprocess tests.** They now copy the generator into the temp
  directory, so `ROOT` resolves there and a broken entry point can only damage
  the sandbox. Each also asserts positively that no aggregate file was created.
- Revert commit restoring all 21 aggregates byte-identically; net `.lean` change
  across the pair of commits is empty.

## Takeaway

**A destructive tool's regression test must run the tool somewhere it is allowed
to be destructive.** The test was well-designed in intent — "verified to fail,
not merely to pass" is this repository's own standard — and the act of meeting
that standard is what caused the damage, because the harness never asked *where*
the subprocess would write.

Two rules worth carrying:

- If a script derives its working root from `__file__`, a test that runs it as a
  subprocess **is** running it against the repository unless the script is
  copied elsewhere first. Import-and-monkeypatch-`ROOT` is safe; `subprocess` on
  the real path is not.
- `git add -A` after running any generator is how a "documentation only" commit
  acquires 24 Lean files. Check `git status` against the claim in the commit
  message *before* committing, not after — and note that `git commit` takes the
  whole index, so a later `git add <one-path>` does not narrow what a previously
  staged `git rm` or generator run will carry in.

The deeper one: this generator had been silently wrong for as long as the Tau
Ceti migration has been running. **Nothing downstream could have caught it** —
an aggregate that imports *less* still compiles, so a green build is not
evidence. The same shape recurs across this repository's tooling: on the same
day, `verify_spectra_reference.py` was found printing the superproject's HEAD as
a submodule pin, and `refresh_tauceti_pr1_consistency.py` was found ready to
stamp this repository's own commit into a manifest as the Tau Ceti revision.
**A tool that reports a plausible wrong answer is more expensive than one that
crashes**, and every one of these was found by running the tool and reading the
output rather than by any gate.
