# Historical repository tools

This directory preserves retired maintenance tools that can still be useful for
repository archaeology, checkpoint recovery, or understanding an earlier
formalization campaign. They are **not current gates or maintenance contracts**.

A tool belongs here when its implementation still captures potentially useful
recovery logic but its inputs, hashes, module list, or campaign assumptions are
frozen to an earlier repository state. New work should use the maintained
source tree and live validators under `scripts/` instead.

- `check_full_part_iii_math_ahead.py` and its adjacent JSON manifest preserve the
  2026-07-20 restoration checkpoint. Its signature hashes are historical and are
  expected to diverge as source-facing declarations evolve.
- `check_repaired_modules.sh` preserves the list of modules and commits used to
  guard an old overlay-heavy compiler-repair campaign. It may be useful for Git
  archaeology when investigating a regression, but its module list is not a
  current build target.

Mutating one-shot migrations and scripts with no plausible recovery value are
not archived here; Git history is sufficient for those.
