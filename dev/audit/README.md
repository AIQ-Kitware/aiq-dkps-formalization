# Review checklists

Two generated files, and nothing else:

- `FILE-CHECKLIST.md` — every file in the repository, once, with a `[x]` when it
  has been reviewed;
- `GROUP-CHECKLIST.md` — the same coverage rolled up by directory group.

Both are produced by

```bash
aiq-lean source checklist            # regenerate, preserving marks
aiq-lean source checklist --progress # report without writing
```

which lives in `aiq-lean-formalization-tools`, not in `scripts/`.  **Do not
hand-maintain the lists**, and do not delete them: regeneration preserves the
`[x]` marks it finds in the existing file, so the file *is* the review state.
Rerun after files move or land; new files appear unchecked and vanished files
drop out.

Rename detection is not reliable enough to trust blindly.  The 2026-08-31
honesty campaign renamed twelve modules with `git mv`, committed the renames,
and regeneration still returned six reviewed files to `[ ]`.  After a rename
sweep, diff the mark count against the previous revision and restore what the
regeneration dropped.

## What used to be here

Twenty-one review documents from the July 2026 hostile-review campaign, plus a
README describing the retired multi-agent lane system.  They were removed on
2026-08-31: nothing outside this directory read them, their findings had been
acted on or superseded, and the README itself called the corpus "a historical
review corpus, not a current work queue".  They remain in Git history.
