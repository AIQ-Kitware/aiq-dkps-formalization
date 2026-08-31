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

## Renames lose marks

**Assume a rename drops the mark.**  The header claims marks survive
"Git-detected renames"; measured on 2026-08-31 they do not.  Twelve modules were
renamed with `git mv` and committed, `git diff -M` records all twelve, and
regeneration returned every one of them to `[ ]` — six of which had been
reviewed.  This is an open gap in `aiq-lean source checklist`, recorded in
`AGENTS.md`; until it is fixed the reconciliation is manual.

After any rename sweep:

```bash
git diff --numstat -M <before> HEAD | grep '=>'      # the renames
git show <before>:dev/audit/FILE-CHECKLIST.md        # the marks that existed
```

and re-tick the new paths whose old paths were `[x]`.  Then check the arithmetic
closes: `checked-now + checked-files-deleted + checked-files-no-longer-listed`
should equal the old checked count exactly.  For the 2026-08-31 sweep that was
712 + 80 + 3 = 795, with no file that still exists at an unchanged path losing
its mark.

## What used to be here

Twenty-one review documents from the July 2026 hostile-review campaign, plus a
README describing the retired multi-agent lane system.  They were removed on
2026-08-31: nothing outside this directory read them, their findings had been
acted on or superseded, and the README itself called the corpus "a historical
review corpus, not a current work queue".  They remain in Git history.
