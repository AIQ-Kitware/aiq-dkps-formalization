# `dev/topurge/root-scratch/` — twelve files moved off the repository root

**jon's goal, 2026-08-02: "make this repo beautiful."** These twelve files sat at
the top level of the repository, which is the first thing a Tau Ceti reviewer
sees. `AGENTS.md` sets the acceptance test as a reviewer saying *"yes, that's
ready"*, and adds that **anything which would make a reviewer hesitate at that
moment is a defect**. A root directory holding overlay manifests for a zip
archive, another agent's branch prompt, and a handoff note addressed to a
specific agent is exactly such a hesitation.

**Nothing was deleted.** Each file moved with `git mv`, so the diff is
rename-only and every file keeps its history — the same treatment, and for the
same reason, as the 79 files in the parent directory.

## What is here

- **Nine overlay/scratch manifests** (`*_MANIFEST.txt`, one `.manifest.json`).
  Each records the contents of a zip overlay applied at some point during the
  campaign. They name absolute paths on machines that no longer matter
  (`OVERLAY_MANIFEST.txt` targets `/home/joncrall/code/aiq-dkps-namek`) and base
  commits long since superseded. No script, Lean file, or build target reads any
  of them — checked before moving.
- **`HANDOFF-toothbrush-2026-07-29.md`** — its own second line reads
  *"**Temporary file.** Delete once absorbed into `dev/LANES.md` / `dev/tauceti/*`."*
  It was absorbed; the file stayed. Archiving rather than deleting keeps the
  three documents that cite it resolving.
- **`prompt.txt`** — an agent prompt beginning *"Your branch is `namek-work`."*
  There is one agent now and it works on `main`.
- **`tan2theta-strat.md`** — a strategy note on routing around
  `exists_unboundedApproximateLeadingSingularFamily`.

## What this does not change

The parent `dev/topurge/MANIFEST.md` records a decision — *leave this directory,
do not propose deleting it again* — about the 79 files staged there on
2026-07-29. That decision stands untouched. This is a new subdirectory holding
different files, moved for the same reason and by the same method; it neither
revisits that decision nor adds anything to the set it covers.
