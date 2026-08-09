# Historical merge-readiness snapshot

This file is preserved as evidence from the July 2026 hostile-review campaign.
It is **not an operative merge checklist** and it does not describe the current
repository state.

The original document mixed measured green checks with lane assignments and a
hand-maintained list of blockers.  The lane system has since been retired and
many of those blockers were completed, superseded, or converted into automated
gates.  Keeping the old verdict table current would create a second status
system that can disagree with the code.

Use the current authorities instead:

```bash
python3 scripts/run_gates.py
python3 scripts/audit_checklist.py --progress   # historical review coverage only
```

For Tau Ceti submission work, also follow `AGENTS.md`, `ForTauCeti/README.md`,
`dev/tauceti/README.md`, and the current upstream review instructions in the
checked-out Tau Ceti repositories.

The detailed `review-*.md` files in this directory remain useful for rationale
and provenance.  Their `{lane:...}` tags and dated verdicts are historical
identifiers, not tasks to reclaim.
