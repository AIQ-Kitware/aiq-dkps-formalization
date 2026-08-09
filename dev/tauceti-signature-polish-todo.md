# Historical record: Tau Ceti signature-polish campaign

**Status: campaign completed/superseded.**  This file once held a 2,000-line
rolling backlog.  It is retained only because a few scripts and audit records
cite specific sections that explain why current gates or API decisions exist.
It is not a TODO list.

Current reusable-library policy is in `AGENTS.md` and `ForTauCeti/README.md`.
Current ownership/provenance is in `dev/tauceti/extraction-manifest.json` and the
checked Tau Ceti status tooling.

## §5.1 Approximation-number signatures

The approximation-number API was normalized during the Tau Ceti migration and
its maintained declarations now live under `ForTauCeti`.  Historical migration
notes may mention `ForMathlib`, old codomains, or PR-lane ownership; those are no
longer current instructions.  `scripts/refresh_tauceti_pr1_consistency.py`
contains the surviving packaging consistency check for this area.

## §7 Operator modulus

The campaign removed redundant square/rectangular staging APIs but deliberately
retained two constructions at different generality where the carrier and scalar
assumptions differ: the finite-dimensional `RCLike` polar-decomposition modulus
and the general complex continuous-linear-map modulus.  Their source docstrings
now explain the relationship.  The old proposal to collapse them mechanically
is therefore historical design exploration, not open debt.

## §13 Declaration-name drift gate

A durable outcome of the campaign was the need to check declaration names that
are copied into data or unguarded challenge files.  That requirement is now
implemented by:

```bash
python3 scripts/check_declaration_name_drift.py
```

The gate, not the former grep-worklist prose, is the current authority.

## Reading old references

Review files may cite this document by section number.  The headings above are
kept so those citations remain meaningful.  For detailed chronology or rejected
alternatives, use Git history rather than restoring the rolling backlog here.
