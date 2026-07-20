# Tau Ceti contribution preparation

These files prepare the current Davis--Kahan development for discussion with
Tau Ceti maintainers.  They are intentionally documentation-only and do not
change any Lean module, aggregate, audit, or build target.

Baseline inspected: `7463ca25c64a46c48411a2769b47714889974a97`.

## Files

- `guidance-issue-draft.md`: proposed Meta issue asking humans how to structure
  the contribution before opening an intention.
- `SpectralSubspacePerturbation/README.md`: draft roadmap specification.
- `SpectralSubspacePerturbation/Suggested.lean.md`: provisional declaration
  shapes, kept subordinate to the prose roadmap.
- `mathematical-declaration-inventory.md`: reusable mathematical content grouped
  by portability and specialization level.
- `source-sine-theta-completion-audit.md`: exact mathematical status of the
  source-general Section 6 theorem and the small remaining audit-hardening queue.
- `finite-dimensional-part-iii-audit.md`: exact claims supported by the stable
  finite source facade, with exclusions.
- `part-iii-production-extraction-queue.md`: the exact 33 proved aliases still
  trapped behind coarse Experimental modules.
- `spectra-provenance-map.md`: upstream, compatibility, dependency, attribution,
  and proposed Tau Ceti treatment of Spectra-derived material.
- `public-api-integration-review.md`: namespace, placement, and PR-boundary
  recommendations for a Tau Ceti port.

The roadmap and issue draft should be revised after maintainers answer the
scope and placement questions.  They should not be submitted as if the current
repository layout were already the desired Tau Ceti layout.  The source-general
Section 6 theorem is complete; the broader roadmap concerns full-paper completion,
production extraction, and library integration rather than reopening that proof.

## Full Part III math-ahead batch

The repository now also carries a candidate full-Part-III proof-closure batch.
It restores 174 exact-signature historical bodies and replaces an unused
speculative continuation roadmap API with the completed proof-carrying
continuation stack.  These candidates are not part of the Tau Ceti-ready
accepted surface until compiled and structurally promoted.  See
`dev/full-part-iii-admission-elimination-math-ahead-2026-07-20.md`.
