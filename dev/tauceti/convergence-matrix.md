# Convergence matrix - historical migration record

The three-stack convergence campaign is complete enough that this document is no
longer the primary planning authority. Its former body described `ForMathlib`,
`vendor/Spectra`, and a wave/lane workflow that no longer exists.

Current architecture is:

```text
Mathlib / TauCeti foundations
          -> ForTauCeti reusable API
          -> DavisKahan paper-facing consumers
```

Use `AGENTS.md`, `ForTauCeti/README.md`, and
`dev/tauceti/extraction-manifest.json` for current ownership and dependency
information. The Tau Ceti roadmap checkout is under `submodules/TauCetiRoadmap`.

The declaration-by-declaration convergence matrix remains available in Git history
for provenance of migration decisions.
