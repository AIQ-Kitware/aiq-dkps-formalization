# Lean import / DKPS lineage bridge: audited snapshot

This report is generated from the user-provided `pins.json` and `source-imports.json`,
the existing DKPS contribution census, and (when available) the Operator Theory roadmap
obligation ledger. It is an intermediate evidence layer, **not a completed theorem graph**.

- Snapshot head in `pins.json`: `8fb4ea3d2122cb442f7043e5de5002cbc966ba81`
- TauCeti dependency revision: `a67a65006c07449dcb2ebe1a3a8b6bf6e0b909f8`
- Lean toolchain: `leanprover/lean4:v4.36.0-rc2`
- Local Lean modules: **1362**; local module-import edges: **3976**.
- Distinct directly imported TauCeti modules: **143**; Mathlib: **289**.
- Explicit-origin PR rows in maintained DKPS census: **32**.
- Explicit roadmap IDs referenced by those rows: **61**.
- IDs intersecting the supplied roadmap-obligation ledger: **61**.

## Example proof-facing module import boundaries

| Source module | Local modules in import closure | Reachable TauCeti modules | Reachable Mathlib modules |
|---|---:|---:|---:|
| `DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation` | 313 | 91 | 99 |
| `DavisKahan.Sources.DavisKahan1970.Sylvester.All` | 122 | 68 | 55 |
| `DavisKahan.Sources.DavisKahan1970.TanTheta` | 155 | 71 | 61 |
| `DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded` | 364 | 92 | 107 |
| `DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExact` | 189 | 75 | 76 |
| `DavisKahan.Sources.DavisKahan1970.Section8.Theorem81` | 186 | 76 | 70 |
| `DavisKahan.Sources.DavisKahan1970.Section8.Theorem82` | 316 | 90 | 98 |
| `DavisKahan.Sources.DavisKahan1970.Section4DirectRotationSource` | 246 | 89 | 94 |
| `DavisKahan.Sources.DavisKahan1970.Section9.All` | 259 | 78 | 122 |
| `DavisKahan.Sources.DavisKahan1970.All` | 1148 | 128 | 232 |

The counts above describe imports reachable by following only **local** module imports.
They do not include transitive imports within TauCeti or Mathlib, do not identify constants
mentioned by proof terms, and are not proof complexity scores.

## Confirmed evidence categories

The maintained DKPS census has a table of upstream PRs with *explicit DKPS origin*.
Its entries carry evidence codes and donor descriptions. The companion JSON records
exact PR links and source line numbers. For example:

- [PR #13599](https://github.com/TauCetiProject/TauCeti/pull/13599), PD-A50–A53: Courant–Fischer and Weyl — census `D, M13; [28 October donor/accepted-proof comparison](../../papers/dk_formalization_journal/COURANT_FISCHER_LINEAGE_AUDIT.md)`; `dev/tauceti/dkps-upstream-contribution-census.md:150`.
- [PR #17527](https://github.com/TauCetiProject/TauCeti/pull/17527), SA-B14–B23: abstract projection-valued measures — census `D, B`; `dev/tauceti/dkps-upstream-contribution-census.md:158`.
- [PR #18917](https://github.com/TauCetiProject/TauCeti/pull/18917), SA-C66–C72: domain-aware Sylvester — census `D, B`; `dev/tauceti/dkps-upstream-contribution-census.md:163`.
- [PR #19299](https://github.com/TauCetiProject/TauCeti/pull/19299), SSP-C27 rectangular Gram prerequisites and scalar double-angle identities — census `D, M25`; `dev/tauceti/dkps-upstream-contribution-census.md:177`.
- [PR #13331](https://github.com/TauCetiProject/TauCeti/pull/13331), MSS-B03: matrix entrywise/operator bound — census `D, M13`; `dev/tauceti/dkps-upstream-contribution-census.md:147`.
- [PR #13866](https://github.com/TauCetiProject/TauCeti/pull/13866), OI: approximation-number equivalence/isometric invariance — census `D, B`; `dev/tauceti/dkps-upstream-contribution-census.md:151`.

**Interpretation:** even an explicit donor statement is not the same as a line-by-line
proof comparison. The Courant–Fischer/Weyl family has a separate detailed audit at
`papers/dk_formalization_journal/COURANT_FISCHER_LINEAGE_AUDIT.md`. The PVM port
has layered Spectra ancestry, which must remain visible. Other items are not upgraded
to proof-descent status merely because the same subject appears in both repositories.

## Not yet demonstrated

1. The exact constant-level dependencies of the 29 source-result endpoints.
2. Which current TauCeti declarations (as opposed to modules) those endpoints use.
3. Historical first-development evidence for every imported declaration.
4. Which roadmap obligations have actually been **taught and proved** in TTS lectures.
5. The complete transitive TauCeti / Mathlib term-level frontier.

## Next proof-dependency extraction

Run a Lean metaprogram against the **pinned compiled environment** that exports
`{declaration, type_constants, proof_value_constants, module, defining_revision}`
for each target theorem and transitively referenced declaration. Preserve the distinction
between a theorem referenced in a *statement* and one referenced in its *proof*.
Correlate declaration identities with historical donor commits using the **existing**
DKPS census and archived donor history; do not infer mathematical authorship from imports.

## Evidence sources

- `dev/tauceti/dkps-upstream-contribution-census.md`
- `dev/tauceti/extraction-manifest.json`
- `dev/tauceti/spectra-provenance-map.md`
- `dev/tauceti/proof-lineage/2026-10-20-canonical-spectrum-migration.md`
- `papers/dk_formalization_journal/COURANT_FISCHER_LINEAGE_AUDIT.md`
- User-provided `pins.json` and `source-imports.json` from 2026-11-07
- Previously supplied roadmap obligations in `prerequisites/roadmap-audit/obligations.json`

