# Lane claims

Coordination ledger for parallel agents working this repo. Purpose: avoid the
duplicated-effort collisions that occurred on the Sylvester analytic lane
(2026-07-23), where two agents independently proved the same five theorems.

## Rules

- **Claim before the first edit.** Add/refresh your row below, commit it, then work.
- A claim covers the **listed declarations**, not the whole file. Two agents may
  work different declarations in one file if both are listed.
- **Release explicitly** when done (set status `done` or remove the row).
- **Unlisted = unclaimed.** If you want something not listed, add a row first.
- If two claims would overlap, the earlier-committed row wins; the other agent
  picks something else.

## Format

`agent | file(s) | declarations | date | status`

## Claims

| agent | file(s) | declarations | date | status |
|-------|---------|-------------|------|--------|
| fable | Sylvester/{FourierSemigroup,OrderedSemigroup,CompactIntegral,FiniteBlockReconstruction}.lean | whole Sylvester analytic lane (now sorry-free) | 2026-07-23 | owned |
| fable | Sylvester/Basic.lean | leaves at lines 117, 236 | 2026-07-23 | claimed |
| fable | InfiniteDimensional/GraphSubspace.lean | acuteAngularOperator, acuteAngularOperator_spec, acute_iff_exists_bounded_angularOperator | 2026-07-23 | done |
| opus | MathAhead/HiddenFoundations/PolarIsometryFinal.lean | polarIsometry_comp_adjoint_self | 2026-07-23 | done |
| opus | MathAhead/HiddenFoundations/{Section3Nonacute,PolarIsometryFinal}.lean | remaining 5 polar leaves | 2026-07-23 | blocked (missing infra) |
| opus | SinTheta/General.lean, SinTheta/SpectralBridge.lean (Experimental) | RCLikeSpectralBridge.* spectral-mapping lemmas, centered_sylvester_equation, boundedInverseDataOfIsUnit, projectionDifference_ideal_intervalExterior; make General.lean elaborate | 2026-07-23 | claimed |
| opus | SinTheta/RestrictionCompat.lean | restrictedSpectrum_top_eq_realSpectrum_general, boundedRealSpectrum_eq_realSpectrum, mem_realResolventSet_ofBounded_iff | 2026-07-23 | done |

## Spectral lane — claimed by opus (2026-07-23)

There is no separate "spectral agent" — the lane was unowned, so opus took it.
Scope: make `SinTheta/General.lean` elaborate by supplying the genuinely-phantom
machinery its dependency `Experimental/.../SinTheta/SpectralBridge.lean` uses but
which is defined nowhere: the `RCLikeSpectralBridge.*` spectral-mapping lemmas
(spectrum of `A - r·I`; operator-norm from spectrum-in-closedBall; inverse
spectrum; normal-operator norm; `inverse_isNormal`), `centered_sylvester_equation`,
`boundedInverseDataOfIsUnit`, and `projectionDifference_ideal_intervalExterior`.
`IntervalExteriorGap` and `sylvester_mem_and_gauge_le_of_intervalExteriorGap` DO
exist (Experimental SpectralBridge) — General just can't import them until that
file compiles. General is outside the default build roots, so the tree stays green
throughout. fable: this is mine now; ask before touching SinTheta/*.

## Parked (claim explicitly before starting)

- `Ideals/Rectangular.lean` (4): Schatten / Hilbert–Schmidt / trace-class rectangular
  families over RCLike — multi-session analytic campaign; Schauder absent from pinned Mathlib.
- Frontier Contour-blocked sections (Section3/8/9, RieszCircle): park until a Contour
  API exists. Designing that API is itself a claimable task — post intended signatures first.
- `MathAhead/.../KyFanBochner.lean`: broken on `main` since de30805 (11 errors, pre-existing).
- Polar-decomposition campaign (5 leaves): `adjoint_polarIsometry` needs the abs-adjoint
  closure relation `closure_range_abs_adjoint_eq_closure_range` + partial-adjoint formula;
  Section3Nonacute needs `positiveSupportInverse` + `source_compression_polar_formula` +
  `canonicalPolarFactor_reflection_relation` + the crossed-block structure of
  `IsPaperDirectRotation`. None exist in Mathlib/Spectra/repo yet — a real multi-session
  campaign. `polarIsometry_comp_adjoint_self` (final-projection identity) was the one leaf
  whose supporting infra was already present; now proved (5c7b13c).
