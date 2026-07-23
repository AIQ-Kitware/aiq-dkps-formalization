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
| fable | InfiniteDimensional/GraphSubspace.lean | acuteAngularOperator, acuteAngularOperator_spec, acute_iff_exists_bounded_angularOperator | 2026-07-23 | claimed |
| opus | MathAhead/HiddenFoundations/{Section3Nonacute,PolarIsometryFinal}.lean | polar-decomposition leaves (6 sorries) | 2026-07-23 | claimed |
| opus | SinTheta/RestrictionCompat.lean | restrictedSpectrum_top_eq_realSpectrum_general, boundedRealSpectrum_eq_realSpectrum, mem_realResolventSet_ofBounded_iff | 2026-07-23 | done |

## Hands-off (owned by the spectral agent — a third party)

`SinTheta/General.lean`, `SinTheta/SpectralBridge.lean`, and anything referencing
`RCLikeSpectralBridge.*`, `centered_sylvester_equation`, or
`projectionDifference_ideal_intervalExterior`. `SinTheta/General.lean` still fails
to elaborate on `main` (references `ExactSinTheta.IntervalExteriorGap`, defined
nowhere); it is outside the default build roots, so the tree stays green.

## Parked (claim explicitly before starting)

- `Ideals/Rectangular.lean` (4): Schatten / Hilbert–Schmidt / trace-class rectangular
  families over RCLike — multi-session analytic campaign; Schauder absent from pinned Mathlib.
- Frontier Contour-blocked sections (Section3/8/9, RieszCircle): park until a Contour
  API exists. Designing that API is itself a claimable task — post intended signatures first.
- `MathAhead/.../KyFanBochner.lean`: broken on `main` since de30805 (11 errors, pre-existing).
