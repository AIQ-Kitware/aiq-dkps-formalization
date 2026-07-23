# Lane claims

Coordination ledger for parallel agents working this repo. Purpose: avoid the
duplicated-effort collisions that occurred on the Sylvester analytic lane
(2026-07-23), where two agents independently proved the same five theorems.

**Identity note (2026-07-23):** agents are identified by their *human*, not by
the model running them (models change mid-session). Rows previously labeled
`opus` were jon's agent; rows labeled `fable` were edward's agent. Edward's
agent has stopped; all its lanes are released. Jon's agent (currently running
the Fable 5 model) is the sole active agent and inherits/owns the active lanes
below.

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
| edward (stopped) | Sylvester/{FourierSemigroup,OrderedSemigroup,CompactIntegral,FiniteBlockReconstruction}.lean | whole Sylvester analytic lane (sorry-free) | 2026-07-23 | done |
| edward (stopped) | Sylvester/Basic.lean | norm_sylvester_le_of_orderedSeparation, compact_mem_of_separatedSylvester_solution | 2026-07-23 | done |
| edward (stopped) | InfiniteDimensional/GraphSubspace.lean | acuteAngularOperator, acuteAngularOperator_spec, acute_iff_exists_bounded_angularOperator | 2026-07-23 | done |
| jon | MathAhead/HiddenFoundations/PolarIsometryFinal.lean | polarIsometry_comp_adjoint_self | 2026-07-23 | done |
| jon | MathAhead/HiddenFoundations/{Section3Nonacute,PolarIsometryFinal}.lean | remaining 5 polar leaves | 2026-07-23 | blocked (missing infra) |
| jon | SinTheta/RCLikeSpectralBridge.lean (new), SinTheta/SpectralBridge.lean (Experimental) | phantom machinery + estimate repair — SpectralBridge now COMPILES | 2026-07-23 | done (3 RCLike leaf sorries) |
| jon | SinTheta/General.lean | make it elaborate — needs spectralSubspace/spectralProjection/sinAngleOperator defs + projectionDifference_ideal_intervalExterior + proof/timeout repair | 2026-07-23 | claimed (queued after RieszCircle) |
| jon | SinTheta/RestrictionCompat.lean | restrictedSpectrum_top_eq_realSpectrum_general, boundedRealSpectrum_eq_realSpectrum, mem_realResolventSet_ofBounded_iff | 2026-07-23 | done |
| jon | Frontier/Core.lean, Frontier/RieszCircle.lean | circle Riesz lane: remaining 5 RieszCircle sorries, per edward's plan in dev/circle-riesz-lane-status-2026-07-23.md (inherited — edward's agent stopped at 4/9) | 2026-07-23 | in progress |

## Spectral lane — claimed by jon (2026-07-23)

There is no separate "spectral agent" — the lane was unowned, so jon's agent
took it. Scope: make `SinTheta/General.lean` elaborate. The genuinely-phantom
`RCLikeSpectralBridge.*` machinery is now supplied and Experimental
SpectralBridge COMPILES; what remains is General's own missing
`spectralSubspace`/`spectralProjection`/`sinAngleOperator` definitions,
`projectionDifference_ideal_intervalExterior`, and proof/timeout repair.
General is outside the default build roots, so the tree stays green throughout.

## Parked (claim explicitly before starting)

- `Ideals/Rectangular.lean` (4): Schatten / Hilbert–Schmidt / trace-class rectangular
  families over RCLike — multi-session analytic campaign; Schauder absent from pinned Mathlib.
- Frontier Contour-blocked sections (Section3/8/9): park until the circle contour
  surface exists. That surface (Core.circleRieszProjection + RieszCircle.lean) is
  now jon's lane (inherited from edward, 2026-07-23); the RieszCircle signatures
  ARE the intended API — consumers should target them, not a new abstract
  contour framework.
- `MathAhead/.../KyFanBochner.lean`: broken on `main` since de30805 (11 errors, pre-existing).
- Polar-decomposition campaign (5 leaves): `adjoint_polarIsometry` needs the abs-adjoint
  closure relation `closure_range_abs_adjoint_eq_closure_range` + partial-adjoint formula;
  Section3Nonacute needs `positiveSupportInverse` + `source_compression_polar_formula` +
  `canonicalPolarFactor_reflection_relation` + the crossed-block structure of
  `IsPaperDirectRotation`. None exist in Mathlib/Spectra/repo yet — a real multi-session
  campaign. `polarIsometry_comp_adjoint_self` (final-projection identity) was the one leaf
  whose supporting infra was already present; now proved (5c7b13c).
