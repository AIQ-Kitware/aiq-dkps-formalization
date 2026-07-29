# Exact proved Part III extraction queue

Baseline: `7463ca25c64a46c48411a2769b47714889974a97`.

`DavisKahan/Experimental/PartIII.lean` contains 111 aliases.  The dependency
probe used for commit `a3db1d3` partitioned them into 78 genuinely open aliases
and 33 proved aliases whose current module placement still crosses an
Experimental boundary.

The 33 proved aliases are exactly the final contiguous block of that file,
starting with `bounded_sylvester_intervalExterior_genuineSpectrum`.  This file
records the exact queue rather than reconstructing it from memory.

## Batch A -- genuine-spectrum Sylvester and sine theory (6)

Source module:
`DavisKahan/Experimental/InfiniteDimensional/Sylvester/GenuineSpectrum.lean`.

- `bounded_sylvester_intervalExterior_genuineSpectrum`
- `bounded_sinTheta_genuineSpectrum`
- `bounded_sinTheta_genuineSpectrum_symmetric`
- `bounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`
- `bounded_sinTheta_uiNorm_genuineSpectrum`
- `bounded_sinTheta_uiNorm_genuineSpectrum_symmetric`

Recommended action: extract the declaration-level clean path onto the existing
production Spectra bridges and Sylvester modules.  Do not promote the current
coarse imports of legacy `Sylvester.Basic` or `Core.UnboundedSpectral`.

## Batch B -- genuine-spectrum double-angle theory (11)

Primary source module:
`DavisKahan/Experimental/InfiniteDimensional/DoubleAngleGenuine.lean`.

- `bounded_sinTwoTheta_genuineSpectrum`
- `bounded_sinTwoTheta_genuineSpectrum_sinAngle`
- `bounded_sinTwoTheta_uiNorm_genuineSpectrum`
- `bounded_reflectionDefect_offdiag`
- `bounded_reflectionDefect_le_cross`
- `bounded_sinTwoTheta_genuineSpectrum_defect`
- `bounded_cross_le_residual`
- `bounded_sinTwoTheta_genuineSpectrum_residual`
- `bounded_sinTwoAngle_gap_identification`
- `bounded_sinTwoTheta_genuineSpectrum_operator`
- `bounded_sinTwoTheta_genuineSpectrum_residual_operator`

`bounded_sinTwoAngle_gap_identification` already has a production-quality
counterpart in `DavisKahan/Interop/Spectra/ReflectionRestriction.lean`; prefer
repointing the source alias if the statements are definitionally or
propositionally identical rather than duplicating the proof.

Recommended destination: production `DoubleAngle/` modules split by reflection
identity, residual estimate, and operator/gauge endpoint.

## Batch C -- genuine-spectrum tangent prerequisites and theorem (3)

Source module:
`DavisKahan/Experimental/InfiniteDimensional/TanTheta/GenuineSpectrum.lean`.

- `bounded_tanTheta_genuineSpectrum`
- `bounded_formBounds_of_spectrum_Icc`
- `bounded_coercive_of_spectrum_exterior`

Recommended action: place the two spectral form/coercivity lemmas near spectral
restriction or bounded-from-spectrum infrastructure, then place the tangent
endpoint in `TanTheta/`.

## Batch D -- graph-subspace geometry (7)

Source module:
`DavisKahan/Experimental/InfiniteDimensional/GraphSubspace.lean`.

- `graph_subspace`
- `graph_projection_operator`
- `graph_projection_formula`
- `graph_gap_value`
- `graph_subspaceGap`
- `graph_tan_maximalAngle`
- `graph_contractive_iff_quarterAcute`

Recommended action: split definitions/projection formulas from metric and angle
corollaries.  The current file imports the old Experimental operator-angle
module; repoint onto the production angle calculus rather than promoting the
coarse import.

## Batch E -- bounded Riccati theory (4)

Source module:
`DavisKahan/Experimental/InfiniteDimensional/Riccati/Bounded.lean`.

- `bounded_riccati_graph_equivalence`
- `bounded_riccati_existence`
- `bounded_riccati_bound`
- `bounded_riccati_uniqueness`

Recommended action: extract in theorem order after Batch D.  The current file
is an aggregate over three narrower Experimental files; determine whether the
proofs can be moved independently without importing unrelated open endpoints.

## Batch F -- already-produced unbounded Riccati existence (1)

- `unbounded_riccati_existence`

A declaration with the same target name exists in the production module
`DavisKahan/Riccati/UnboundedExistence.lean`.  First compare statements and
repoint the source alias if they agree.  Do not preserve an Experimental route
merely because the alias currently names it.

## Batch G -- close-projection unitary equivalence (1)

Source module:
`DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean`.

- `close_projections_unitarily_equivalent`

The file contains an unrelated open continuation obligation.  Extract only the
unitary-equivalence theorem and its minimal helper closure.  Likely destination:
operator-angle, direct-rotation, or projection-geometry infrastructure rather
than a continuation module.

## Acceptance for every batch

- target declarations retain their statements;
- no source alias points into Experimental after extraction;
- no production module imports an Experimental module;
- `DavisKahan.All` and the generated aggregates remain stable;
- the five structural checks remain clean;
- the full sine-theta source audit remains unchanged;
- split PRs remain single-topic and preserve attribution.

## Math-ahead update

The full-Part-III repair batch restores candidate bodies for the formerly open
foundation and endpoint declarations while preserving their exact statements.
This does not retire the 33-item extraction queue.  Instead, after the restored
bodies compile, the queue should be recomputed: some mixed files may become
wholly production-ready, making a larger canonical promotion preferable to the
original declaration-by-declaration split.

See `topurge/dev/full-part-iii-admission-elimination-math-ahead-2026-07-20.md`
and the machine-checked signature manifest for the candidate scope.
