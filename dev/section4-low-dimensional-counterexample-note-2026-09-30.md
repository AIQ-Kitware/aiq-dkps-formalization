# Low-dimensional Proposition 4.4 note (2026-09-30)

This overlay formalizes the clean two-dimensional part of the low-dimensional
counterexample discussion around Proposition 4.4.

## What is formalized

New Lean module:

- `DavisKahan/Sources/DavisKahan1970/Section4LowDimensional.lean`

It proves, in the explicit real plane model from Section 4 Example 4.1, that on
`0 ≤ θ ≤ π / 3` the direct-rotation displacement is no larger than the
reflecting competitor in **every** square unitarily invariant seminorm.

Concretely, the proof packages the Example 4.1 singular-value computations

- direct rotation: `(2 sin (θ/2), 2 sin (θ/2))`
- reflection: `(2, 0)`

into a Ky Fan domination argument and then applies
`kyFanSum_le_iff_forall_seminorm`.

The resulting surface theorem is

- `TauCeti.DavisKahan1970.Section4LowDimensional.example4_1_directRotation_uiNorm_minimal_of_le_pi_div_three`

which states that, among the two orthogonal plane competitors in the model
(direct rotation or reflection), the direct rotation is minimal for every
square unitarily invariant seminorm whenever `θ ≤ π / 3`.

## Why this matters

This formalizes the "no two-dimensional real counterexample" statement in the
standard Section 4.1 coordinates.  Since a real two-dimensional orthogonal
competitor carrying one line to another is necessarily one of those two cases,
this is the core low-dimensional obstruction for ambient dimension `2`.

## What is not yet formalized here

This overlay does **not** complete the ambient-dimension-`3` classification.
The remaining gap is the source-facing reduction from an arbitrary `3`-D
competitor to the standard line/plane coordinate models.  The mathematics is
straightforward (orientation-preserving competitors reduce to a rotation case;
orientation-reversing competitors reduce to a reflection-rotation case), but I
left that broader reduction out of this patch in favor of a tight, reliable,
small Lean increment.
