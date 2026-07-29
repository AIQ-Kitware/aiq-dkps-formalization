# Real operator-angle complexification source survey

Date: 2026-07-18

This implementation uses the following upstream or repository-local sources.

## Mathlib

- `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
  - `Submodule.HasOrthogonalProjection`
  - `Submodule.eq_starProjection_of_mem_orthogonal`
  - `Submodule.sub_starProjection_mem_orthogonal`
  - `Submodule.inner_right_of_mem_orthogonal`
  - `Submodule.mem_orthogonal`
- `Mathlib/Analysis/InnerProductSpace/ProdL2.lean`
  - inherited L2 product structure already used by `Core/Complexification.lean`

## Repository-local foundations

- `Core/Complexification.lean`
  - concrete real Hilbert-space complexification
  - `ofReal`, `conjugation`, `complexify`, and exact operator norm transport
- `Core/OperatorAngleComplex.lean`
  - axiom-clean complex sine/cosine/tangent operator calculus
- `ForMathlib/Analysis/InnerProductSpace/ProjectionGap.lean`
  - symmetric and directed projection-gap definitions
- `ForMathlib/Analysis/InnerProductSpace/ReducingSubspace.lean`
  - reducing-subspace interface used by the transport theorem

No new mathematical paper was required. The construction is the standard
coordinatewise complexification of a real Hilbert subspace.
