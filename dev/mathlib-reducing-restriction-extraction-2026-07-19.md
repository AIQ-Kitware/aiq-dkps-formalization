# Upstream extraction plan: restrictions to reducing subspaces

Date: 2026-07-19

## Candidate theorem

A densely defined closed operator on a Hilbert space restricts to a closed
operator on any orthogonally complemented invariant subspace whose projection
preserves the domain. If the operator is self-adjoint and the orthogonal
complement is also invariant, the restriction is self-adjoint.

## Recommended upstream decomposition

The reusable layer should not mention Davis--Kahan, spectral measures, or
complexification.

1. `InvariantSubspace` for an unbounded linear operator with explicit domain.
2. `ReducesSubspace`, recording domain preservation by the two projections and
   invariance of both summands.
3. The restricted domain `dom A intersect U` as a submodule of `U`.
4. The restricted operator and its closedness.
5. Density of the restricted domain by projection of an ambient approximating
   sequence.
6. Inclusion-domain and inclusion-intertwining lemmas.
7. Characterization of the restricted adjoint domain.
8. Symmetry and self-adjointness of the restriction.
9. Compatibility with orthogonal complementation.
10. Compatibility with bounded operator restriction/compression.

## Naming guidance

Possible Mathlib-style names:

- `UnboundedOperator.InvariantSubspace`
- `UnboundedOperator.Reduces`
- `UnboundedOperator.restrict`
- `UnboundedOperator.restrict_domain`
- `UnboundedOperator.restrict_closed`
- `UnboundedOperator.restrict_isSelfAdjoint`
- `UnboundedOperator.restrict_inclusion_intertwines`

The current repository type is project-local, so the first upstream step is
likely a theorem-quality local module followed by a proposal against whichever
closed-operator representation Mathlib accepts.

## Hypothesis minimization

For closedness and density of the restriction, only the selected projection
must preserve the domain and the selected summand must be invariant.
Self-adjointness uses the complementary domain and invariance laws. The current
single `ReducesSubspace` record is convenient, but a future upstream API may
split these layers so weaker results do not ask for unnecessary facts.

## Proof architecture

Avoid proving self-adjointness by resolvent surjectivity; that introduces a
complex scalar dependency and is awkward over real Hilbert spaces. The direct
adjoint-domain proof is scalar-generic:

- extend the restricted adjoint relation to the ambient domain using the
  orthogonal decomposition;
- use ambient self-adjointness;
- restrict the resulting action back to the selected summand.

## Additional compatibility results worth upstreaming

- restriction to `U-perp` from the same reduction witness;
- direct-sum equivalence between `A` and `A|U directSum A|U-perp`;
- equality of graphs under the direct-sum equivalence;
- spectral union for the complex self-adjoint case;
- bounded functional calculus commutes with restriction;
- restriction of a bounded operator agrees with the bounded compression when
  the subspace reduces it.

## Repository boundary

The generic restriction module belongs below the Spectra bridge. The following
must remain outside the upstream core:

- construction of spectral projections;
- conjugation descent of a real spectral PVM;
- Davis--Kahan residual and gap records;
- ideal-gauge estimates.
