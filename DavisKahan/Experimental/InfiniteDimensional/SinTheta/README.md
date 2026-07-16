# Canonical and alternative `sin Θ` developments

This directory is organized around the full Davis--Kahan 1970 single-angle
result. The canonical target is **not** the bounded theorem. It is the
source-faithful, domain-aware result for self-adjoint closed operators that may
be unbounded, with a bounded residual block and an applicable unitarily
invariant ideal gauge.

The canonical dependency chain is:

1. `Core/Unbounded.lean`: densely defined closed operators and full-domain
   embeddings of bounded operators;
2. `Core/UnboundedSpectral.lean`: self-adjoint spectral projections,
   semibounds, cutoffs, truncations, and domain-aware Sylvester equations;
3. `Sylvester/Unbounded.lean`: Davis--Kahan Section 5, including the genuinely
   two-unbounded ordered theorem and the interval/exterior theorem;
4. `FrameFactorization.lean`: the lower-frame polar factor needed by the
   generalized theorem;
5. `Unbounded.lean`: the residual block identity and transport from the
   Sylvester estimate to the directed sine;
6. `Canonical.lean`: bundled, source-facing generalized and isometric theorem
   statements.

`Canonical.lean` owns the theorem shape that should eventually move into the
supported source tree. Its generalized theorem comes first. The isometric
result is derived by setting the lower frame bound to one.

## Status of bounded and finite proofs

`Bounded.lean` is useful and should remain. It supplies an independent proof
route with weaker infrastructure requirements and is valuable for regression,
finite-rank transfer, and comparison with the general proof. It is not the
canonical completion boundary.

Likewise, the finite-dimensional results are genuine theorems and should not be
deleted. As the source-facing API becomes general, independent bounded and
finite proofs should be exported under `DavisKahan/Alternative` or under
explicitly qualified specialization names. Multiple proof paths are desirable
when their logical strength and scope are visible in the module structure.

## Gap configurations

The canonical theorem accepts `UnboundedSylvesterGap`, whose constructors
cover:

- interval/exterior separation;
- a lower-semibounded left block above an upper-semibounded right block;
- the reversed ordered orientation.

The ordered constructors permit both diagonal blocks to be genuinely
unbounded. The interval/exterior branch follows the source's bounded-spectral-
block relaxation. These cases must not be collapsed into point-spectrum
predicates.

## Norm scope

The source-facing norm parameter is `UnitaryInvariantIdealFamily`, currently an
alias for the stronger finite-Ky-Fan-dominant rectangular family required by
the cutoff proof. Operator norm is one instance. Hilbert--Schmidt, trace,
Schatten, Ky Fan, and compact-operator instances are separate obligations.
Proving only operator norm does not complete the canonical theorem.

## Soundness boundaries

The unbounded theorem must retain all of the following information:

- explicit operator domains;
- domain transport for the cross block;
- equality of the Sylvester equation on the source domain;
- self-adjointness of both diagonal blocks;
- source-faithful spectral separation or semibounds;
- bounded extension and ideal membership of the residual;
- a complete orthogonal exact-space decomposition before calling the block the
  full directed sine.

Do not replace these with a bounded operator plus comments about a future
extension. A bounded theorem should be obtained from the general API by the
full-domain constructor, or retained as a clearly named alternative proof.

## Current compiler-first frontier

The high-level theorem assembly now follows the intended chain. The remaining
substantive frontier is lower in the graph:

- closed graph for the full-domain bounded constructor;
- adjoint and spectral calculus for the closed-operator model;
- cutoff-domain inclusion, cutoff commutation, and strong convergence;
- the two ordered Ky Fan cutoff estimates;
- the interval/exterior unbounded Sylvester theorem;
- the unbounded residual block identity;
- construction of `LowerFramePolarData` from the positive continuous
  functional calculus for the Gram operator;
- concrete unitarily invariant ideal instances.

The downstream lower-frame geometry is now concentrated behind that one
proof-carrying existence seam. Closed range and Gram coercivity are proved
directly; frame normalization, the factor `ε`, range preservation, the
isometric specialization, and the exact directed-sine gauge identity are
derived from the selected polar package.

Compiler repairs should strengthen these seams rather than retreating to a
bounded headline theorem.
