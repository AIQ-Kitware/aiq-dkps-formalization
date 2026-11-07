# Source and scope

The lecture works with finite real matrices. Its examples distinguish invariant
from reducing subspaces and derive the self-adjoint complement argument using
the adjoint identity. `facts.lean` applies the accepted Tau Ceti declarations
`Submodule.offDiagBlock_eq_zero_iff` and
`Submodule.starProjection_add_starProjection_orthogonal`. These are broader
inner-product-space statements with explicit projection hypotheses. No new
foundation theorem is introduced. The block criterion concerns preservation of
both parts, not fixing either part pointwise.

The historical and coordinate background is available in the linked learning
companion; the proof given here is the elementary vector argument.
