# Source and convention

Classroom scope: finite real equal-dimensional subspaces, increasing angles
obtained by inverse cosine of decreasing overlap singular values. The two-slice
example is in four dimensions: the first slice uses e1,e3 and the second e2,e4.

The accepted Tau Ceti module `Projection/PrincipalAngle` defines
`Submodule.principalCosines` through the cross-projection singular values.
`facts.lean` applies `principalCosines_nonneg`, `principalCosines_le_one`, and
`principalCosines_comm`. The finite-support data is padded by zeros; dimension
information determines the classroom list, including geometric right angles.

We deliberately do not identify the increasing classroom list with the
library's `principalAngles`: the latter uses a decreasing directed-sine
convention. Unequal-dimensional directed sine lists are not asserted symmetric.
The external learning sources explain the geometric definition and computation.
