# Source and scope

Finite real matrices, entrywise/Frobenius inner product. The illustrative cost
is one half the squared Frobenius norm, with example X=[[1,2],[0,-1]] and
D=[[0,1],[2,0]]. The graph is F(X+tD)=3+2t+(5/2)t².

`facts.lean` applies Mathlib's `Matrix.trace_mul_comm` and
`Matrix.trace_conjTranspose_mul_self_eq_zero_iff`, simplifying conjugate
transpose to real transpose. The accepted facts certify cyclic trace equality
and the positive pairing test. They do not alone certify every constrained
gradient or stationarity construction; those restrictions are stated locally.

For skew matrices, -tr(GB)=tr(GᵀB); no sign convention is silently changed.
Testing with G itself is legitimate only when G is an allowed direction.
The learning companion supplies a matrix-calculus lesson and focused references.
