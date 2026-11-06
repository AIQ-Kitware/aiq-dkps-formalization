# Sources, scope, and formal correspondence

This is a finite-dimensional symmetric/Hermitian Rayleigh–Ritz lecture. It
explains the role of a trial subspace before introducing residual estimates.
The three Lean companions apply accepted bounded Hilbert-space identities;
they are not certificates of every historical, numerical, or spectral claim
in the narration. No new foundation is introduced.

## Context and mathematical sources

- Rayleigh, *The Theory of Sound*, vol. 1 (1877), and Ritz, *Über eine neue
  Methode zur Lösung gewisser Variationsprobleme der mathematischen Physik*,
  Journal für die reine und angewandte Mathematik (1909), supply the brief
  historical motivation. These are separate contributions, not a joint paper.
  The repository's historical lectures and source records discuss them.
- Parlett, *The Symmetric Eigenvalue Problem*, SIAM edition (1998), Chapter 11,
  is the Rayleigh–Ritz reference cited by the accepted Tau Ceti module.
- Davis and Kahan, *The rotation of eigenvectors by a perturbation. III* (1970),
  supplies the downstream residual-and-separation application. The journal
  manuscript's general trial model is not assumed to be the Ritz compression.
- The quotient and nested extremal estimates follow by optimizing the same
  Rayleigh quotient over smaller or larger sets of unit vectors. The lecture
  does not claim convergence of arbitrary trial-space sequences.

## Accepted Tau Ceti APIs

Inspected and compiled against pinned Tau Ceti
`95f09254dec44b756e90d78f20f93dc4d3572783`:

`TauCeti/Analysis/InnerProductSpace/Compression.lean`

`TauCeti/Analysis/InnerProductSpace/RayleighRitz.lean`

| Lecture identity | Accepted declaration |
| --- | --- |
| B = Q* A Q | `ContinuousLinearMap.compression_def` |
| Q* R = 0 for an isometric Q | `ContinuousLinearMap.adjoint_comp_sylvester_compression` |
| A Q - Q M = R + Q(B-M) | `ContinuousLinearMap.sylvester_eq_sylvester_compression_add` |
| R is the perpendicular output component | `ContinuousLinearMap.sylvester_compression` |
| Fixed-frame Frobenius Pythagoras | `TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_sylvester_eq_sq_frobenius_sylvester_compression_add` |

The first three are the examples displayed on the Lean cards. In code, X is
Q, `A.compression X` is B, and `A.sylvester M X` is A Q - Q M. The real
bounded Hilbert-space companion includes completeness and an isometry
hypothesis. Compression and the algebraic splitting themselves need neither
symmetry nor isometry; orthogonality uses isometry. The library results are
also available for real/complex scalar fields. The lecture uses symmetry for
the small eigenproblem, variational interpretation, and eigenvalue inclusion.

The accepted module credits the Tau Ceti contributors, Jon Crall, GPT 5.6 High,
and OpenAI GPT-6. Its finite linear-map orthogonality theorem explicitly
records the corresponding DKPS `Residual/Ritz.lean` statement and uses the
accepted continuous-map proof. This proof ancestry is separate from authorship
of the present lecture. The companion imports accepted Tau Ceti directly.

## Mathematical qualifications

- Trial describes the role of a chosen subspace; it implies neither invariance
  nor closeness to a specified spectral target.
- Compression projects the output back into the trial space. It agrees with
  restriction as an endomorphism of that space when the space is invariant.
- For fixed orthonormal Q, the compression uniquely minimizes the Frobenius
  residual over every small model M. This does not optimize the subspace Q.
- An orthonormal change Q to QZ preserves the trial space. It conjugates the
  compression to Z*BZ and transforms the residual to RZ. Lifted Ritz
  eigenspaces and Ritz values are unchanged; bases inside repeated eigenspaces
  need not be unique.
- For unit u and Hermitian A, min_j |lambda_j - theta| <= ||Au-theta u||
  follows from the exact spectral expansion. This certifies proximity to some
  spectral value, not identification of a wanted spectral space. Angle bounds
  additionally require separation hypotheses.
- The unbounded connection is a scope reminder, not an extension of the matrix
  proof: domain inclusion, self-adjoint trial model, and bounded residual
  hypotheses must be supplied in the general source-facing theorem.
- For a full-column-rank nonorthogonal basis V, the Galerkin eigenproblem is
  V*AV y = theta V*V y. Stable orthogonalization returns to the Q formulation.

## Numerical illustrations

`model.py` supplies the recurring matrix with rows (2,1,1), (1,2,-1),
(1,-1,5). Its first-two-coordinate trial plane is reused throughout the
construction. For Q = (e1,e2), its compression has
Ritz values 1 and 3, with residual norms sqrt(2) and 0. The trial plane is not
invariant. Tests verify these claims, Galerkin orthogonality, the Frobenius
splitting, real/complex trial-basis invariance, and eigenvalue inclusion.
The quotient curve is 2 + sin(2t) on unit trial coordinates (cos t, sin t).
Nested coordinate spaces give smallest Ritz values 2, 1, and 3 - sqrt(6).
Tests verify the input/output decomposition, cancellation and reinforcement
of residual columns, quotient values, and nested extremal bounds.

`visuals.py` maps the 3D trial plane to a perspective drawing. It is a viewing
projection, not a mathematical isometry: lengths in the picture are
foreshortened. The coordinate-circle scene explicitly distinguishes that view
from the actual norm equality for Q. The model-error triangle is a schematic
of orthogonal components for one input; its side lengths are not numerical
labels for the matrix example.

The drawings are generated vector graphics and require no downloaded images.
