# Proposed TauCetiRoadmap Meta issue

## Title

`[Meta]: Guidance on integrating an existing spectral-subspace perturbation development`

## Body

I have an existing, substantial Lean development of spectral-subspace
perturbation theory and would like guidance on how to structure it for Tau Ceti
before opening an intention or a roadmap PR.

### Mathematical highlights

- A proof-complete finite-dimensional Davis--Kahan Part III specialization,
  including sharp Sylvester bounds, generalized and ordinary `sin Theta`,
  Ritz-residual `tan Theta`, `sin 2 Theta`, operator-norm `tan 2 Theta`, and
  projector-difference bounds.
- Source-faithful real and complex Section 6 `sin Theta` theory for closed,
  possibly unbounded, self-adjoint operators, including the universal-norm
  Theorem 6.1, the pairwise-gap square-norm Theorem 6.2, and common-domain
  and graph-core formulations.
- Rectangular approximation numbers and symmetric operator ideals for maps
  between distinct Hilbert spaces, with independent domain and codomain
  universes where the mathematics permits it.
- Hilbert--Schmidt theory relating approximation singular values, basis-column
  energy, tensor models, and finite-dimensional Frobenius norms.
- Bounded and closed Sylvester equations under ordered, interval/exterior, and
  arbitrary pairwise spectral separation.
- Directed operator-angle calculus, real/complex compatibility, sharpness
  examples, and finite-multiplicity equality models.

The work is human-directed and largely implemented by AI agents.  It also uses
an attributed snapshot of the Spectra project for general complex spectral and
unbounded-operator infrastructure.  The current repository separates
admission-free production mathematics from an explicit nondefault Experimental
surface.

I do not want to claim an invented roadmap area or preserve the accidental
organization of the existing repository.  I would appreciate guidance on:

1. Should this become one new roadmap, tentatively **Spectral subspace
   perturbation, operator angles, and Sylvester equations**?
2. Should some pieces instead extend existing roadmaps, particularly
   `OneParameterSemigroups`, or be split into multiple roadmap areas?
3. Which parts are appropriately general Tau Ceti infrastructure, and which
   should remain a Davis--Kahan source-facing layer?
4. Should Spectra-derived results be integrated into canonical `TauCeti/...`
   topic modules with detailed provenance, rather than retained as a permanent
   vendor-shaped subtree?
5. Would maintainers prefer one comprehensive staged roadmap or a small initial
   roadmap covering the reusable foundation before the paper-level theorem
   package?

I can prepare a roadmap PR with intrinsic mathematical milestones, provisional
Lean signatures, a source-correspondence matrix, and a declaration-level
provenance appendix after receiving direction on scope and placement.

Existing development: `<repository URL>`

Primary source: C. Davis and W. M. Kahan, *The Rotation of Eigenvectors by a
Perturbation. III*, SIAM Journal on Numerical Analysis (1970).

Related formal source: Spectra, upstream revision
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
