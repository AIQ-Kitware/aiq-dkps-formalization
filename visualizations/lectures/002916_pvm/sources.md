# Mathematical sources and formal correspondence

This lecture explains the spectral-measure viewpoint rather than proving the
spectral theorem. The finite matrix model, multiplication operator, and diagonal
unbounded example are elementary illustrations. The three companion examples
apply accepted Tau Ceti declarations; they do not formalize every assertion in
the narration.

## Mathematical context

Kato, *Perturbation Theory for Linear Operators* (1966), develops spectral
projections and their role in perturbation theory. Davis and Kahan (1970),
*The rotation of eigenvectors by a perturbation. III*, is the downstream
motivation for selecting reducing spectral subspaces. The Riesz/von Neumann
reference in the narration places the subject in its historical tradition;
it assigns no exclusive priority for the spectral theorem or PVM terminology.
See the repository's distilled literature and journal bibliography for these
sources.

## Accepted API

`TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic` defines
`TauCeti.ProjValMeasure X H`, for a measurable space X and a complete complex
inner product space H. Its projection takes an explicit measurability proof.
The lecture specializes X to the real line with its Borel measurable structure.

| Symbolic fact | Accepted declaration / companion |
| --- | --- |
| E(B) E(C) = E(B intersection C) | `ProjValMeasure.proj_inter`; first example in `facts.lean` |
| E(complement B) = I - E(B) | `ProjValMeasure.proj_compl`; second example |
| squared norm of E(B)x = mu_x(B) | `ProjValMeasure.norm_sq_proj_apply`; third example |
| Strong countable additivity for disjoint B_j | `tendsto_sum_proj_of_pairwise_disjoint` in the same module |
| Scalar measure and total mass | `diag`, `diag_finite`, `diag_univ_toReal` |

The scalar measure uses extended nonnegative reals in Lean. `toReal` is valid
here because `diag_finite` ensures finiteness. The stored `inner_proj` identity
relates this measure to the projection's quadratic form.

The accepted module records adaptation of Adam Bornemann's Spectra work
(commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`), followed by Tau Ceti
integration. This is provenance of the formal implementation, distinct from
LLM authorship of the present lecture.

## Construction and unbounded scope

Accepted `ProjValMeasure/Integral.lean` develops abstract spectral integration.
The operator-to-PVM construction is a separate layer. In this repository,
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean` contains
`boundedPVM` and the bridge from the bounded self-adjoint functional calculus.
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean`
and `SpectralMeasure.lean` develop the unbounded construction and spectral
cutoffs. Those donor constructions must not be described as already accepted
Tau Ceti APIs merely because the abstract PVM laws have landed.

For an unbounded self-adjoint A with its spectral measure E:

- The integral defining A is defined on vectors whose scalar spectral measure
  has finite second moment; its squared output norm is that second moment.
- Every E(B) is bounded and preserves the domain. A E(B)x = E(B)Ax is asserted
  for x in the domain.
- If B is contained in [-M,M], M nonnegative, the entire range of E(B) lies
  in the domain, and the cutoff operator has norm at most M.

These are stated with their domain restrictions in the lecture; the three
small Lean applications should not be read as compiler certificates of this
entire analytic construction.

## Evidence-bearing illustrations

`dkvis/learning/pvm/model.py` uses an orthogonal change of basis and eigenvalues
1, 2, 2, 4. Tests verify projection laws, multiplicity, square functional
calculus, and vector energy versus rank. The continuous example is multiplication
by t on L2([0,1]); singleton level sets have Lebesgue measure zero, so there
are no nonzero eigenvectors. The unbounded example multiplies the nth
coordinate by n on l2, with n starting at one. Its bounded coordinate cutoffs
converge strongly, while their complements have operator norm one.

All visual assets are code-generated vector graphics. No external images are
required or stored for this lecture.
