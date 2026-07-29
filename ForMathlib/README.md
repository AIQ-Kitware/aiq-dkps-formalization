# ForMathlib — staging library for Mathlib contributions

Paper-agnostic results from `Acharyya2024`/`Acharyya2025`, restated in Mathlib
idiom and generality, staged for upstream PRs.  The ranked candidate list and
per-candidate dossiers live in `planning/mathlib-candidates.md`.

## Pattern

- **One file per proposed Mathlib destination path.**  For example,
  `ForMathlib/Analysis/InnerProductSpace/GramMatrix.lean` stages additions to
  `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.
- **Mathlib-only, minimal imports.**  No file here may import the paper
  libraries; the paper libraries import from here (and keep only their
  paper-facing specializations).  This guarantees each staged file is
  self-contained and that the generalized statement actually serves the
  application.
- **Everything lives under the `ForMathlib` namespace** so that a future
  Mathlib bump that upstreams these results cannot create name clashes.
  Within it, declarations use their intended final namespaces (e.g.
  `ForMathlib.Matrix.…`).
- **Maximal generality.**  Statements are over `RCLike 𝕜` (not just `ℝ`)
  where the proofs allow it.

## At PR time

1. Copy the staged declarations into the destination Mathlib file (or a new
   file), dropping the `ForMathlib` namespace wrapper.
2. Convert the header to Mathlib's module system (`module`,
   `public import`, `@[expose] public section`) and minimal-import style.
3. Add the Mathlib copyright header.  Per Mathlib's contribution policy,
   substantial AI assistance must be disclosed in the PR description and a
   human author must understand and vouch for every line.
4. After the PR lands, delete the staged file here and bump the Mathlib pin.

## Singular-value and frame layer

`RectangularSingularValues.lean`, `SingularSystem.lean`, `FiniteFrame.lean`, and
`CenteredScatter.lean` are fully proved and imported by `ForMathlib.lean`; the raw-response
Quench spectral track consumes the first, third, and fourth through
`DkpsQuench2026/Spectral/GramSpectrum.lean`.  The
design and external proof-source map are in
`docs/planning/rectangular-singular-values-and-frames.md` and
`dev/external-lean-references.md`. Licensed proof snapshots are isolated under
`vendor/lean/` and are not build dependencies; they were used as cross-checks only, and no
vendored code was copied into the build.

## Inventory

**Current contents (2026-07-29): four modules.**
`LinearAlgebra/Matrix/{PosDef,RankFactorization}.lean` and
`Topology/{ApproxMinimizer,Berge}.lean`.  The table below is the *destination*
table and is deliberately larger than the tree: most of its rows have already
been migrated into `ForTauCeti` and are listed here for the Mathlib destination
they were staged against, not as files on disk.

The last such migration was lane **Y3(b2)** on 2026-07-29, which moved the
closed 8-module `Analysis/InnerProductSpace` component —
`{ProjectionBlocks, ProjectionGap, QuadraticFormBounds, ReducingSubspace,
SylvesterBound, SylvesterOperator, CoerciveUnit}.lean` and
`SpectralOrder/Complex.lean` — into `ForTauCeti/Analysis/InnerProductSpace/`,
taking `ForMathlib` from 12 modules to 4.  The four that remain are the
genuinely Mathlib-shaped remainder: none of them is an inner-product-space
module, and three of them (`RankFactorization`, `PosDef`, `Berge`) are pinned
by comparator conformance statements.


| Staged file | Destination | Candidate (mathlib-candidates.md) |
| --- | --- | --- |
| `Analysis/InnerProductSpace/RectangularSingularValues.lean` | proposed additions near `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` | nonzero eigenspace equivalence for `A†A`/`AA†`, multiplicities, and rectangular adjoint invariance |
| `Analysis/InnerProductSpace/SingularSystem.lean` | proposed new singular-system/SVD file | intrinsic right/left singular vectors, orthonormality, and rank-one reconstruction |
| `Analysis/InnerProductSpace/FiniteFrame.lean` | proposed new finite-frame file | analysis/synthesis/frame/Gram operators and frame-bound equivalences |
| `Analysis/InnerProductSpace/CenteredScatter.lean` | proposed finite-family mean/scatter file | exact add-one centered-scatter identity and Löwner monotonicity |
| `Analysis/InnerProductSpace/CourantFischer.lean` | new `Mathlib/Analysis/InnerProductSpace/CourantFischer.lean` | #3a Courant–Fischer (both directions) + Weyl's eigenvalue perturbation inequality, `RCLike` |
| `Analysis/InnerProductSpace/DavisKahan.lean` | new `Mathlib/Analysis/InnerProductSpace/DavisKahan.lean` | Davis–Kahan cross-block (squared sin-Θ) bound `∑ ‖⟪uᵢ,v̂ⱼ⟫‖² ≤ nε²/gap²` + rank-`d`/floor corollary `≤ 4nε²/α²` (`RCLike`); canonical **projector form** `‖P̂−P‖_F² = 2·Σcross ≤ 2nε²/gap²` (ℝ) |
| `Analysis/InnerProductSpace/IntertwiningUnitary.lean` | new `Mathlib/Analysis/InnerProductSpace/IntertwiningUnitary.lean` | Davis §2 canonical intertwining unitary of two complete orthogonal projection families: `spectralProjection` API, `OrthoProjFamily`, `intertwiningUnitary` (`U Pⱼ = P'ⱼ U`), block polar factors `range Pⱼ ≃ₗᵢ range P'ⱼ`, rotation angles (`RCLike`) |
| `Analysis/InnerProductSpace/GramMatrix.lean` | `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean` | #1 Gram rigidity (equal Grams ⇒ linear isometry equiv), generalized to `RCLike` and stated via `Matrix.gram` |
| `Analysis/InnerProductSpace/PartialIsometry.lean` | new `Mathlib/Analysis/InnerProductSpace/PartialIsometry.lean` | `IsPartialIsometry` (`u * star u * u = u`) in any star-monoid + operator characterization (isometric on `(ker u)ᗮ`) and constructor (`RCLike`) |
| `Analysis/InnerProductSpace/PolarDecomposition.lean` | new `Mathlib/Analysis/InnerProductSpace/PolarDecomposition.lean` | operator polar decomposition `A = U\|A\|`: modulus `abs A = √(A⋆A)`, partial-isometry polar factor, invertible/unitary case, ℂ headline `A = U ∘L CFC.abs A` (`RCLike` + ℂ bridge) |
| `Analysis/InnerProductSpace/PositiveSqrt.lean` | additions to `Mathlib/Analysis/InnerProductSpace/Positive.lean` | spectral positive square root of a positive operator: existence, uniqueness, `ker`/`range`, pointwise root, `IsUnit` transfer (`RCLike`) |
| `Analysis/InnerProductSpace/RotationBound.lean` | new `Mathlib/Analysis/InnerProductSpace/RotationBound.lean` | Davis's sharper total-rotation estimate (Thm 3.2): `γ'²∑sin²θᵢ + ∑(λᵢ−λ'ᵢ)² ≤ ‖H‖²_F`, angle identification for the canonical unitary, and the corollary `γ'²∑sin²θᵢ ≤ 2‖𝒞⊥H‖²_F` (`RCLike`) |
| `Analysis/InnerProductSpace/NearIsometry.lean` | new `Mathlib/Analysis/InnerProductSpace/NearIsometry.lean` | #6 quantitative polar factor (near-isometry ⇒ isometry within `2δ`), bundled `≃ₗᵢ` + CLM op-norm corollary |
| `Analysis/InnerProductSpace/Basic.lean` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` | `inner_linearCombination_linearCombination` — inner product of two `Finsupp.linearCombination`s expanded over `⟪v i, v j⟫` (general; no orthonormality, no Gram matrix; sits by `Finsupp.sum_inner`) |
| `Analysis/InnerProductSpace/Spectrum.lean` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` | #3b Davis–Kahan cross-term identity, generalized to `RCLike` |
| `Analysis/Matrix/EntrywiseOpNorm.lean` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` + `Mathlib/Analysis/Matrix/Normed.lean` | norm comparisons: `ℓ¹ ≤ √card·ℓ²` (`RCLike`) and entrywise → `ℓ²`-operator-norm `‖toEuclideanLin A x‖ ≤ nε‖x‖` (ℝ) |
| `Analysis/Matrix/Spectrum.lean` | `Mathlib/Analysis/Matrix/Spectrum.lean` | PSD low-rank sorted-eigenvalue tail `eigenvalues₀ i = 0` for `i ≥ rank` (`RCLike`) |
| `LinearAlgebra/Matrix/PosDef.lean` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean` | #5 rank-constrained PSD factorization `PosSemidef ∧ rank ≤ d ↔ ∃ A : Matrix (Fin d) n, B = Aᴴ * A` (`RCLike`) |
| `MeasureTheory/CompactExists.lean` | `Mathlib/MeasureTheory/Constructions/BorelSpace/` | measurability of a compactly-quantified existential `{ω | ∃ y ∈ S, F y ω ≤ c}` for Carathéodory `F` (no measurable selection) |
| `MeasureTheory/Function/ConvergenceInMeasure.lean` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` | #7 `TendstoInMeasure` from a vanishing rate (general filter, `EDist`, measurability-free) |
| `MeasureTheory/Measure/Typeclasses/Probability.lean` | `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` | #2a measurability-free `1 − μ sᶜ ≤ μ s` |
| `Probability/Moments/SampleMean.lean` | new `Mathlib/Probability/Moments/SampleMean.lean` | #4 sample-mean MSE `∫ ‖r⁻¹ Σ Xₖ − μ‖² = r⁻² Σ ∫ ‖Xₖ − μ‖²` on a finite-dim real IPS (pairwise indep, Bochner mean) |
| `Probability/Moments/Variance.lean` | `Mathlib/Probability/Moments/Variance.lean` | #2b uncentered second-moment Chebyshev |
| `Topology/ApproxMinimizer.lean` | `Mathlib/Topology/Order/Compact.lean` (companion to `IsCompact.exists_isMinOn`) | approximate-minimizer stability: `z k ∈ K` compact, per-point approx-min of continuous `F` with vanishing error ⇒ subsequence → a global minimizer (elementary Γ-convergence recovery) |
