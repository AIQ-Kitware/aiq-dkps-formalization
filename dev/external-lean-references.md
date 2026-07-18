# External Lean references for spectral theory, SVD, and finite frames

This registry records external Lean formalizations that informed or may directly support
this repository. It exists for four reasons:

1. credit the original authors and projects;
2. preserve exact source commits and paths;
3. separate mathematical strategy from independently re-authored Mathlib-facing code; and
4. distinguish license-compatible vendoring from reference-only reading.

## Reuse policy

External sources are divided into two tiers.

### Licensed vendoring

When a compatible explicit license has been verified, selected source snapshots or excerpts
may be committed under `vendor/lean/`. Every such copy must have:

- repository, commit, source path, and blob SHA;
- author and license information;
- an exact/excerpted/modified classification;
- a prominent modification notice when it is not an exact file snapshot; and
- a matching license text under `vendor/lean/LICENSES/`.

Vendored material is not imported by the project build. Adapted production proofs must still
carry source attribution in their own headers and should be reworked into current Mathlib
idiom rather than copied blindly.

### Reference-only sources

When no license is visible, we do not copy source text into the repository. We may document
permalinks, theorem names, and proof strategies, then independently re-derive the result.
A local git-ignored cache under `dev/reference-repos/` may be used during development.

The focused Davis--Kahan reuse analysis is in
`dev/davis-kahan-existing-work-survey.md`. The arbitrary-Hilbert-space graph-subspace donor audit is
in `dev/graph-subspace-vendor-survey-2026-07-14.md`. The local rectangular and frame APIs are staged in
`ForMathlib/Analysis/InnerProductSpace/RectangularSingularValues.lean`,
`SingularSystem.lean`, and `FiniteFrame.lean`.

---

## Current Mathlib singular-value API

At the repository's pinned Mathlib revision
`c368140668f5fa16a1bd977448c1f665d48c3df4`,
`Analysis/InnerProductSpace/SingularValues.lean` defines singular values for a rectangular
finite-dimensional linear map as a zero-padded `Nat`-indexed finitely supported sequence. The values are square roots of the sorted eigenvalues of `T.adjoint.comp T`.
Available API includes nonnegativity, antitonicity, support equal to map rank, and the exact
square/eigenvalue identity.

The missing layer relevant here is not a new singular-value definition. It is:

- adjoint invariance for unequal dimensions;
- sorted positive-spectrum equivalence of `T.adjoint.comp T` and
  `T.comp T.adjoint`;
- a reusable intrinsic singular system and reconstruction theorem; and
- finite-frame analysis/synthesis and frame-bound equivalences.

Mathlib also already has `Matrix.charpoly_mul_comm'` and
`Matrix.charpoly_mul_comm_of_le`, which encode the rectangular `AB`/`BA`
characteristic-polynomial relation and provide an algebraic route to zero-padded spectral
comparison.

---


## Pinned Mathlib graph-subspace infrastructure

The graph-subspace survey found no complete external implementation of the acute-projection-pair
theorem, but it found that the project-pinned Mathlib already supplies nearly all of the supporting
functional analysis:

- `LinearPMap.graph`, closedness, closability, and graph closure;
- anti-Lipschitz complete-range and closed-range theorems;
- `ContinuousLinearMap.equivRange` and continuous left inverses for injective closed-range maps;
- `ContinuousLinearEquiv.ofBijective` from the Banach open-mapping theorem; and
- `Units.oneSub` / `NormedRing.inverse_one_sub` for near-identity compression inverses.

Exact excerpts at pinned Mathlib commit `c368140668f5fa16a1bd977448c1f665d48c3df4` are preserved under
`vendor/lean/mathlib4/`. They are references only; production modules import Mathlib directly.

The complete search history, screened repositories, signature correction, and implementation order
are recorded in `dev/graph-subspace-vendor-survey-2026-07-14.md`.

## Licensed sources vendored in this repository

The exact local inventory is machine-readable in `vendor/lean/manifest.toml`.

### `jbarrcfl/mathlib4`

- Repository: <https://github.com/jbarrcfl/mathlib4>
- Operator-norm commit: `f99fc7704e93eb402469ab24cd6970601aad1141`
- SVD/Eckart-Young commit: `5dae5bc5cdc098c0d21c48590aa47f1cd2e67c9b`
- License: Apache-2.0, retained in source headers.
- Relevant files:
  - `Mathlib/Analysis/InnerProductSpace/SingularValuesNorm.lean`
  - `Mathlib/Analysis/InnerProductSpace/SingularValueDecomposition.lean`

Main reusable content:

- operator norm equals the top singular value;
- right singular eigenbasis of `T.adjoint.comp T`;
- normalized left singular vectors;
- orthogonality and `T v_i = sigma_i u_i`;
- finite reconstruction;
- codomain-basis extension;
- rank truncation and operator-norm Eckart-Young.

The second file is a close architectural match for the proposed intrinsic
`SingularSystem.lean`. It should be audited against the pinned Mathlib before adaptation.
No explicit AI-use statement was found in the surveyed fork PR text, so this registry does
not classify its proofs as AI-generated.

Vendored excerpt:
`vendor/lean/jbarrcfl-mathlib4/TopSingularValue.excerpt.lean`.

### `YuanheZ/lean-stat-learning-theory`

- Repository: <https://github.com/YuanheZ/lean-stat-learning-theory>
- Referenced commit: `216e578c9576bab6b0abc3ba6c65762536768e96`
- License: Apache-2.0.
- Relevant files and blob SHAs:
  - `SLT/MatrixInfra/Basic.lean`, `8c7dd1aaeaedd6c702c28fee2845d9f66cecf219`
  - `SLT/MatrixInfra/CourantFischer.lean`, `ff953534b773b60a5940a7bff0aeae275fc87704`
  - `SLT/MatrixInfra/EYM.lean`, `ef6e16a2942555987e9bfc4d944f96838d72627f`
  - `SLT/MatrixInfra/Perturb.lean`, `1de3e2023f6051fe75f2fb4ecb6ec437fb6cf118`

This is the strongest licensed source found in the extended survey. It develops:

- matrix and linear-map singular systems;
- literal rank-one and `U Sigma V*` reconstruction;
- both Gram decompositions;
- Rayleigh and singular quotients;
- full eigenvalue and singular-value Courant-Fischer formulas;
- leading/trailing spectral subspaces; and
- an attained operator-norm Eckart-Young-Mirsky theorem;
- Weyl perturbation bounds for sorted eigenvalues and singular values;
- spectral-subspace and spectral-projection APIs; and
- eigenvector and spectral-projection Davis--Kahan theorems.

The repository's associated paper describes a human-AI collaborative workflow. Reuse should
credit the named file authors and the project, without assigning a particular theorem to a
particular model unless the project records that provenance.

Vendored excerpts:

- `vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean` preserves the
  right/left singular-vector core, the zero case, orthonormality, and reconstruction.
- `vendor/lean/lean-stat-learning-theory/EYMOperatorNorm.excerpt.lean` preserves the
  operator-norm Eckart--Young lower and attained bounds.
- `vendor/lean/lean-stat-learning-theory/DavisKahanSpectralProjection.excerpt.lean` preserves
  the centered operator-norm spectral-projection DK proof.

### `Dronmong/drifting-identifiability`

- Repository: <https://github.com/Dronmong/drifting-identifiability>
- Referenced commit: `06c699d07c2fa186ba8e708597ccdb9b8ba1c04f`
- License: MIT.
- Relevant files:
  - `DriftingIdentifiability/FiniteStability.lean`
  - `DriftingIdentifiability/EmpiricalFrameBound.lean`

`FiniteStability.lean` proves a particularly useful finite-dimensional theorem: linear
independence of a finite synthesis family yields a positive lower frame constant. The proof
uses `LinearMap.exists_antilipschitzWith`, then converts the ambient sup-norm control into an
entrywise `l1` bound. It also develops an explicit reciprocal inverse-matrix certificate.

This is more application-shaped than the desired Mathlib finite-frame API, but its
antilipschitz proof is a strong donor for the existence direction.

Vendored excerpt:
`vendor/lean/drifting-identifiability/FiniteFrameBound.excerpt.lean`.

---


## Licensed source surveyed but not copied: `adambornemann-glitch/Spectra`

- Repository: <https://github.com/adambornemann-glitch/Spectra>
- Audited commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- License: Apache-2.0.
- Reported toolchain: Lean `v4.31.0-rc1`, one release behind this project.

The project reports a broad proof-complete operator-theory stack: closed and unbounded operators,
self-adjoint extensions, resolvents, projection-valued measures, two spectral-theorem routes,
bounded and unbounded functional calculus, polar decomposition, trace class, and Hilbert--Schmidt
operators.

It is the strongest future vendor candidate found for the spectral-projection, Section 8,
unbounded-operator, and operator-ideal programs. No source is copied in the present pass: the
immediate graph theorem does not need it, and importing or excerpting a large subtree before a
theorem-level dependency audit would obscure the toolchain and API adaptation work still required.
See `dev/graph-subspace-vendor-survey-2026-07-14.md`.

## Direct Davis--Kahan formalizations found in the 2026-07-12 pass

### Licensed direct donor: `YuanheZ/lean-stat-learning-theory`

`SLT/MatrixInfra/Perturb.lean` is the closest compatible external DK development found.  At
commit `216e578c9576bab6b0abc3ba6c65762536768e96` it proves finite-dimensional `RCLike`
operator-norm versions of Weyl, an eigenvector-angle bound, and centered/closed-interval/general
spectral-projection DK bounds.  Its public spectral-subspace API is parallel to, but not
identical with, this repository's `SpectrumIn` and reduction-based API.

Use it as:

- an independent audit of the local operator-norm endpoint;
- a donor for interval/set-separated convenience wrappers;
- a source of already-debugged spectral-projection helper lemmas; and
- a coordination point before upstreaming overlapping Mathlib declarations.

Do not replace the local dimension-free Sylvester, unitarily invariant norm, residual,
projector-difference, sharp-angle, or YWS layers with the narrower finite proof.

### Restrictive reference: `facebookresearch/atlas-lean`

At commit `34ffed396f376454c1a9b297f3fd74c5c801fb50`,
`Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean` proves a real-matrix leading
spiked-covariance eigenvector bound, and `Cor_4_9.lean` combines it with concentration for a
PCA application.  The repository uses CC BY-NC 4.0 plus additional restrictions, including a
machine-learning-use rider.  No source or proof text is copied; the files are recorded only
for theorem-statement comparison.

### Screened out: `jrgochan/prime`

`proofs/Cathedral/Spectral/DavisKahan.lean` at commit
`3b554aa38b0d30f13e81262eeef4d4cf3e8696f6` assumes a DK statement rather than proving it.
It supplies no reusable perturbation argument.

See `dev/davis-kahan-existing-work-survey.md` for the applicability matrix and recommended
reuse boundaries.

---

<!-- BEGIN Spectra collaboration reference -->
## Active external dependency candidate: `adambornemann-glitch/Spectra`

- Repository: <https://github.com/adambornemann-glitch/Spectra>
- Audited commit: `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`
- License: Apache-2.0 in the repository and inspected source modules.
- Integration mode: Git submodule during active collaboration; later a pinned
  Lake Git dependency if the required APIs merge upstream.
- Full audit: `dev/spectra-integration-survey-2026-07-14.md`.

Spectra is the leading candidate for the complex PVM, spectral-theorem,
unbounded self-adjoint, bounded polar-decomposition, trace-class, and
Hilbert--Schmidt substrate. It does not contain the Davis--Kahan graph, angle,
Sylvester, or four-theorem geometry. General PVM range-subspace and reducing
subspace infrastructure should be contributed upstream; paper-facing
perturbation results remain in this repository.

Do not copy Spectra files into `vendor/lean/` as the production integration
strategy, and do not classify declarations from the project's existing Mathlib
dependency as third-party vendor material.
<!-- END Spectra collaboration reference -->

## Reference-only sources: no visible license

### `rjwalters/lean-genius`

- Repository: <https://github.com/rjwalters/lean-genius>
- Earlier referenced commit: `3e09c97392dc68d068becb89e2068b1830234661`
- License status: no root `LICENSE` was visible when checked on 2026-07-12; do not vendor.
- Nature: large automated-proof corpus and proof-search infrastructure.

Previously referenced files:

| File | Content | Use here |
|---|---|---|
| `SchurHornMajorization.lean` | convex/Karamata forward Schur-Horn | strategy for local Schur-Horn |
| `CauchyInterlacingKyFan.lean` | compression trace / Ky Fan partial sums | Ky Fan and compression design |
| `CauchyInterlacingWeyl.lean` | Weyl monotonicity and addition bounds | comparison with local Weyl |
| interlacing keystone/Poincare files | compression and interlacing scaffolds | alternative sorted-spectrum route |

Additional 2026 survey findings in the current corpus/PR history:

- PR `#38360`, `CauchyInterlacingSortedInterlacing.lean`: an abstract sorted-multiset
  selection lemma and termwise eigenvalue interlacing. This is the most relevant possible
  donor for turning multiplicity data into equality of ordered eigenvalue lists.
- PR `#38347`, `CauchyInterlacingPoincareCompression.lean`: Ky Fan trace brackets for
  compressions.
- PR `#27189`, `SpectralTraceDetEigenvaluesOQ01.lean`: trace/determinant as symmetric
  functions of eigenvalues and singularity criteria.
- PR `#36469`: covariance quadratic-form nonnegativity via variance.
- PRs `#33370` and `#33380`: operator absolute value `|A| = sqrt(A†A)` and the intended
  path toward polar decomposition and SVD.

Several PR descriptions explicitly identify Claude Code generation; others only report an
automated-proof workflow. Record provenance per declaration rather than assuming a single
model for the entire repository. Use all of these as strategy references only. In
particular, the interlacing route may help convert `AB`/`BA` nonzero-spectrum facts into
ordered equalities, but any final proof must be independently authored.

### `andersonwu2000/Asterism`

- Repository: <https://github.com/andersonwu2000/Asterism>
- Referenced commit: `5a1701e3c285b504fba0d9bd115345d11d413a77`
- License status: no root `LICENSE` was visible when checked on 2026-07-12; do not vendor.
- Nature: automated Lean proof framework with a generated reusable library.

Most relevant files:

- `Library/LinearAlgebra/SVD/AdjointSelf.lean`
- `Library/LinearAlgebra/SVD/SingularValues.lean`
- `Library/LinearAlgebra/SVD/BasisConstruction.lean`
- `Library/LinearAlgebra/SVD/MatrixForm.lean`
- `Library/LinearAlgebra/SVD/Basic.lean`
- `Library/LinearAlgebra/EckartYoung/SingularEigenRelations.lean`
- `Library/LinearAlgebra/EckartYoung/TopSingularSubspace.lean`
- `Library/LinearAlgebra/EckartYoung/BottomSpanBound.lean`
- `Library/LinearAlgebra/EckartYoung/EckartYoung.lean`

The SVD development is modular and close to the desired proof order:

1. diagonalize `T.adjoint.comp T`;
2. show image inner products are diagonal with entries `sigma_i^2`;
3. normalize nonzero images;
4. extend the normalized family to a codomain orthonormal basis; and
5. assemble a rectangular matrix diagonalization.

This is an excellent proof map, but no text should be copied absent a license.

### `BoltonBailey/BrascampLieb`

- Repository: <https://github.com/BoltonBailey/BrascampLieb>
- Referenced commit: `b721c8c5f17cef32a477e585b8e6941bd0c24aa5`
- Relevant file:
  `BrascampLieb/ToMathlib/Analysis/InnerProductSpace/SingularValue.lean`
- License status: no root `LICENSE` found; do not vendor.

The file proves nonzero-spectrum transport between `f.adjoint * f` and
`f * f.adjoint` using `spectrum.nonzero_mul_comm`, then derives equality of the nonzero
ranges of singular values for a square map and its adjoint. This is a useful compact route
for existence/set-level facts, but it does not by itself preserve multiplicity or sorted
zero padding. The final rectangular theorem needs a stronger argument.

Mirrors appear in `project-numina/BrascampLieb` and the LeanTriathlon corpus; those mirrors
do not change the licensing decision for the surveyed source.

### `jaumededios/Cantor_Measure_Frames`

- Repository: <https://github.com/jaumededios/Cantor_Measure_Frames>
- Referenced commit: `f9b80c7e9640bcd320707b84cffe86d672ed0409`
- Relevant file: `CantorMeasureFrames/Basic.lean`
- License status: no root `LICENSE` found; do not vendor.

The file provides clean countable-frame and explicit two-sided frame-bound definitions in
Hilbert and `L2` spaces. It is useful for statement design, but it does not yet provide the
finite analysis/synthesis operator API needed here.

---

## Other adjacent Lean developments

### Closed Mathlib rectangular-SVD PRs

Closed, unmerged Mathlib PRs `#31821` (head
`05cfe4d60de27b5d06d2b186c8ad552ef0d723e1`) and `#31830` (head
`dd72e823b585f9ca3980dfef2a2b43e7d8ecfe7c`) develop explicit complex rectangular matrix
SVDs. Their Apache-2.0 source headers list `Authors: Levi, GPT 5.1`. They contain useful constructions for
thin SVD, pseudoinverse diagonal factors, and tall/wide basis completion. Review discussion
also exposes design problems to avoid: duplicate unitary notions, global configuration
changes, missing structural conditions, and matrix-specific metavariable workarounds.

Use them as a proof quarry, not as the architectural base.

### Zulip and review-discussion status

No directly relevant public Zulip thread was found by the indexed searches run on
2026-07-12. This is not evidence that no discussion exists; Zulip archives are not reliably
indexed by general search. The Mathlib PR `#31830` review is therefore the concrete design
discussion currently preserved here. Its actionable feedback was to reuse the existing
`Matrix.unitaryGroup`, avoid unexplained global option changes, and state all structural
unitarity conditions explicitly.

Before opening the first upstream PR, start a focused Zulip thread with the proposed root
theorem (the nonzero eigenspace equivalence for `A†A` and `AA†`), link the active
Hilbert--Schmidt/singular-value work, and ask whether reviewers prefer:

- the intrinsic eigenspace equivalence first;
- a characteristic-polynomial `AB`/`BA` theorem first; or
- a larger singular-system file.

Record the resulting thread permalink in this section.

### Active Hilbert-Schmidt and Eckart-Young work

Mathlib PR `#41477` adds a scoped Hilbert-Schmidt inner product and norm on rectangular
finite-dimensional linear maps. Its author discloses Claude Code assistance and plans
follow-up branches for Frobenius and operator-norm Eckart-Young results. Coordinate before
upstreaming overlapping norm or low-rank approximation results.

### Approximation numbers

Mathlib PR `#32126` is an open draft defining approximation numbers for continuous linear
maps as best finite-rank approximation errors. The current zero-padded finite-dimensional
singular-value API was designed to be compatible with that eventual extension. New work
should preserve this design rather than introduce a competing finite-indexed definition.

### Other repositories found

- `marcmorningstar/lean4-ergodic-theory`: singular exponents, exterior norms, and Lyapunov
  applications; adjacent to multiplicative singular-value theory.
- `rkirov/linear-algebra-done-right-lean`: textbook SVD chapters and useful elementary
  operator lemmas.
- `NetRxn/SK_EFT_Hawking`: vector majorization and sorted-prefix sums; already used as a
  Schur-Horn design reference. Exact source:
  `lean/SKEFTHawking/QuantumNetwork/VectorMajorization.lean` at commit
  `a55226f613c54b4a272dafa7f2bf8bb2bcca3921`.

---

## Correspondence to this repository

| Local target | Best donor/reference | Intended use |
|---|---|---|
| rectangular adjoint invariance | Asterism SVD; BrascampLieb nonzero spectrum; Mathlib charpoly `AB/BA` | choose singular-system proof, use others as cross-checks |
| left singular vectors and reconstruction | jbarrcfl SVD; Asterism; lean-stat-learning-theory `Basic.lean` | adapt into intrinsic `SingularSystem.lean` |
| top and bottom singular values | jbarrcfl norm proof; local `SingularSubspace.lean`; lean-stat CF | consolidate variational API |
| singular Courant-Fischer | lean-stat `CourantFischer.lean` | licensed adaptation, coordinate with local CF |
| operator-norm Eckart-Young | lean-stat `EYM.lean`; jbarrcfl SVD | licensed adaptation |
| finite lower frame existence | drifting-identifiability `FiniteStability.lean` | generalize from application indexing/norm to finite frames |
| finite frame definitions | Cantor frames; local generalized DK theory | statement design, independent implementation |
| finite operator-norm spectral projection DK | lean-stat `Perturb.lean` | licensed audit/donor for interval and set-separation wrappers |
| statistical leading-eigenvector application | Atlas `Thm_4_8.lean` / `Cor_4_9.lean` | restrictive reference-only statement comparison |
| sorted compression/interlacing | lean-genius corpus | reference-only alternate route |

---

## Prior Schur-Horn correspondence

The earlier Schur-Horn work remains independently re-derived from the strategy in
`lean-genius/SchurHornMajorization.lean`:

| Our declaration | Source declaration read | Relationship |
|---|---|---|
| `convexOn_sum_re_inner_orthonormalBasis_self_le` | `schur_majorization_convexOn` | same doubly-stochastic/Jensen strategy, independently re-derived |
| `sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues` | `schur_trace_eq` | trace equality case |
| `sum_sq_re_inner_orthonormalBasis_self_le_sum_sq_eigenvalues` | `schur_sum_sq_le` | square-function instance |
| `schurWeight` and row/column sums | `dsWeight` and row/column sums | same weight-matrix design |

## Approximation-number upstream draft

- Pull request: <https://github.com/leanprover-community/mathlib4/pull/32126>
- Audited head: `1751f75e87544fc47dc06b123922ec71ccd2d11e`
- Status on 2026-07-18: open draft, not merged.
- Relevant file: `Mathlib/Analysis/Normed/Operator/SingularValues.lean`.

The draft defines zero-based best finite-rank approximation numbers as an
`NNReal` infimum and proves the basic infimum API, normalization, monotonicity,
and near-minimizer existence.  The project adapts that small stable core under
`ForMathlib/Analysis/Normed/Operator/ApproximationNumber.lean` rather than
pinning production code to an unmerged Mathlib branch.  The local adaptation
adds the perturbation, composition, and scalar laws needed by the operator
ideal layer.  The draft does not currently supply the Hilbert-space adjoint
law, the Ky Fan triangle theorem, or the strong-cutoff convergence theorem.
