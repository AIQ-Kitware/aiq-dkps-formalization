# Davis--Kahan existing-work survey

Survey date: 2026-07-12

This document answers two separate questions:

1. which reference proofs already vendored for Perfect Quench materially reduce the Davis--Kahan workload; and
2. which additional Lean developments should be copied, adapted, cross-checked, or merely cited.

The survey is theorem- and license-aware. A nearby theorem is useful only when its statement,
proof architecture, toolchain, and reuse terms fit the local development.

## Executive assessment

The existing Perfect Quench vendor set is highly useful, but mostly as shared spectral
infrastructure rather than as a replacement for the Davis--Kahan core.

| Existing snapshot | Direct DK value | Perfect Quench value | Best local targets |
|---|---:|---:|---|
| `SingularSystemGram.excerpt.lean` | high | high | `RectangularSingularValues.lean`, `SingularSystem.lean`, principal-angle coordinate models, singular-subspace DK |
| `TopSingularValue.excerpt.lean` | medium | medium | operator-norm endpoints, largest principal sine, residual and dilation wrappers |
| `EYMOperatorNorm.excerpt.lean` | low to medium | high | truncated estimators, low-rank approximation, spectral-tail control; not the main self-adjoint DK proof |
| `FiniteFrameBound.excerpt.lean` | medium to high | high | generalized/trial-subspace DK, conditioning of analysis maps, positive lower frame constants |

The strongest newly found direct donor is
`YuanheZ/lean-stat-learning-theory/SLT/MatrixInfra/Perturb.lean`. It contains an
Apache-2.0 finite-dimensional `RCLike` development of Weyl bounds, spectral subspaces,
spectral projections, an eigenvector-angle theorem, and an operator-norm spectral-projection
Davis--Kahan theorem. A focused excerpt of its centered projection proof is now preserved in
`vendor/lean/lean-stat-learning-theory/DavisKahanSpectralProjection.excerpt.lean`.

It should not replace the local architecture. The local development is substantially broader:
it has a dimension-free Sylvester core, arbitrary unitarily invariant norms, Frobenius and
Ky Fan endpoints, residual theorems, projector differences, principal-angle dictionaries,
Davis's `sin 2 theta` and `tan 2 theta` results, sharpness, singular subspaces, and the
Yu--Wang--Samworth aligned-basis chain. The external proof is most valuable for:

- checking the finite operator-norm endpoint independently;
- supplying a clean interval/set-separation convenience API;
- reducing risk in remaining spectral-projection adapters; and
- identifying already-solved Weyl and spectral-subspace helper lemmas.

## Detailed reuse map

### Singular systems and rectangular Gram spectra

The singular-system snapshot is the most important shared dependency. Davis--Kahan for
singular subspaces is normally obtained either from Hermitian dilation or from the two Gram
operators `A†A` and `AA†`. The donor already proves the right singular basis equation,
constructs nonzero left singular vectors, handles zero singular values, proves
orthonormality, and reconstructs the map.

This directly lowers the difficulty of:

- nonzero eigenspace equivalence between `A†A` and `AA†`;
- adjoint invariance of positive singular spectra;
- intrinsic left/right singular systems;
- principal-angle coordinate isometries for rectangular maps; and
- right/left singular-subspace perturbation wrappers.

The donor is Euclidean/matrix-shaped, while the desired local API is intrinsic. The right
move is to adapt its proof seams, not its public matrix interface.

### Top singular value and operator norm

The top-singular-value excerpt closes an endpoint that otherwise repeatedly reappears:
turning a largest singular value into an operator norm. It is useful after the geometric or
Sylvester work is done, especially for:

- `sin(theta_max)` interpretations;
- cross-projection operator norms;
- residual-map operator-norm corollaries; and
- Hermitian-dilation singular-subspace bounds.

It does not prove spectral separation or any DK inequality by itself.

### Eckart--Young--Mirsky

The EYM excerpt is not a shortcut for classical self-adjoint DK. It becomes valuable when the
operator entering DK is itself a truncated, compressed, or empirical low-rank approximation.
For Perfect Quench, it can turn singular-value tails into certified approximation errors and
can justify replacing a full operator by a rank-constrained surrogate before applying a
perturbation theorem.

The most likely future use is a two-stage result:

1. control the approximation error of a truncated empirical/operator model by EYM; then
2. feed that error into a DK or singular-subspace theorem.

### Finite frames

The finite-frame donor is more relevant to DK than its application-specific presentation
suggests. A positive lower frame constant is a coercivity certificate for the analysis map.
That is exactly the kind of hypothesis needed by generalized eigenvalue, trial-subspace, and
non-orthonormal-coordinate variants of DK.

It is especially useful for:

- proving injective analysis/synthesis maps are quantitatively bounded below;
- converting spanning or independence assumptions into a positive conditioning constant;
- controlling covariance/Gram maps in Perfect Quench; and
- discharging transversality assumptions in generalized DK statements.

The donor uses a finite coordinate/sup-norm route. The local Mathlib-facing layer should expose
basis-free analysis, synthesis, Gram, frame, and coercivity theorems.

## Newly surveyed direct DK formalizations

### `YuanheZ/lean-stat-learning-theory`

- Repository: <https://github.com/YuanheZ/lean-stat-learning-theory>
- Commit surveyed: `216e578c9576bab6b0abc3ba6c65762536768e96`
- File: `SLT/MatrixInfra/Perturb.lean`
- Blob: `1de3e2023f6051fe75f2fb4ecb6ec437fb6cf118`
- License: Apache-2.0

Relevant declarations include:

- `LinearMap.IsSymmetric.spectralSubspace`;
- `LinearMap.IsSymmetric.spectralProjection`;
- `LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm`;
- `LinearMap.abs_singularValues_sub_le_opNorm`;
- `LinearMap.IsSymmetric.davisKahan_eigenvector_angle_hdp`;
- `LinearMap.IsSymmetric.davisKahan_spectralProjection_centered`;
- `LinearMap.IsSymmetric.davisKahan_spectralProjection_closedInterval_hdp`; and
- `LinearMap.IsSymmetric.davisKahan_spectralProjection_hdp`.

The proof architecture is finite-dimensional and coordinate/eigenbasis driven. The centered
projection theorem bounds the lower action of the shifted operator on one selected block,
upper-bounds it on the other, decomposes the shifted cross projection into perturbation and
within-block pieces, and cancels the radius term. This is an excellent independent audit of
the local coercivity/Sylvester endpoint.

Recommended action:

- keep the copied proof as an unbuilt reference excerpt;
- add compatibility lemmas only where they simplify public interval/set-separated statements;
- retain the local `SpectrumIn`, reduction, residual, and dimension-free Sylvester core;
- port missing helper lemmas with explicit source attribution; and
- coordinate any upstreaming to avoid parallel incompatible spectral-subspace APIs.

### `facebookresearch/atlas-lean`

- Repository: <https://github.com/facebookresearch/atlas-lean>
- Commit surveyed: `34ffed396f376454c1a9b297f3fd74c5c801fb50`
- Files:
  - `Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_8.lean`
  - `Atlas/HighDimensionalStatistics/code/Chapter4/Cor_4_9.lean`
- License: CC BY-NC 4.0 with additional restrictions, including a machine-learning-use rider

`Thm_4_8.lean` proves a real-matrix, single-leading-eigenvector Davis--Kahan sine bound for a
spiked covariance model. `Cor_4_9.lean` combines it with covariance concentration for a PCA
application. These are useful statement-level comparisons for the local rank-one and
statistical wrappers, but they are much narrower than the local subspace theory.

Because the repository's terms prohibit the relevant reuse mode, no source text or proof
strategy is copied here. Record only theorem names, statements, and bibliographic comparison.

### `jrgochan/prime`

- Repository: <https://github.com/jrgochan/prime>
- Commit surveyed: `3b554aa38b0d30f13e81262eeef4d4cf3e8696f6`
- File: `proofs/Cathedral/Spectral/DavisKahan.lean`

This file assumes a Davis--Kahan statement and uses it in an unrelated speculative bridge. It
contains no reusable proof of the perturbation theorem and should not influence the local
architecture.

## Mathlib and upstream coordination

- Mathlib PR `#41477` develops a scoped Hilbert--Schmidt norm for rectangular linear maps and
  explicitly plans Frobenius EYM follow-ups. The local Frobenius/UINorm layer should be ready
  to migrate to this API rather than competing with it.
- Mathlib PRs `#31821` and `#31830` contain closed rectangular matrix-SVD developments. They
  remain useful proof quarries but are matrix-specific and were not accepted as the API base.
- Mathlib PR `#40771` is the repository author's draft DK eigenspace contribution. It overlaps
  this repository rather than constituting independent external evidence; future upstream work
  should consolidate around the strongest local theorem family.
- No independent substantial Lean proof of principal-angle symmetry, the UINorm Sylvester
  theorem, Davis's sharp `sin 2 theta` theory, or the full YWS aligned-basis result was found.

## What should be imported, adapted, or left alone

### Import as a dependency

Not recommended now. The external SLT project tracks a nearby but different Lean/Mathlib
revision and defines overlapping spectral infrastructure. A direct dependency would create
namespace/API coupling for a small number of donor proofs.

### Vendor exact excerpts

Recommended for stable, license-compatible proof seams with immutable provenance. The current
vendor directory now covers:

- top singular value/operator norm;
- singular systems and Gram decompositions;
- operator-norm EYM;
- finite lower-frame existence; and
- the centered spectral-projection DK proof.

### Adapt into production

Recommended only when a donor closes an actual local seam. Production code should use local
names and current Mathlib idiom, preserve theorem-level attribution in comments, and avoid
copying application-specific wrappers.

### Reference only

Use this category for restrictive, unclear, or absent licenses and for developments that only
state rather than prove a result. The Atlas files and the Prime file belong here.

## Highest-value next actions

1. Use the lean-stat centered projection proof to audit and, if useful, add an interval/set
   separated wrapper around the already-proved local operator-norm theorem.
2. Finish the intrinsic rectangular singular-system and adjoint-invariance layer using the
   existing singular-system donor as the primary proof quarry.
3. Finish the finite-frame analysis/synthesis API and connect positive frame bounds to the
   generalized DK coercivity hypotheses.
4. Track Mathlib PR `#41477`; replace local Frobenius infrastructure with upstream API when it
   stabilizes.
5. Use EYM only at the estimator/truncation boundary, not as a detour in the classical DK core.
6. Keep related-work notes on overlapping theorem declarations current as external projects
   evolve.

## Search coverage and negative results

The 2026-07-12 pass searched GitHub code and Mathlib pull requests for Davis--Kahan,
spectral-projection perturbation, principal/canonical angles, Sylvester spectral separation,
Weyl singular-value perturbation, SVD, EYM, Hilbert--Schmidt norms, and finite-frame bounds.

The search found two substantive external DK developments: the Apache-2.0 lean-stat file and
the restrictive Atlas PCA endpoint. It found no additional reusable Lean development that
supersedes the local Sylvester/UINorm/principal-angle/sharp-Davis infrastructure.
