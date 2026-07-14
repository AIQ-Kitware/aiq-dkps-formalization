# AIQ DKPS Formalization

Lean 4 formalizations for response-based embeddings of black-box generative
models, centered on the data kernel perspective space (DKPS) and the
multidimensional-scaling / spectral-perturbation infrastructure needed to make
those theorem statements precise.

This repository focuses on six active Lean libraries:

| Library        | Role                                                                                                                    |
| -------------- | ------------------------------------------------------------------------------------------------------------------------|
| `ForMathlib`   | Mathlib-staging library for reusable, paper-agnostic infrastructure. |
| `DavisKahan`  | Davis--Kahan perturbation library targeting the full Hilbert-space 1970 theory; the stable finite branch is a valuable specialization, while bounded, ideal-norm, and unbounded coverage remain active. |
| `Acharyya2024` | Asymptotic DKPS/raw-stress MDS consistency for model representations.                                                   |
| `Acharyya2025` | Finite-sample concentration for response-based vector embeddings, including a proved CMDS spectral perturbation bridge. |
| `DkpsQuench2026` | Query-efficiency theorem family for DKPS-based benchmark prediction from cached responses.                             |
| `Helm2025`     | Transfer of statistical-inference guarantees from population DKPS embeddings to estimated/aligned embeddings.           |

The active libraries formalize more than paper-facing wrappers.  They include
supporting mathematics for raw-stress multidimensional scaling, classical MDS
double-centering, finite-dimensional spectral perturbation, orthogonal-alignment
(Gram rigidity / polar factor) bookkeeping, sample-mean concentration,
high-probability event propagation, and consistency transfer.

## Repository layout

```text
.
├── ForMathlib.lean        # root module for the Mathlib-staging library
├── ForMathlib/            # staged reusable Mathlib additions
├── DavisKahan.lean        # root module for the stable Davis--Kahan library
├── DavisKahan/            # bounded, finite, source, specialized, alternative, and experimental branches
├── Acharyya2024.lean      # root module for the 2024 consistency library
├── Acharyya2024/          # raw-stress MDS, probability, second moments, paper-facing consistency
├── Acharyya2025.lean      # root module for the 2025 concentration library
├── Acharyya2025/          # CMDS, Weyl/Davis-Kahan, Gram rigidity/polar factor, aligned finite-sample rates
├── DkpsQuench2026.lean    # root module for the 2026 Quench formalization
├── DkpsQuench2026/        # subject-oriented paper, geometry, response, spectral, rate, and query-efficiency modules
├── Helm2025.lean          # root module for the statistical-inference transfer layer
├── Helm2025/              # population/estimated DKPS transfer theorem statements and bridge
├── Challenge/             # comparator challenges (MathlibCandidate / MathlibPending) + manifest
├── comparator/            # per-PR comparator configs
├── docs/                  # planning trackers (docs/planning) and challenge how-to (docs/challenge)
├── dev/                   # engineering memory: benchmark questions + debug postmortems (agent-readable)
├── external/Spectra       # Git submodule for collaborative spectral/operator infrastructure
├── lakefile.toml          # Lake workspace for the six active libraries
├── lake-manifest.json     # pinned dependency manifest
└── lean-toolchain         # Lean toolchain pin
```

The sidecar files such as `Acharyya2025.lean` are normal Lean root modules.  The
subdirectory files are imported as submodules, for example
`Acharyya2025.RateChain`.

**Agents / contributors:** [`dev/`](dev/README.md) is long-running engineering
memory — distilled benchmark questions and effortful-debug postmortems from real
work in this repo. Read [`dev/SEARCH.md`](dev/SEARCH.md) before a task that
resembles a past mistake (restating a theorem, slimming a conformance, matching a
comparator export); add to it after a fix whose root cause is a transferable
invariant.

## Fresh environment

In a fresh environment you will need to setup Lean4, see:

```bash
./setup_lean.sh
```

<!-- BEGIN Spectra collaboration checkout -->
## Spectra collaboration checkout

The full Hilbert-space Davis--Kahan roadmap needs spectral-measure and
unbounded-operator infrastructure that is being developed in the external
[`Spectra`](https://github.com/adambornemann-glitch/Spectra) project. During the
collaboration phase, this repository tracks Spectra as the Git submodule
`external/Spectra` rather than copying selected source files.

Initialize it with:

```bash
git submodule update --init --recursive
```

For a first checkout, or to configure the upstream and contribution remotes:

```bash
scripts/bootstrap_spectra_submodule.sh --create-fork
```

The submodule is intentionally staged separately from the Lake dependency.
After porting the Spectra compatibility branch to this repository's Lean and
Mathlib pins, enable and test the narrow dependency cone with:

```bash
python3 scripts/enable_spectra_lake_dependency.py
scripts/spectra_import_smoke.sh
```

See `dev/spectra-integration-survey-2026-07-14.md` for the division of labor,
reviewed modules, version-skew risks, and planned upstream contributions.
<!-- END Spectra collaboration checkout -->

## Build

```bash
lake exe cache get
lake build ForMathlib DavisKahan Acharyya2024 Acharyya2025 DkpsQuench2026 Helm2025
```

To build everything declared in `lakefile.toml`:

```bash
lake build
```

## Formalization scope

### `ForMathlib`

Staging area for upstream Mathlib contributions extracted from the paper
libraries: results are restated in Mathlib idiom (e.g. generalized from `ℝ` to
`RCLike 𝕜`), placed in files mirroring their proposed Mathlib destination
paths, and import only Mathlib.  The paper libraries import these general
versions and keep only thin paper-facing specializations.  See
`ForMathlib/README.md` for the contribution workflow and
`planning/mathlib-candidates.md` for the ranked candidate list.

### `DavisKahan`

Canonical spectral-subspace perturbation theory extracted from the former
`ForMathlib` staging monoliths. The project target is the full Hilbert-space
scope of Davis--Kahan (1970), including the bounded main body, arbitrary
unitary-invariant norm scope, and unbounded self-adjoint passages. `import
DavisKahan` currently exposes supported bounded-operator results, the strong
finite-dimensional specialization, and a finite Part III facade; this import
must not be interpreted as a full-paper completion claim. Other source
surfaces, specialized endpoints, alternative proofs, and mirrored experiments
require explicit imports; `DavisKahan.All` collects all proof-finished branches.
General-purpose linear-algebra infrastructure remains in `ForMathlib`. See
`DavisKahan/README.md` and
`docs/planning/davis-kahan-full-paper-goal.md`.

### `Acharyya2024`

Formalizes the consistency layer for generative-model representations in DKPS.
The library includes finite-dimensional DKPS/MDS definitions, second-moment
sample-mean algebra, probability bounds via Chebyshev and union bounds,
raw-stress stability, and repaired paper-facing consistency statements with
explicit hypotheses for uniqueness and sampling/limit behavior.

### `Acharyya2025`

Formalizes a finite-sample concentration chain for response-based vector
embeddings.  Beyond the probability step, this library proves an aligned
classical-MDS perturbation pipeline: double-centering stability,
entrywise-to-operator transport, Weyl-style spectral perturbation,
Davis-Kahan-style subspace control, Gram realization facts,
quantitative polar alignment, and an explicit end-to-end rate chain.

### `DkpsQuench2026`

Formalizes query-efficient benchmark-score prediction from cached model
responses.  The theorem layer uses the literal tie-averaged nearest-neighbor
estimator, states eventual fixed-`Q`, size-`m`, and all-strict-budget
conclusions, and derives uniform reference coverage from compactness, full
support, and iid sampling.  A fixed-population theorem connects directly to the
`Acharyya2025` second-moment chain.  The newer target-augmented theorem runs CMDS
on `Fin (n+1)` at stage `n`, controls only target-to-reference distances, and
removes the global finite factorization of the model class.

`DkpsQuench2026/` is organized by mathematical subject rather than by
workflow stage.  The `Paper` modules retain the theorem shape closest to the
article; `Geometry`, `Response`, `Spectral`, `Probability`, and `Rates` derive
the intermediate certificates; and `QueryEfficiency` exposes the finite,
compact-infinite, and all-query raw-response theorem family.  The canonical tree
contains no remaining proof holes.

### `Helm2025`

Formalizes transfer results for statistical inference on black-box generative
models in DKPS.  The bridge file connects `Acharyya2025` aligned finite-sample
concentration to estimated-embedding alignment events and consistency
hypotheses used by the inference layer.

## Literature/formalization discrepancy ledger

[`papers/DKPS-formalized-vs-literature.tex`](papers/DKPS-formalized-vs-literature.tex)
is the maintained audit for the four primary DKPS papers. It records repaired
statements, surfaced assumptions, strengthened or weakened conclusions, MDS
variant differences, completed theorem mappings, and the remaining opportunities for hypothesis reduction. Update it whenever a
preferred public capstone changes its hypothesis load or scope.

## References

### Direct theorem targets

- Aranyak Acharyya, Michael W. Trosset, Carey E. Priebe, and Hayden S. Helm.
  *Consistent estimation of generative model representations in the data kernel
  perspective space*. arXiv:2409.17308, 2024.

- Aranyak Acharyya, Joshua Agterberg, Youngser Park, and Carey E. Priebe.
  *Concentration bounds on response-based vector embeddings of black-box
  generative models*. arXiv:2511.08307, 2025.

- Hayden S. Helm, Aranyak Acharyya, Youngser Park, Brandon Duderstadt, and
  Carey E. Priebe. *Statistical inference on black-box generative models in the
  data kernel perspective space*. Findings of ACL, 2025.

- Hayden Helm, Ben Johnson, and Carey Priebe. *Query-efficient model evaluation
  using cached responses*. arXiv:2605.07096, 2026.

### DKPS and response-based model embeddings

- Brandon Duderstadt, Hayden S. Helm, and Carey E. Priebe. *Comparing
  Foundation Models using Data Kernels*. arXiv:2305.05126, 2023.

- Hayden Helm, Brandon Duderstadt, Youngser Park, and Carey Priebe. *Tracking
  the perspectives of interacting language models*. EMNLP, 2024.

### Multidimensional scaling and alignment

- Warren S. Torgerson. *Multidimensional Scaling: I. Theory and Method*.
  Psychometrika, 17(4):401-419, 1952.

- J. C. Gower. *Some Distance Properties of Latent Root and Vector Methods Used
  in Multivariate Analysis*. Biometrika, 53(3-4):325-338, 1966.

- J. B. Kruskal. *Multidimensional scaling by optimizing goodness of fit to a
  nonmetric hypothesis*. Psychometrika, 29:1-27, 1964.

- Michael W. Trosset and Carey E. Priebe. *Continuous Multidimensional
  Scaling*. arXiv:2402.04436, 2024.

- Anna Little, Yuying Xie, and Qiang Sun. *An Analysis of Classical
  Multidimensional Scaling with Applications to Clustering*. Information and
  Inference: A Journal of the IMA, 12(1):72-112, 2023.

- Colin Goodall. *Procrustes Methods in the Statistical Analysis of Shape*.
  Journal of the Royal Statistical Society, Series B, 53(2):285-321, 1991.

### Spectral perturbation

- Chandler Davis and W. M. Kahan. *The Rotation of Eigenvectors by a
  Perturbation. III*. SIAM Journal on Numerical Analysis, 7(1):1-46, 1970.

- Yi Yu, Tengyao Wang, and Richard J. Samworth. *A useful variant of the
  Davis-Kahan theorem for statisticians*. Biometrika, 102(2):315-323, 2015.

- Yuxin Chen, Yuejie Chi, Jianqing Fan, and Cong Ma. *Spectral Methods for Data
  Science: A Statistical Perspective*. Foundations and Trends in Machine
  Learning, 14(5):566-806, 2021.

## Growing response-level Quench chain

The growing target-augmented Quench path now has a response-level front end.
Stage-dependent response means propagate to stage-dependent CMDS entrywise
control, and a finite-target second-moment corollary closes the full chain from
response errors to eventual query efficiency.  Hypothesis-reduced capstones now
derive population PSD/rank from the Gram witness, and finite target classes
derive compactness automatically.  Infinite target classes still require a
genuine uniform response concentration theorem; this is no longer conflated
with the spectral or nearest-neighbor parts of the development.
