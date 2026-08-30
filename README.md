# AIQ DKPS Formalization

Lean 4 formalizations for response-based embeddings of black-box generative
models, centered on the data kernel perspective space (DKPS) and the
multidimensional-scaling / spectral-perturbation infrastructure needed to make
those theorem statements precise.

`ForTauCeti` is the deliverable. Everything else either feeds it or consumes it.

## The libraries

**`lake build` builds these.** A result not reachable from one of them is not
guarded: it may be proved and still break unnoticed, which is why the censuses
report "proved in the default build" rather than "proved".

| Library | Role |
| --- | --- |
| `ForTauCeti` | **The product.** The elegant, paper-independent operator-theory library staged for upstream, with declarations already carrying their final `TauCeti.*` namespaces. Polished roadmaps are generated *from* it. |
| `DavisKahan` | The paper-facing Davis--Kahan library, targeting the full Hilbert-space 1970 theory rather than its finite-dimensional specialization. May consume `ForTauCeti`. |
| `YuWangSamworth2015` | Yu--Wang--Samworth (2015): Theorems 1--3, Corollary 1, Lemma A1, and the appendix identities, with source defects recorded explicitly. Sorry-free. |
| `RoadmapBridge` | Discharges roadmap signatures with the delivered declarations, so "delivered" is a claim the compiler checks rather than a name match. |
| `Acharyya2024` | Asymptotic DKPS/raw-stress MDS consistency for model representations. |
| `Acharyya2025` | Finite-sample concentration for response-based vector embeddings, including a proved CMDS spectral-perturbation bridge. |
| `DkpsQuench2026` | Query-efficiency theorem family for DKPS-based benchmark prediction from cached responses. |
| `Helm2025` | Transfer of statistical-inference guarantees from population DKPS embeddings to estimated/aligned embeddings. |

**Outside the default build, deliberately.** Each is built by naming it:

| Library | Why it is not guarded |
| --- | --- |
| `DavisKahan.Experimental` | A drained staging area. What it held has been promoted into `DavisKahan`/`ForTauCeti` or deleted; two ideal-family scratch modules remain, and they do not compile against the current ideal API. |
| `Challenge` | Comparator challenges, which are posed problems rather than results. |

The libraries formalize more than paper-facing wrappers. They include supporting
mathematics for raw-stress multidimensional scaling, classical MDS
double-centering, spectral perturbation, orthogonal-alignment (Gram rigidity /
polar factor) bookkeeping, operator ideals and approximation numbers,
sample-mean concentration, high-probability event propagation, and consistency
transfer.

`ForMathlib` is **gone**, retired into `ForTauCeti` in full. There is no second
staging area.

## Where the project actually stands

Two censuses map each numbered result of a source paper to the Lean declarations
that discharge it, and both report against the build rather than against
themselves:

```bash
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_yu_wang_samworth_source_census.py
```

They are maintained by hand. When a declaration is renamed or moved, the census
entry is edited in the same commit — that is the maintenance, and inferring it
automatically is what previously produced status that looked healthy and was not.

## Repository layout

```text
.
├── ForTauCeti.lean          # root module for the deliverable
├── ForTauCeti/              # the staged upstream library: operator ideals, approximation
│                            #   numbers, polar decomposition, spectral order, sin-theta
├── RoadmapBridge.lean       # root module for the roadmap-to-delivery bridge
├── RoadmapBridge/           # each roadmap signature discharged by the delivered declaration
├── DavisKahan.lean          # root module for the paper-facing Davis--Kahan library
├── DavisKahan/              # Sources/ (source-faithful 1970), FiniteDimensional/, SinTheta/,
│                            #   Sylvester/, SpectralTheory/, Geometry/, InfiniteDimensional/
├── YuWangSamworth2015/      # Yu--Wang--Samworth 2015 paper-facing package (sorry-free)
├── Acharyya2024{.lean,/}    # raw-stress MDS, probability, second moments, consistency
├── Acharyya2025{.lean,/}    # CMDS, Weyl/Davis--Kahan, Gram rigidity, finite-sample rates
├── DkpsQuench2026{.lean,/}  # geometry, response, spectral, rate, query-efficiency modules
├── Helm2025{.lean,/}        # population/estimated DKPS transfer statements and bridge
├── Challenge/               # comparator challenges (MathlibCandidate / MathlibPending)
├── comparator/              # per-PR comparator configs
├── dev/                     # engineering memory, the source censuses, and audit records
├── docs/                    # planning trackers and challenge how-to
├── external/                # notes on optional editable external checkouts
├── submodules/              # coordination/reference/delivery repos; never build inputs
├── retired/                 # provenance for the closed Spectra collaboration
├── scripts/                 # the census tools and the build gates (`scripts/run_gates.py`)
├── lakefile.toml            # Lake workspace: default targets and explicit opt-in libraries
├── lake-manifest.json       # pinned dependency manifest
└── lean-toolchain           # Lean toolchain pin
```

The sidecar files such as `Acharyya2025.lean` are normal Lean root modules.  The
subdirectory files are imported as submodules, for example
`Acharyya2025.RateChain`.

Git repositories under `submodules/` are a different concept: they are optional
coordination/reference/delivery checkouts and are not required by `lake build`.
Standalone delivery repositories own their own submission-specific statements,
metadata, and verification workflow. Mathematical and public-API fixes are made in
this repository first, then copied/refreshed into the relevant standalone repository.
See [`submodules/README.md`](submodules/README.md).

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
## Spectra collaboration — CLOSED 2026-07-29

The Spectra collaboration is over and **nothing here needs setting up**. This
section previously told readers to create an `external/Spectra` submodule and
enable a Lake dependency on it; both are gone.

Final state: in-scope `import Spectra` is **0**, the vendored source tree and
`external/Spectra` submodule are gone, and the sixteen lifecycle scripts were
removed. Attribution and exact recovery material remain under `retired/`,
including `Spectra.UPSTREAM.md`, `Spectra.SHA256SUMS`, and the complete-fork
patch; the live provenance map is `dev/tauceti/spectra-provenance-map.md`.

For the record of the completed campaign see
[`dev/spectra-integration-survey-2026-07-14.md`](dev/spectra-integration-survey-2026-07-14.md)
and [`dev/tauceti/spectra-removal-plan.md`](dev/tauceti/spectra-removal-plan.md);
both describe finished work.
<!-- END Spectra collaboration checkout -->

## Build

```bash
lake exe cache get
lake build
```

`lake build` builds every default target. `Challenge`, the diagnostic audit
modules, and the drained experimental tree are opt-in, and are built by naming
them:

```bash
lake build Challenge
lake build DavisKahan.Audits.All
lake build DavisKahan.Experimental
```


The gates are Python and run separately. Do not run `lake` at the same time —
five gates shell out to it and a concurrent build makes them report failures that
are not real:

```bash
python3 scripts/run_gates.py          # all of them
python3 scripts/run_gates.py --fast   # skip the five that build Lean
```

## Formalization scope

### `ForTauCeti`

The library this repository exists to produce: reusable operator theory in
upstream idiom, generalized past the papers that motivated it (typically from `ℝ`
to `RCLike 𝕜`, and from finite dimensions to a Hilbert space), with declarations
already in their final `TauCeti.*` namespaces and provenance on every module. The
paper libraries import it and keep only thin paper-facing specializations.

It is not a holding pen and there is no terminal state in which it is empty; the
roadmaps and mechanical ports are generated **from** it. See
`ForTauCeti/README.md`.

### `DavisKahan`

Canonical spectral-subspace perturbation theory. The project target is the full Hilbert-space
scope of Davis--Kahan (1970), including the bounded main body, arbitrary
unitary-invariant norm scope, and unbounded self-adjoint passages. `import
DavisKahan` exposes the supported bounded-operator and finite-dimensional
theory together with the production source aggregate in `DavisKahan.Sources.All`.
That stable import is broader than the old finite Part III facade, but it must
still not be interpreted as a blanket full-paper completion claim. Specialized
endpoints, alternative proofs, and experiments require explicit imports;
`DavisKahan.All` collects all proof-finished branches.
General-purpose linear-algebra infrastructure lives in `ForTauCeti`. See
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
