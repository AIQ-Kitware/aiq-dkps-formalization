# DKPS source-paper index

Generated from `source_manifest.json`. This is the canonical inventory of works whose definitions, theorem families, or proof architecture are directly formalized, actively scaffolded, or inherited by the DKPS and raw-response Quench development.

The index deliberately separates a paper's **formalization role** from the state of its local literature asset. A transcription is normally not a proof-level reconstruction; an exact short-paper transcription may be marked sufficient only when a maintained discrepancy ledger performs the modernization and theorem mapping. A modern textbook never silently replaces a primary source.

## Inventory summary

- **55 works**: 46 papers, 8 books, and 1 monograph.
- **4** source-order distilled reconstructions are complete.
- **3** broad core notes remain to be upgraded.
- **1** exact transcriptions are intentionally sufficient because a maintained discrepancy ledger supplies the theorem-level reconstruction.
- **3** works have transcription or source text but no source-order proof reconstruction.
- **44** works have no local distilled note at all.
- **17** entries remain in the bibliographic verification queue.
- Priority split: P0=12, P1=21, P2=16, P3=6.

## Interpretation

- **P0**: direct DKPS/Quench theorem papers, inherited DKPS foundations, or the central Davis--Kahan sources.
- **P1**: exact theorem sources needed to audit mathematical infrastructure already formalized or on the active proof path.
- **P2**: supporting, newly discovered primary, or lineage sources that clarify provenance and constants.
- **P3**: reference works and retained future arbitrary-dimensional extensions.

## DKPS lineage and target papers

| Key | Year | Work | Role | Formalization status | Literature asset | Priority |
|---|---:|---|---|---|---|---|
| `HelmMehtaDuderstadtYangWhiteGeisaVogelsteinPriebe2020` | 2020 | A Partition-Based Similarity for Classification Distributions | lineage background | background lineage for distribution and task similarity | `missing` | P2 |
| `DuderstadtHelmPriebe2023` | 2023 | Comparing Foundation Models Using Data Kernels | inherited foundation | foundational definitions reused downstream | `missing` | P0 |
| `HelmPriebeYang2023` | 2023 | A Statistical Turing Test for Generative Models | lineage background | background lineage for response-conditioned generative-model comparison | `missing` | P2 |
| `AcharyyaTrossetPriebeHelm2024` | 2024 | Consistent Estimation of Generative Model Representations in the Data Kernel Perspective Space | direct target | substantially formalized | `transcription_only` | P0 |
| `HelmDuderstadtParkPriebe2024` | 2024 | Tracking the Perspectives of Interacting Language Models | inherited foundation | foundational perspective-space definitions reused downstream | `missing` | P0 |
| `TrossetPriebe2024` | 2024 | Continuous Multidimensional Scaling | primary method source | methods imported by Acharyya 2024 formalization | `missing` | P0 |
| `AcharyyaAgterbergParkPriebe2025` | 2025 | Concentration Bounds on Response-Based Vector Embeddings of Black-Box Generative Models | direct target | substantially formalized | `transcription_only` | P0 |
| `HelmAcharyyaDuderstadtParkPriebe2025` | 2025 | Statistical Inference on Black-Box Generative Models in the Data Kernel Perspective Space | direct target | substantially formalized | `source_text_only` | P0 |
| `HelmJohnsonPriebe2026` | 2026 | Query-Efficient Model Evaluation Using Cached Responses | direct target | formal theorem family complete, including finite, compact-infinite, and all-query raw-response Quench capstones | `transcription_sufficient` | P0 |

## MDS, Euclidean distance geometry, Gram rigidity, and alignment

| Key | Year | Work | Role | Formalization status | Literature asset | Priority |
|---|---:|---|---|---|---|---|
| `Schoenberg1935` | 1935 | Remarks to Maurice Frechet's Article: Sur la Definition Axiomatique d'une Classe d'Espace Distancies Vectoriellement Applicable sur l'Espace de Hilbert | primary theorem source | classical source for Euclidean distance matrices | `missing` | P2 |
| `YoungHouseholder1938` | 1938 | Discussion of a Set of Points in Terms of Their Mutual Distances | primary theorem source | historical source for distance-to-coordinate realization | `missing` | P2 |
| `Torgerson1952` | 1952 | Multidimensional Scaling: I. Theory and Method | primary theorem source | classical scaling algorithm formalized | `missing` | P1 |
| `Kruskal1964` | 1964 | Multidimensional Scaling by Optimizing Goodness of Fit to a Nonmetric Hypothesis | primary theorem source | raw-stress objective and minimizer theory formalized | `missing` | P1 |
| `Gower1966` | 1966 | Some Distance Properties of Latent Root and Vector Methods Used in Multivariate Analysis | primary theorem source | classical scaling identities formalized | `missing` | P1 |
| `Schoenemann1966` | 1966 | A Generalized Solution of the Orthogonal Procrustes Problem | primary theorem source | exact classical source for the polar/SVD alignment step | `missing` | P1 |
| `Sibson1979` | 1979 | Studies in the Robustness of Multidimensional Scaling: Perturbational Analysis of Classical Scaling | primary theorem source | direct precedent for CMDS perturbation/alignment | `missing` | P1 |
| `Goodall1991` | 1991 | Procrustes Methods in the Statistical Analysis of Shape | modern comparison | alignment vocabulary and statistical context | `missing` | P2 |
| `ChienWaldron2016` | 2016 | A Characterization of Projective Unitary Equivalence of Finite Frames and Applications | modern comparison | frame-theoretic Gram rigidity source | `missing` | P2 |
| `LittleXieSun2023` | 2023 | An Analysis of Classical Multidimensional Scaling with Applications to Clustering | modern comparison | modern CMDS perturbation comparison source | `missing` | P2 |

## Spectral perturbation, principal angles, and matrix inequalities

| Key | Year | Work | Role | Formalization status | Literature asset | Priority |
|---|---:|---|---|---|---|---|
| `Weyl1912` | 1912 | Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller Differentialgleichungen (mit einer Anwendung auf die Theorie der Hohlraumstrahlung) | primary theorem source | historical primary source for Weyl eigenvalue inequalities | `missing` | P1 |
| `Schur1923` | 1923 | Ueber eine Klasse von Mittelbildungen mit Anwendungen auf die Determinantentheorie | primary theorem source | forward Schur--Horn/Karamata direction formalized | `missing` | P1 |
| `EckartYoung1936` | 1936 | The Approximation of One Matrix by Another of Lower Rank | related upstream | related to newly scaffolded singular-system/Eckart--Young infrastructure | `missing` | P2 |
| `vonNeumann1937` | 1937 | Some Matrix-Inequalities and Metrization of Matrix-Space | primary theorem source | primary source for trace and symmetric-norm inequalities used in the local spectral infrastructure | `missing` | P1 |
| `Fan1949` | 1949 | On a Theorem of Weyl Concerning Eigenvalues of Linear Transformations I | primary theorem source | Ky Fan variational and dominance infrastructure formalized | `missing` | P1 |
| `HoffmanWielandt1953` | 1953 | The Variation of the Spectrum of a Normal Matrix | primary theorem source | formalized | `missing` | P1 |
| `FanHoffman1955` | 1955 | Some Metric Inequalities in the Space of Matrices | primary theorem source | classical nearest-unitary/polar-factor source | `missing` | P2 |
| `Rosenblum1956` | 1956 | On the Operator Equation BX - XA = Q | supporting source | background for the Sylvester--Rosenblum equation | `missing` | P2 |
| `Mirsky1960` | 1960 | Symmetric Gauge Functions and Unitarily Invariant Norms | primary theorem source | unitarily invariant norm framework formalized | `missing` | P1 |
| `Davis1963` | 1963 | The Rotation of Eigenvectors by a Perturbation | primary theorem source | Sections I--V reconstructed in source order; core endpoints formalized, canonical direct rotation remains unfinished | `complete` | P0 |
| `Halmos1969` | 1969 | Two Subspaces | primary theorem source | canonical two-subspace/direct-rotation background | `missing` | P2 |
| `DavisKahan1970` | 1970 | The Rotation of Eigenvectors by a Perturbation. III | primary theorem source | source-facing coverage is extensive and the tracked census is near-terminal, with Proposition 4.4 formally refuted as transcribed; an independent statement audit has identified a remaining unrestricted Section 2 tan(2 Theta) exact-wrapper gap, so the repository does not currently certify 100% source fidelity | `core_note` | P0 |
| `Wedin1972` | 1972 | Perturbation Bounds in Connection with Singular Value Decomposition | primary theorem source | singular-subspace/Wedin-style corollaries scaffolded | `missing` | P1 |
| `BhatiaDavisMcIntosh1983` | 1983 | Perturbation of Spectral Subspaces and Solution of Linear Operator Equations | primary theorem source | hard arbitrary-spectrum Sylvester estimate scaffolded | `missing` | P1 |
| `Higham1986` | 1986 | Computing the Polar Decomposition--with Applications | modern comparison | quantitative polar-factor comparison source | `missing` | P2 |
| `BhatiaRosenthal1997` | 1997 | How and Why to Solve the Operator Equation AX - XB = Y | supporting source | modern reference for Sylvester equations | `missing` | P2 |
| `AlbeverioMakarovMotovilov2001` | 2001 | Graph Subspaces and the Spectral Shift Function | supporting source | source-order sharp Sylvester/Fourier bridge reconstructed; scalar pi/2 interpolation and real descent remain active | `complete` | P1 |
| `KostrykinMakarovMotovilov2005` | 2005 | On the Existence of Solutions to the Operator Riccati Equation and the Tan Theta Theorem | primary theorem source | tan Theta and Riccati scaffold sources | `missing` | P1 |
| `KnyazevArgentati2006` | 2006 | Majorization for Changes in Angles Between Subspaces, Ritz Values, and Graph Laplacian Spectra | modern comparison | principal-angle and majorization comparison source | `missing` | P2 |
| `KnyazevJujunashviliArgentati2010` | 2010 | Angles Between Infinite Dimensional Subspaces with Applications to the Rayleigh--Ritz and Alternating Projectors Methods | future extension | future arbitrary-dimensional principal-angle reference | `missing` | P3 |
| `Motovilov2012` | 2012 | Comment on 'The Tan Theta Theorem with Relaxed Conditions' | primary theorem source | used to audit the relaxed tan Theta statement | `missing` | P1 |
| `Nakatsukasa2012` | 2012 | The Tan Theta Theorem with Relaxed Conditions | primary theorem source | tan Theta statement source | `missing` | P1 |
| `GrubisicKostrykinMakarovVeselic2013` | 2013 | The Tan 2 Theta Theorem for Indefinite Quadratic Forms | primary theorem source | tan 2 Theta source | `missing` | P1 |
| `Seelmann2014` | 2014 | Notes on the Sin 2 Theta Theorem | primary theorem source | operator-angle sin 2 Theta source | `missing` | P1 |
| `YuWangSamworth2015` | 2015 | A Useful Variant of the Davis--Kahan Theorem for Statisticians | primary theorem source | source-order reconstruction complete; symmetric, aligned-basis, and singular-subspace theorem families formalized | `complete` | P0 |
| `Deepesh2024` | 2024 | Approximation results on s-numbers of operators | primary method source | analytic cutoff-convergence target identified | `core_note` | P0 |
| `Ullrich2024` | 2024 | Inequalities between s-numbers | primary method source | definition and elementary s-number laws actively formalized | `core_note` | P0 |

## Reference works and modern syntheses

| Key | Year | Work | Role | Formalization status | Literature asset | Priority |
|---|---:|---|---|---|---|---|
| `Kato1966` | 1966 | Perturbation Theory for Linear Operators | reference work | reference horizon for the retained unbounded and spectral-projection scaffolds | `missing` | P3 |
| `StewartSun1990` | 1990 | Matrix Perturbation Theory | reference work | cross-check source for matrix/subspace perturbation statements | `missing` | P2 |
| `Bhatia1997` | 1997 | Matrix Analysis | reference work | modern reference for UI norms, Sylvester bounds, and Davis--Kahan | `missing` | P1 |
| `CoxCox2001` | 2001 | Multidimensional Scaling, Second Edition | reference work | modern classical-MDS reference | `missing` | P2 |
| `BorgGroenen2005` | 2005 | Modern Multidimensional Scaling: Theory and Applications, Second Edition | reference work | modern Procrustes/MDS reference | `missing` | P3 |
| `Higham2008` | 2008 | Functions of Matrices: Theory and Computation | reference work | modern polar decomposition and matrix-function reference | `missing` | P3 |
| `MarshallOlkinArnold2011` | 2011 | Inequalities: Theory of Majorization and Its Applications, Second Edition | reference work | modern majorization reference | `missing` | P3 |
| `HornJohnson2013` | 2013 | Matrix Analysis, Second Edition | reference work | strengthened source-order Courant--Fischer chain with explicit Lean index dictionary, literal min--max implementation obligations, declaration-level coverage, full Weyl/interlacing/majorization roadmap, and expanded singular-value deletion, min--max, additive/product, and norm-dominance descendants; core theorem families remain only partially formalized | `complete` | P1 |
| `ChenChiFanMa2021` | 2021 | Spectral Methods for Data Science: A Statistical Perspective | reference work | statistical spectral-methods context | `missing` | P3 |

## Highest-value missing reconstructions

- **`DuderstadtHelmPriebe2023` — Comparing Foundation Models Using Data Kernels**: Acquire source; reconstruct the data-kernel and population-geometry definitions that later papers treat as inherited.
- **`AcharyyaTrossetPriebeHelm2024` — Consistent Estimation of Generative Model Representations in the Data Kernel Perspective Space**: Turn the transcription and crosswalk into a source-order proof reconstruction with equation/theorem anchors and discrepancy notes.
- **`HelmDuderstadtParkPriebe2024` — Tracking the Perspectives of Interacting Language Models**: Acquire source and reconstruct the exact DKPS definitions inherited by the theorem papers.
- **`TrossetPriebe2024` — Continuous Multidimensional Scaling**: Acquire source and identify exactly which compactness/argmin-continuity results are reused or replaced in Lean.
- **`AcharyyaAgterbergParkPriebe2025` — Concentration Bounds on Response-Based Vector Embeddings of Black-Box Generative Models**: Create a source-order reconstruction that distinguishes the paper proof from the stronger/generalized Lean lemmas.
- **`HelmAcharyyaDuderstadtParkPriebe2025` — Statistical Inference on Black-Box Generative Models in the Data Kernel Perspective Space**: Create a source-order theorem reconstruction and clearly isolate the inference-preservation assumptions not stated in the paper.
- **`Torgerson1952` — Multidimensional Scaling: I. Theory and Method**: Acquire source and reconstruct the exact classical-scaling theorem chain used in DKPS.
- **`Kruskal1964` — Multidimensional Scaling by Optimizing Goodness of Fit to a Nonmetric Hypothesis**: Separate the raw-stress criterion actually used by DKPS from the nonmetric optimization material not formalized.
- **`Gower1966` — Some Distance Properties of Latent Root and Vector Methods Used in Multivariate Analysis**: Reconstruct the source formulas and map them to exact double-centering and Gram-realization declarations.
- **`Schoenemann1966` — A Generalized Solution of the Orthogonal Procrustes Problem**: Add as an explicit source: the repo currently cites later Procrustes surveys but formalizes the classical polar-factor solution itself.
- **`Sibson1979` — Studies in the Robustness of Multidimensional Scaling: Perturbational Analysis of Classical Scaling**: Acquire source; compare constants and hypotheses against the Acharyya 2025 deterministic perturbation chain.
- **`Weyl1912` — Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller Differentialgleichungen (mit einer Anwendung auf die Theorie der Hohlraumstrahlung)**: Verify the exact location and historical formulation of the finite-dimensional sum inequalities; compare the local perturbation corollary with the original statement.
- **`Schur1923` — Ueber eine Klasse von Mittelbildungen mit Anwendungen auf die Determinantentheorie**: Acquire/translate source and separate Schur majorization from later Horn converse results.
- **`vonNeumann1937` — Some Matrix-Inequalities and Metrization of Matrix-Space**: Acquire a reliable scan/edition and separate the exact original results from later Mirsky/Fan dominance formulations.
- **`Fan1949` — On a Theorem of Weyl Concerning Eigenvalues of Linear Transformations I**: Identify which 1949 statements correspond exactly to the current finite-dimensional API.
- **`HoffmanWielandt1953` — The Variation of the Spectrum of a Normal Matrix**: Reconstruct the original doubly-stochastic/rearrangement proof and compare it with the Lean route.
- **`Mirsky1960` — Symmetric Gauge Functions and Unitarily Invariant Norms**: Reconstruct the exact representation theorem and note where the Lean interface is finite-dimensional or norm-seminorm generalized.
- **`DavisKahan1970` — The Rotation of Eigenvectors by a Perturbation. III**: Close and compile the unrestricted Section 2 tan(2 Theta) source wrapper from only the printed hypotheses, then run the clean compiler certificate and an independent row-by-row semantic audit. Keep the readable mathematical distillation current, and keep exact source excerpts and source-to-Lean registration in the separate audit register/map so exposition and certification cannot drift together.
- **`Wedin1972` — Perturbation Bounds in Connection with Singular Value Decomposition**: Acquire source and determine which theorem should be the canonical named Wedin wrapper over the Hermitian-dilation results.
- **`BhatiaDavisMcIntosh1983` — Perturbation of Spectral Subspaces and Solution of Linear Operator Equations**: Acquire and reconstruct the original 1983 paper in source order. The Albeverio--Makarov--Motovilov note documents the later sharp pi/2 synthesis and attribution chain but is not a substitute for the original proof.
- **`KostrykinMakarovMotovilov2005` — On the Existence of Solutions to the Operator Riccati Equation and the Tan Theta Theorem**: Reconstruct the exact hypotheses and distinguish the bounded finite-dimensional specialization from the full operator theorem.
- **`Motovilov2012` — Comment on 'The Tan Theta Theorem with Relaxed Conditions'**: Distill together with Nakatsukasa 2012 while preserving the disagreement and corrected statement.
- **`Nakatsukasa2012` — The Tan Theta Theorem with Relaxed Conditions**: Record the exact pole/separation condition and the issue corrected by Motovilov.
- **`GrubisicKostrykinMakarovVeselic2013` — The Tan 2 Theta Theorem for Indefinite Quadratic Forms**: Reconstruct the form-domain theorem and clearly state the finite-dimensional bounded specialization formalized here.
- **`Seelmann2014` — Notes on the Sin 2 Theta Theorem**: Reconstruct the exact separation hypotheses and compare its angle conventions with the Lean API.
- **`Bhatia1997` — Matrix Analysis**: Create a theorem-indexed bridge note, not a chapter summary.
- **`Ullrich2024` — Inequalities between s-numbers**: Complete the Hilbert-space adjoint, Ky Fan addition, and strong-cutoff convergence proofs and cross-check index conventions against the paper.
- **`Deepesh2024` — Approximation results on s-numbers of operators**: Formalize the Hilbert-space finite-dimensional compactness or min-max argument without adding separability assumptions.

## Sources missing from the repository's prior explicit source map

These works were added by the audit rather than copied from an existing canonical DKPS source inventory:

- **`HelmMehtaDuderstadtYangWhiteGeisaVogelsteinPriebe2020` — A Partition-Based Similarity for Classification Distributions** (2020): The partition/task-similarity framework that precedes the data-kernel model-comparison program.
- **`HelmPriebeYang2023` — A Statistical Turing Test for Generative Models** (2023): The statistical pattern-recognition framing for context-conditioned human/model distribution comparison that precedes response-based DKPS evaluation.
- **`Schoenberg1935` — Remarks to Maurice Frechet's Article: Sur la Definition Axiomatique d'une Classe d'Espace Distancies Vectoriellement Applicable sur l'Espace de Hilbert** (1935): Conditional negative type and Hilbert-space realization underlying Euclidean distance matrices and double centering.
- **`YoungHouseholder1938` — Discussion of a Set of Points in Terms of Their Mutual Distances** (1938): Early Euclidean distance realization and coordinate recovery from mutual distances.
- **`Schoenemann1966` — A Generalized Solution of the Orthogonal Procrustes Problem** (1966): The orthogonal Procrustes minimizer and its SVD/polar-factor representation.
- **`Weyl1912` — Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller Differentialgleichungen (mit einer Anwendung auf die Theorie der Hohlraumstrahlung)** (1912): The eigenvalue inequalities whose operator-norm perturbation corollary is proved locally and repeatedly used in the DKPS spectral chain.
- **`vonNeumann1937` — Some Matrix-Inequalities and Metrization of Matrix-Space** (1937): The singular-value trace inequality and symmetric-norm viewpoint behind the local von-Neumann-type trace bound and unitarily invariant norm layer.
- **`FanHoffman1955` — Some Metric Inequalities in the Space of Matrices** (1955): Metric optimality of the unitary polar factor and related unitarily invariant norm inequalities.
- **`Halmos1969` — Two Subspaces** (1969): Canonical decomposition of a pair of subspaces/projections and the generic two-subspace model.

## Bibliographic verification queue

No distilled note should be presented as source-faithful until the exact edition or article record is confirmed.

- `Schoenberg1935` — Remarks to Maurice Frechet's Article: Sur la Definition Axiomatique d'une Classe d'Espace Distancies Vectoriellement Applicable sur l'Espace de Hilbert
- `YoungHouseholder1938` — Discussion of a Set of Points in Terms of Their Mutual Distances
- `vonNeumann1937` — Some Matrix-Inequalities and Metrization of Matrix-Space
- `FanHoffman1955` — Some Metric Inequalities in the Space of Matrices
- `Rosenblum1956` — On the Operator Equation BX - XA = Q
- `BhatiaDavisMcIntosh1983` — Perturbation of Spectral Subspaces and Solution of Linear Operator Equations
- `BhatiaRosenthal1997` — How and Why to Solve the Operator Equation AX - XB = Y
- `KostrykinMakarovMotovilov2005` — On the Existence of Solutions to the Operator Riccati Equation and the Tan Theta Theorem
- `KnyazevJujunashviliArgentati2010` — Angles Between Infinite Dimensional Subspaces with Applications to the Rayleigh--Ritz and Alternating Projectors Methods
- `Nakatsukasa2012` — The Tan Theta Theorem with Relaxed Conditions
- `StewartSun1990` — Matrix Perturbation Theory
- `Bhatia1997` — Matrix Analysis
- `CoxCox2001` — Multidimensional Scaling, Second Edition
- `BorgGroenen2005` — Modern Multidimensional Scaling: Theory and Applications, Second Edition
- `Higham2008` — Functions of Matrices: Theory and Computation
- `MarshallOlkinArnold2011` — Inequalities: Theory of Majorization and Its Applications, Second Edition
- `ChenChiFanMa2021` — Spectral Methods for Data Science: A Statistical Perspective

## Maintenance

```bash
python scripts/check_distilled_literature_index.py
python scripts/render_distilled_literature_index.py
```

The checker validates schema, enums, repository evidence paths, local asset paths, unique target-note names, and exact agreement between the manifest and both generated indexes.
